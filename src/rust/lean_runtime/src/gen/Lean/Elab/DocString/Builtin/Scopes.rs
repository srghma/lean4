// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Scopes
// Imports: Lean.Elab.DocString Lean.Elab.DocString.Builtin.Parsing
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_TSyntax_getId, l_Lean_TSyntax_getId___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadLift___lam__0___boxed,
    lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadLogCoreM, l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed,
    l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Elab::DocString::Builtin::Parsing::{
    initialize_Lean_Elab_DocString_Builtin_Parsing, l_Lean_Doc_parseQuotedStrLit___redArg,
    runtime_initialize_Lean_Elab_DocString_Builtin_Parsing,
};
use crate::r#gen::Lean::Elab::DocString::{
    initialize_Lean_Elab_DocString, runtime_initialize_Lean_Elab_DocString,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_instAddErrorMessageContextTermElabM,
    l_Lean_Elab_Term_instMonadMacroAdapterTermElabM,
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
};
use crate::r#gen::Lean::Environment::l_Lean_instMonadEnvOfMonadLift___redArg___lam__0;
use crate::r#gen::Lean::Exception::l_Lean_throwErrorAt___redArg;
use crate::r#gen::Lean::Log::l_Lean_instMonadLogOfMonadLift___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadEnvMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthenFn, l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot,
    l_Lean_Parser_sepBy1, l_Lean_Parser_symbol, l_Lean_Parser_whitespace,
    l_Lean_Parser_withAntiquot,
};
use crate::r#gen::Lean::Parser::Extra::l_Lean_Parser_ident;
use crate::r#gen::Lean::Parser::Types::l_Lean_Parser_withCache;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Prelude::lean_name_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__0_value
        ) as *mut LeanObject,
        11079354408986465895 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value
        ) as *mut LeanObject,
        10352885018404983386 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__4_value
        ) as *mut LeanObject,
        5444244426488757208 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [68, 111, 99, 83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__6_value
        ) as *mut LeanObject,
        2486765539904776311 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [66, 117, 105, 108, 116, 105, 110, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__8_value
        ) as *mut LeanObject,
        700876400105220763 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 99, 111, 112, 101, 115, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__10_value
        ) as *mut LeanObject,
        4570434455475722275 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__11_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        3885593668613330158 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__12_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__2_value
        ) as *mut LeanObject,
        7231748941142714647 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 111, 99, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__14_value
        ) as *mut LeanObject,
        14004310548618627539 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 109, 112, 111, 114, 116, 115, 0],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__15_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16_value
        ) as *mut LeanObject,
        9460312923576688979 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value: LeanStringObject<6> =
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
        m_data: [108, 111, 99, 97, 108, 0],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__26_value)
                as *mut LeanObject,
            5128563302434957432 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_value: LeanStringObject<63> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 63,
        m_capacity: 63,
        m_length: 62,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102,
            105, 101, 114, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 108, 111, 99, 97,
            108, 96, 32, 111, 114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 111, 102, 32, 105,
            109, 112, 111, 114, 116, 115, 0,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28_value)
        as *mut LeanObject;
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32,
            96, 0,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30_value)
        as *mut LeanObject;
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value: LeanStringObject<2> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32_value)
        as *mut LeanObject;
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value: LeanClosureObject<5> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__35_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value: LeanClosureObject<2> =
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
        m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__36_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value: LeanClosureObject<5> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__37_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value: LeanClosureObject<2> =
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
        m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__38_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_whitespace as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 109, 109, 97, 45, 115, 101, 112, 97,
            114, 97, 116, 101, 100, 32, 105, 109, 112, 111, 114, 116, 115, 32, 108, 105, 115, 116,
            44, 32, 103, 111, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42_value)
        as *mut LeanObject;
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_TSyntax_getId___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value: LeanClosureObject<0> =
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
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__45_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__46_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__52_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__47_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__48_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__49_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__50_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__53_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__51_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Doc_instFromDocArgDocScope___closed__0_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__34_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_instFromDocArgDocScope___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Doc_instFromDocArgDocScope: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instFromDocArgDocScope___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Doc_DocScope_ctorIdx(mut v_x_617_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_617_) == 0 {
        let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
        v___x_618_ = lean_unsigned_to_nat(0);
        return v___x_618_;
    } else {
        let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
        v___x_619_ = lean_unsigned_to_nat(1);
        return v___x_619_;
    }
}
pub unsafe fn l_Lean_Doc_DocScope_ctorIdx___boxed(
    mut v_x_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_Doc_DocScope_ctorIdx(v_x_620_);
    lean_dec(v_x_620_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Doc_DocScope_ctorElim___redArg(
    mut v_t_622_: *mut LeanObject,
    mut v_k_623_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_622_) == 0 {
        return v_k_623_;
    } else {
        let mut v_mods_624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
        v_mods_624_ = lean_ctor_get(v_t_622_, 0);
        lean_inc_ref(v_mods_624_);
        lean_dec_ref_known(v_t_622_, 1);
        v___x_625_ = lean_apply_1(v_k_623_, v_mods_624_);
        return v___x_625_;
    }
}
pub unsafe fn l_Lean_Doc_DocScope_ctorElim(
    mut v_motive_626_: *mut LeanObject,
    mut v_ctorIdx_627_: *mut LeanObject,
    mut v_t_628_: *mut LeanObject,
    mut v_h_629_: *mut LeanObject,
    mut v_k_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_628_, v_k_630_);
    return v___x_631_;
}
pub unsafe fn l_Lean_Doc_DocScope_ctorElim___boxed(
    mut v_motive_632_: *mut LeanObject,
    mut v_ctorIdx_633_: *mut LeanObject,
    mut v_t_634_: *mut LeanObject,
    mut v_h_635_: *mut LeanObject,
    mut v_k_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_637_: *mut LeanObject = core::ptr::null_mut();
    v_res_637_ =
        l_Lean_Doc_DocScope_ctorElim(v_motive_632_, v_ctorIdx_633_, v_t_634_, v_h_635_, v_k_636_);
    lean_dec(v_ctorIdx_633_);
    return v_res_637_;
}
pub unsafe fn l_Lean_Doc_DocScope_local_elim___redArg(
    mut v_t_638_: *mut LeanObject,
    mut v_local_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_638_, v_local_639_);
    return v___x_640_;
}
pub unsafe fn l_Lean_Doc_DocScope_local_elim(
    mut v_motive_641_: *mut LeanObject,
    mut v_t_642_: *mut LeanObject,
    mut v_h_643_: *mut LeanObject,
    mut v_local_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_642_, v_local_644_);
    return v___x_645_;
}
pub unsafe fn l_Lean_Doc_DocScope_import_elim___redArg(
    mut v_t_646_: *mut LeanObject,
    mut v_import_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    v___x_648_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_646_, v_import_647_);
    return v___x_648_;
}
pub unsafe fn l_Lean_Doc_DocScope_import_elim(
    mut v_motive_649_: *mut LeanObject,
    mut v_t_650_: *mut LeanObject,
    mut v_h_651_: *mut LeanObject,
    mut v_import_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_653_ = l_Lean_Doc_DocScope_ctorElim___redArg(v_t_650_, v_import_652_);
    return v___x_653_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18()
-> *mut LeanObject {
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = 0;
    v___x_693_ = 1;
    v___x_694_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17;
    v___x_695_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__16;
    v___x_696_ = l_Lean_Parser_mkAntiquot(v___x_695_, v___x_694_, v___x_693_, v___x_692_);
    return v___x_696_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20()
-> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19;
    v___x_699_ = l_Lean_Parser_symbol(v___x_698_);
    return v___x_699_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21()
-> *mut LeanObject {
    let mut v___x_700_: u8 = 0;
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v___x_700_ = 0;
    v___x_701_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__20,
    );
    v___x_702_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__19;
    v___x_703_ = l_Lean_Parser_ident;
    v___x_704_ = l_Lean_Parser_sepBy1(v___x_703_, v___x_702_, v___x_701_, v___x_700_);
    return v___x_704_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22()
-> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__21,
    );
    v___x_706_ = lean_unsigned_to_nat(1024);
    v___x_707_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17;
    v___x_708_ = l_Lean_Parser_leadingNode(v___x_707_, v___x_706_, v___x_705_);
    return v___x_708_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23()
-> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__22,
    );
    v___x_710_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__18,
    );
    v___x_711_ = l_Lean_Parser_withAntiquot(v___x_710_, v___x_709_);
    return v___x_711_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24()
-> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__23,
    );
    v___x_713_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17;
    v___x_714_ = l_Lean_Parser_withCache(v___x_713_, v___x_712_);
    return v___x_714_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports()
-> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24_once
        ),
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__24,
    );
    return v___x_715_;
}
pub unsafe fn _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM()
-> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
    return v___x_716_;
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___private__1___lam__0(
    mut v___y_717_: *mut LeanObject,
    mut v___y_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports;
    v_fn_720_ = lean_ctor_get(v___x_719_, 1);
    lean_inc_ref(v_fn_720_);
    v___x_721_ = lean_apply_2(v_fn_720_, v___y_717_, v___y_718_);
    return v___x_721_;
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1(
    mut v___x_722_: *mut LeanObject,
    mut v___f_723_: *mut LeanObject,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lean_Parser_andthenFn(v___x_722_, v___f_723_, v___y_724_, v___y_725_);
    return v___x_726_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0() -> *mut LeanObject
{
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = l_instMonadEIO(lean_box(0));
    return v___x_727_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1() -> *mut LeanObject
{
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__0,
    );
    v___x_729_ = l_StateRefT_x27_instMonad___redArg(v___x_728_);
    return v___x_729_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10() -> *mut LeanObject
{
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_Core_instMonadLogCoreM;
    v___x_739_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9;
    v___x_740_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_739_, v___x_738_);
    return v___x_740_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11() -> *mut LeanObject
{
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_741_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__10,
    );
    v___f_742_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8;
    v___x_743_ = l_Lean_instMonadLogOfMonadLift___redArg(v___f_742_, v___x_741_);
    return v___x_743_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12() -> *mut LeanObject
{
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__11,
    );
    v___x_745_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9;
    v___x_746_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_745_, v___x_744_);
    return v___x_746_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13() -> *mut LeanObject
{
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__12,
    );
    v___f_748_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8;
    v___x_749_ = l_Lean_instMonadLogOfMonadLift___redArg(v___f_748_, v___x_747_);
    return v___x_749_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14() -> *mut LeanObject
{
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_751_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_751_, 0, v___x_750_);
    return v___f_751_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15() -> *mut LeanObject
{
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_753_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_753_, 0, v___x_752_);
    return v___f_753_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16() -> *mut LeanObject
{
    let mut v___f_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___f_754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__15,
    );
    v___f_755_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__14,
    );
    v___x_756_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_756_, 0, v___f_755_);
    lean_ctor_set(v___x_756_, 1, v___f_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17() -> *mut LeanObject
{
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16,
    );
    v___f_758_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_758_, 0, v___x_757_);
    return v___f_758_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18() -> *mut LeanObject
{
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_759_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__16,
    );
    v___f_760_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_760_, 0, v___x_759_);
    return v___f_760_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19() -> *mut LeanObject
{
    let mut v___f_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___f_761_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__18,
    );
    v___f_762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__17,
    );
    v___x_763_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_763_, 0, v___f_762_);
    lean_ctor_set(v___x_763_, 1, v___f_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20() -> *mut LeanObject
{
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_765_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19,
    );
    v___f_765_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_765_, 0, v___x_764_);
    return v___f_765_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21() -> *mut LeanObject
{
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__19,
    );
    v___f_767_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_767_, 0, v___x_766_);
    return v___f_767_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22() -> *mut LeanObject
{
    let mut v___f_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    v___f_768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__21,
    );
    v___f_769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__20,
    );
    v___x_770_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_770_, 0, v___f_769_);
    lean_ctor_set(v___x_770_, 1, v___f_768_);
    return v___x_770_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23() -> *mut LeanObject
{
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22,
    );
    v___f_772_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_772_, 0, v___x_771_);
    return v___f_772_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24() -> *mut LeanObject
{
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_774_: *mut LeanObject = core::ptr::null_mut();
    v___x_773_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__22,
    );
    v___f_774_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_774_, 0, v___x_773_);
    return v___f_774_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25() -> *mut LeanObject
{
    let mut v___f_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___f_775_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__24,
    );
    v___f_776_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23_once),
        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__23,
    );
    v___x_777_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_777_, 0, v___f_776_);
    lean_ctor_set(v___x_777_, 1, v___f_775_);
    return v___x_777_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29() -> *mut LeanObject
{
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    v___x_782_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__28;
    v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
    return v___x_783_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31() -> *mut LeanObject
{
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__30;
    v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
    return v___x_786_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33() -> *mut LeanObject
{
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__32;
    v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
    return v___x_789_;
}
pub unsafe fn _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43() -> *mut LeanObject
{
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_805_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__42;
    v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___private__1(
    mut v_v_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_855_: u8 = 0;
    let mut v_toFunctor_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___f_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v_toFunctor_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_886_: u8 = 0;
    let mut v___f_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160__overap_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut v_val_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822__overap_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v_fileName_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_957_: u8 = 0;
    let mut v_cancelTk_x3f_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_959_: u8 = 0;
    let mut v_inheritedTraceOptions_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093__overap_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_970_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: u8 = 0;
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204__overap_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_986_: usize = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut v_a_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v_isSharedCheck_1004_: u8 = 0;
    let mut v_reuseFailAlloc_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_unused_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v_unused_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v_unused_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_unused_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_835_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1,
                );
                v_toApplicative_836_ = lean_ctor_get(v___x_835_, 0);
                v_toFunctor_837_ = lean_ctor_get(v_toApplicative_836_, 0);
                v_toSeq_838_ = lean_ctor_get(v_toApplicative_836_, 2);
                v_toSeqLeft_839_ = lean_ctor_get(v_toApplicative_836_, 3);
                v_toSeqRight_840_ = lean_ctor_get(v_toApplicative_836_, 4);
                v___f_841_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2;
                v___f_842_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3;
                lean_inc_ref_n(v_toFunctor_837_, 2);
                v___f_843_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_843_, 0, v_toFunctor_837_);
                v___f_844_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_844_, 0, v_toFunctor_837_);
                v___x_845_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_845_, 0, v___f_843_);
                lean_ctor_set(v___x_845_, 1, v___f_844_);
                lean_inc(v_toSeqRight_840_);
                v___f_846_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_846_, 0, v_toSeqRight_840_);
                lean_inc(v_toSeqLeft_839_);
                v___f_847_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_847_, 0, v_toSeqLeft_839_);
                lean_inc(v_toSeq_838_);
                v___f_848_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_848_, 0, v_toSeq_838_);
                v___x_849_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_849_, 0, v___x_845_);
                lean_ctor_set(v___x_849_, 1, v___f_841_);
                lean_ctor_set(v___x_849_, 2, v___f_848_);
                lean_ctor_set(v___x_849_, 3, v___f_847_);
                lean_ctor_set(v___x_849_, 4, v___f_846_);
                v___x_850_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_850_, 0, v___x_849_);
                lean_ctor_set(v___x_850_, 1, v___f_842_);
                v___x_851_ = l_StateRefT_x27_instMonad___redArg(v___x_850_);
                v_toApplicative_852_ = lean_ctor_get(v___x_851_, 0);
                v_isSharedCheck_1015_ = (!lean_is_exclusive(v___x_851_)) as u8;
                if v_isSharedCheck_1015_ == 0 {
                    v_unused_1016_ = lean_ctor_get(v___x_851_, 1);
                    lean_dec(v_unused_1016_);
                    v___x_854_ = v___x_851_;
                    v_isShared_855_ = v_isSharedCheck_1015_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_852_);
                    lean_dec(v___x_851_);
                    v___x_854_ = lean_box(0);
                    v_isShared_855_ = v_isSharedCheck_1015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_856_ = lean_ctor_get(v_toApplicative_852_, 0);
                v_toSeq_857_ = lean_ctor_get(v_toApplicative_852_, 2);
                v_toSeqLeft_858_ = lean_ctor_get(v_toApplicative_852_, 3);
                v_toSeqRight_859_ = lean_ctor_get(v_toApplicative_852_, 4);
                v_isSharedCheck_1013_ = (!lean_is_exclusive(v_toApplicative_852_)) as u8;
                if v_isSharedCheck_1013_ == 0 {
                    v_unused_1014_ = lean_ctor_get(v_toApplicative_852_, 1);
                    lean_dec(v_unused_1014_);
                    v___x_861_ = v_toApplicative_852_;
                    v_isShared_862_ = v_isSharedCheck_1013_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_859_);
                    lean_inc(v_toSeqLeft_858_);
                    lean_inc(v_toSeq_857_);
                    lean_inc(v_toFunctor_856_);
                    lean_dec(v_toApplicative_852_);
                    v___x_861_ = lean_box(0);
                    v_isShared_862_ = v_isSharedCheck_1013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_863_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4;
                v___f_864_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5;
                lean_inc_ref(v_toFunctor_856_);
                v___f_865_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_865_, 0, v_toFunctor_856_);
                v___f_866_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_866_, 0, v_toFunctor_856_);
                v___x_867_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_867_, 0, v___f_865_);
                lean_ctor_set(v___x_867_, 1, v___f_866_);
                v___f_868_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_868_, 0, v_toSeqRight_859_);
                v___f_869_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_869_, 0, v_toSeqLeft_858_);
                v___f_870_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_870_, 0, v_toSeq_857_);
                if v_isShared_862_ == 0 {
                    lean_ctor_set(v___x_861_, 4, v___f_868_);
                    lean_ctor_set(v___x_861_, 3, v___f_869_);
                    lean_ctor_set(v___x_861_, 2, v___f_870_);
                    lean_ctor_set(v___x_861_, 1, v___f_863_);
                    lean_ctor_set(v___x_861_, 0, v___x_867_);
                    v___x_872_ = v___x_861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_867_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___f_863_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 2, v___f_870_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 3, v___f_869_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 4, v___f_868_);
                    v___x_872_ = v_reuseFailAlloc_1012_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_855_ == 0 {
                    lean_ctor_set(v___x_854_, 1, v___f_864_);
                    lean_ctor_set(v___x_854_, 0, v___x_872_);
                    v___x_874_ = v___x_854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_872_);
                    lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___f_864_);
                    v___x_874_ = v_reuseFailAlloc_1011_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_875_ = l_StateRefT_x27_instMonad___redArg(v___x_874_);
                v_toApplicative_876_ = lean_ctor_get(v___x_875_, 0);
                v_isSharedCheck_1009_ = (!lean_is_exclusive(v___x_875_)) as u8;
                if v_isSharedCheck_1009_ == 0 {
                    v_unused_1010_ = lean_ctor_get(v___x_875_, 1);
                    lean_dec(v_unused_1010_);
                    v___x_878_ = v___x_875_;
                    v_isShared_879_ = v_isSharedCheck_1009_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_876_);
                    lean_dec(v___x_875_);
                    v___x_878_ = lean_box(0);
                    v_isShared_879_ = v_isSharedCheck_1009_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_880_ = lean_ctor_get(v_toApplicative_876_, 0);
                v_toSeq_881_ = lean_ctor_get(v_toApplicative_876_, 2);
                v_toSeqLeft_882_ = lean_ctor_get(v_toApplicative_876_, 3);
                v_toSeqRight_883_ = lean_ctor_get(v_toApplicative_876_, 4);
                v_isSharedCheck_1007_ = (!lean_is_exclusive(v_toApplicative_876_)) as u8;
                if v_isSharedCheck_1007_ == 0 {
                    v_unused_1008_ = lean_ctor_get(v_toApplicative_876_, 1);
                    lean_dec(v_unused_1008_);
                    v___x_885_ = v_toApplicative_876_;
                    v_isShared_886_ = v_isSharedCheck_1007_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_883_);
                    lean_inc(v_toSeqLeft_882_);
                    lean_inc(v_toSeq_881_);
                    lean_inc(v_toFunctor_880_);
                    lean_dec(v_toApplicative_876_);
                    v___x_885_ = lean_box(0);
                    v_isShared_886_ = v_isSharedCheck_1007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_887_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6;
                v___f_888_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7;
                lean_inc_ref(v_toFunctor_880_);
                v___f_889_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_889_, 0, v_toFunctor_880_);
                v___f_890_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_890_, 0, v_toFunctor_880_);
                v___x_891_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_891_, 0, v___f_889_);
                lean_ctor_set(v___x_891_, 1, v___f_890_);
                v___f_892_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_892_, 0, v_toSeqRight_883_);
                v___f_893_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_893_, 0, v_toSeqLeft_882_);
                v___f_894_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_894_, 0, v_toSeq_881_);
                if v_isShared_886_ == 0 {
                    lean_ctor_set(v___x_885_, 4, v___f_892_);
                    lean_ctor_set(v___x_885_, 3, v___f_893_);
                    lean_ctor_set(v___x_885_, 2, v___f_894_);
                    lean_ctor_set(v___x_885_, 1, v___f_887_);
                    lean_ctor_set(v___x_885_, 0, v___x_891_);
                    v___x_896_ = v___x_885_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_891_);
                    lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___f_887_);
                    lean_ctor_set(v_reuseFailAlloc_1006_, 2, v___f_894_);
                    lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___f_893_);
                    lean_ctor_set(v_reuseFailAlloc_1006_, 4, v___f_892_);
                    v___x_896_ = v_reuseFailAlloc_1006_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_879_ == 0 {
                    lean_ctor_set(v___x_878_, 1, v___f_888_);
                    lean_ctor_set(v___x_878_, 0, v___x_896_);
                    v___x_898_ = v___x_878_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_896_);
                    lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___f_888_);
                    v___x_898_ = v_reuseFailAlloc_1005_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_899_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
                v_toMonadQuotation_900_ = lean_ctor_get(v___x_899_, 0);
                v_toMonadRef_901_ = lean_ctor_get(v_toMonadQuotation_900_, 0);
                v___f_902_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8;
                v___x_903_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9;
                v___x_904_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13,
                );
                v_toMonadFileMap_905_ = lean_ctor_get(v___x_904_, 0);
                v___x_906_ = l_Lean_Meta_instMonadEnvMetaM;
                v_getEnv_907_ = lean_ctor_get(v___x_906_, 0);
                v_modifyEnv_908_ = lean_ctor_get(v___x_906_, 1);
                lean_inc(v_modifyEnv_908_);
                v___f_909_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_909_, 0, v_modifyEnv_908_);
                lean_closure_set(v___f_909_, 1, v___x_903_);
                lean_inc(v_getEnv_907_);
                v___x_910_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_910_, 0, lean_box(0));
                lean_closure_set(v___x_910_, 1, lean_box(0));
                lean_closure_set(v___x_910_, 2, lean_box(0));
                lean_closure_set(v___x_910_, 3, lean_box(0));
                lean_closure_set(v___x_910_, 4, v_getEnv_907_);
                v___f_911_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_911_, 0, v___f_909_);
                lean_closure_set(v___f_911_, 1, v___f_902_);
                v___x_912_ = lean_alloc_closure(
                    l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_912_, 0, lean_box(0));
                lean_closure_set(v___x_912_, 1, v___x_910_);
                v___x_913_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_913_, 0, v___x_912_);
                lean_ctor_set(v___x_913_, 1, v___f_911_);
                v___x_914_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25,
                );
                v___x_915_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
                lean_inc_ref(v_toMonadRef_901_);
                v___x_916_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_916_, 0, v___x_914_);
                lean_ctor_set(v___x_916_, 1, v_toMonadRef_901_);
                lean_ctor_set(v___x_916_, 2, v___x_915_);
                match lean_obj_tag(v_v_827_) {
                    0 => {
                        lean_dec_ref_known(v___x_913_, 2);
                        v_val_917_ = lean_ctor_get(v_v_827_, 0);
                        v_isSharedCheck_932_ = (!lean_is_exclusive(v_v_827_)) as u8;
                        if v_isSharedCheck_932_ == 0 {
                            v___x_919_ = v_v_827_;
                            v_isShared_920_ = v_isSharedCheck_932_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_val_917_);
                            lean_dec(v_v_827_);
                            v___x_919_ = lean_box(0);
                            v_isShared_920_ = v_isSharedCheck_932_;
                            state = 9;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec_ref_known(v___x_913_, 2);
                        v_val_933_ = lean_ctor_get(v_v_827_, 0);
                        lean_inc_n(v_val_933_, 2);
                        lean_dec_ref_known(v_v_827_, 1);
                        v___x_934_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once
                            ),
                            _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31,
                        );
                        v___x_935_ = l_Lean_MessageData_ofSyntax(v_val_933_);
                        v___x_936_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_936_, 0, v___x_934_);
                        lean_ctor_set(v___x_936_, 1, v___x_935_);
                        v___x_937_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once
                            ),
                            _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33,
                        );
                        v___x_938_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_938_, 0, v___x_936_);
                        lean_ctor_set(v___x_938_, 1, v___x_937_);
                        v___x_1822__overap_939_ = l_Lean_throwErrorAt___redArg(
                            v___x_898_, v___x_916_, v_val_933_, v___x_938_,
                        );
                        lean_inc(v_a_833_);
                        lean_inc_ref(v_a_832_);
                        lean_inc(v_a_831_);
                        lean_inc_ref(v_a_830_);
                        lean_inc(v_a_829_);
                        lean_inc_ref(v_a_828_);
                        v___x_940_ = lean_apply_7(
                            v___x_1822__overap_939_,
                            v_a_828_,
                            v_a_829_,
                            v_a_830_,
                            v_a_831_,
                            v_a_832_,
                            v_a_833_,
                            lean_box(0),
                        );
                        return v___x_940_;
                    }
                    _ => {
                        v_val_941_ = lean_ctor_get(v_v_827_, 0);
                        v_isSharedCheck_1004_ = (!lean_is_exclusive(v_v_827_)) as u8;
                        if v_isSharedCheck_1004_ == 0 {
                            v___x_943_ = v_v_827_;
                            v_isShared_944_ = v_isSharedCheck_1004_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_val_941_);
                            lean_dec(v_v_827_);
                            v___x_943_ = lean_box(0);
                            v_isShared_944_ = v_isSharedCheck_1004_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_921_ = l_Lean_TSyntax_getId(v_val_917_);
                v_y_922_ = lean_erase_macro_scopes(v___x_921_);
                v___x_923_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27;
                v___x_924_ = lean_name_eq(v_y_922_, v___x_923_);
                lean_dec(v_y_922_);
                if v___x_924_ == 0 {
                    lean_del_object(v___x_919_);
                    v___x_925_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29,
                    );
                    v___x_2160__overap_926_ = l_Lean_throwErrorAt___redArg(
                        v___x_898_, v___x_916_, v_val_917_, v___x_925_,
                    );
                    lean_inc(v_a_833_);
                    lean_inc_ref(v_a_832_);
                    lean_inc(v_a_831_);
                    lean_inc_ref(v_a_830_);
                    lean_inc(v_a_829_);
                    lean_inc_ref(v_a_828_);
                    v___x_927_ = lean_apply_7(
                        v___x_2160__overap_926_,
                        v_a_828_,
                        v_a_829_,
                        v_a_830_,
                        v_a_831_,
                        v_a_832_,
                        v_a_833_,
                        lean_box(0),
                    );
                    return v___x_927_;
                } else {
                    lean_dec(v_val_917_);
                    lean_dec_ref_known(v___x_916_, 3);
                    lean_dec_ref(v___x_898_);
                    v___x_928_ = lean_box(0);
                    if v_isShared_920_ == 0 {
                        lean_ctor_set(v___x_919_, 0, v___x_928_);
                        v___x_930_ = v___x_919_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                        v___x_930_ = v_reuseFailAlloc_931_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_930_;
            }
            11 => {
                v_fileName_945_ = lean_ctor_get(v_a_832_, 0);
                v_fileMap_946_ = lean_ctor_get(v_a_832_, 1);
                v_options_947_ = lean_ctor_get(v_a_832_, 2);
                v_currRecDepth_948_ = lean_ctor_get(v_a_832_, 3);
                v_maxRecDepth_949_ = lean_ctor_get(v_a_832_, 4);
                v_ref_950_ = lean_ctor_get(v_a_832_, 5);
                v_currNamespace_951_ = lean_ctor_get(v_a_832_, 6);
                v_openDecls_952_ = lean_ctor_get(v_a_832_, 7);
                v_initHeartbeats_953_ = lean_ctor_get(v_a_832_, 8);
                v_maxHeartbeats_954_ = lean_ctor_get(v_a_832_, 9);
                v_quotContext_955_ = lean_ctor_get(v_a_832_, 10);
                v_currMacroScope_956_ = lean_ctor_get(v_a_832_, 11);
                v_diag_957_ = lean_ctor_get_uint8(
                    v_a_832_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_958_ = lean_ctor_get(v_a_832_, 12);
                v_suppressElabErrors_959_ = lean_ctor_get_uint8(
                    v_a_832_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_960_ = lean_ctor_get(v_a_832_, 13);
                v___x_961_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39;
                v___f_962_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__41;
                v_ref_963_ = l_Lean_replaceRef(v_val_941_, v_ref_950_);
                lean_inc_ref(v_inheritedTraceOptions_960_);
                lean_inc(v_cancelTk_x3f_958_);
                lean_inc(v_currMacroScope_956_);
                lean_inc(v_quotContext_955_);
                lean_inc(v_maxHeartbeats_954_);
                lean_inc(v_initHeartbeats_953_);
                lean_inc(v_openDecls_952_);
                lean_inc(v_currNamespace_951_);
                lean_inc(v_maxRecDepth_949_);
                lean_inc(v_currRecDepth_948_);
                lean_inc_ref(v_options_947_);
                lean_inc_ref(v_fileMap_946_);
                lean_inc_ref(v_fileName_945_);
                v___x_964_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_964_, 0, v_fileName_945_);
                lean_ctor_set(v___x_964_, 1, v_fileMap_946_);
                lean_ctor_set(v___x_964_, 2, v_options_947_);
                lean_ctor_set(v___x_964_, 3, v_currRecDepth_948_);
                lean_ctor_set(v___x_964_, 4, v_maxRecDepth_949_);
                lean_ctor_set(v___x_964_, 5, v_ref_963_);
                lean_ctor_set(v___x_964_, 6, v_currNamespace_951_);
                lean_ctor_set(v___x_964_, 7, v_openDecls_952_);
                lean_ctor_set(v___x_964_, 8, v_initHeartbeats_953_);
                lean_ctor_set(v___x_964_, 9, v_maxHeartbeats_954_);
                lean_ctor_set(v___x_964_, 10, v_quotContext_955_);
                lean_ctor_set(v___x_964_, 11, v_currMacroScope_956_);
                lean_ctor_set(v___x_964_, 12, v_cancelTk_x3f_958_);
                lean_ctor_set(v___x_964_, 13, v_inheritedTraceOptions_960_);
                lean_ctor_set_uint8(
                    v___x_964_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_957_,
                );
                lean_ctor_set_uint8(
                    v___x_964_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_959_,
                );
                lean_inc_ref(v___x_916_);
                lean_inc(v_toMonadFileMap_905_);
                lean_inc_ref(v___x_898_);
                v___x_2093__overap_965_ = l_Lean_Doc_parseQuotedStrLit___redArg(
                    v___x_898_,
                    v_toMonadFileMap_905_,
                    v___x_913_,
                    v___x_916_,
                    v___x_904_,
                    v___x_961_,
                    v___f_962_,
                    v_val_941_,
                );
                lean_inc(v_a_833_);
                lean_inc(v_a_831_);
                lean_inc_ref(v_a_830_);
                lean_inc(v_a_829_);
                lean_inc_ref(v_a_828_);
                v___x_966_ = lean_apply_7(
                    v___x_2093__overap_965_,
                    v_a_828_,
                    v_a_829_,
                    v_a_830_,
                    v_a_831_,
                    v___x_964_,
                    v_a_833_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_966_) == 0 {
                    v_a_967_ = lean_ctor_get(v___x_966_, 0);
                    v_isSharedCheck_995_ = (!lean_is_exclusive(v___x_966_)) as u8;
                    if v_isSharedCheck_995_ == 0 {
                        v___x_969_ = v___x_966_;
                        v_isShared_970_ = v_isSharedCheck_995_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_967_);
                        lean_dec(v___x_966_);
                        v___x_969_ = lean_box(0);
                        v_isShared_970_ = v_isSharedCheck_995_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_943_);
                    lean_dec_ref_known(v___x_916_, 3);
                    lean_dec_ref(v___x_898_);
                    v_a_996_ = lean_ctor_get(v___x_966_, 0);
                    v_isSharedCheck_1003_ = (!lean_is_exclusive(v___x_966_)) as u8;
                    if v_isSharedCheck_1003_ == 0 {
                        v___x_998_ = v___x_966_;
                        v_isShared_999_ = v_isSharedCheck_1003_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_996_);
                        lean_dec(v___x_966_);
                        v___x_998_ = lean_box(0);
                        v_isShared_999_ = v_isSharedCheck_1003_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_971_ = lean_unsigned_to_nat(0);
                v___x_972_ =
                    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17;
                lean_inc(v_a_967_);
                v___x_973_ = l_Lean_Syntax_isOfKind(v_a_967_, v___x_972_);
                if v___x_973_ == 0 {
                    lean_del_object(v___x_969_);
                    lean_del_object(v___x_943_);
                    v___x_974_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43,
                    );
                    lean_inc(v_a_967_);
                    v___x_975_ = l_Lean_MessageData_ofSyntax(v_a_967_);
                    v___x_976_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_976_, 0, v___x_974_);
                    lean_ctor_set(v___x_976_, 1, v___x_975_);
                    v___x_977_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33,
                    );
                    v___x_978_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_978_, 0, v___x_976_);
                    lean_ctor_set(v___x_978_, 1, v___x_977_);
                    v___x_2204__overap_979_ =
                        l_Lean_throwErrorAt___redArg(v___x_898_, v___x_916_, v_a_967_, v___x_978_);
                    lean_inc(v_a_833_);
                    lean_inc_ref(v_a_832_);
                    lean_inc(v_a_831_);
                    lean_inc_ref(v_a_830_);
                    lean_inc(v_a_829_);
                    lean_inc_ref(v_a_828_);
                    v___x_980_ = lean_apply_7(
                        v___x_2204__overap_979_,
                        v_a_828_,
                        v_a_829_,
                        v_a_830_,
                        v_a_831_,
                        v_a_832_,
                        v_a_833_,
                        lean_box(0),
                    );
                    return v___x_980_;
                } else {
                    lean_dec_ref_known(v___x_916_, 3);
                    lean_dec_ref(v___x_898_);
                    v___f_981_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__44;
                    v___x_982_ = l_Lean_Syntax_getArg(v_a_967_, v___x_971_);
                    lean_dec(v_a_967_);
                    v___x_983_ = l_Lean_Syntax_getArgs(v___x_982_);
                    lean_dec(v___x_982_);
                    v___x_984_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_983_);
                    lean_dec_ref(v___x_983_);
                    v___x_985_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54;
                    v_sz_986_ = lean_array_size(v___x_984_);
                    v___x_987_ = 0usize;
                    v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_985_,
                        v___f_981_,
                        v_sz_986_,
                        v___x_987_,
                        v___x_984_,
                    );
                    if v_isShared_944_ == 0 {
                        lean_ctor_set_tag(v___x_943_, 1);
                        lean_ctor_set(v___x_943_, 0, v___x_988_);
                        v___x_990_ = v___x_943_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_988_);
                        v___x_990_ = v_reuseFailAlloc_994_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_970_ == 0 {
                    lean_ctor_set(v___x_969_, 0, v___x_990_);
                    v___x_992_ = v___x_969_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
                    v___x_992_ = v_reuseFailAlloc_993_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_992_;
            }
            15 => {
                if v_isShared_999_ == 0 {
                    v___x_1001_ = v___x_998_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
                    v___x_1001_ = v_reuseFailAlloc_1002_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___private__1___boxed(
    mut v_v_1017_: *mut LeanObject,
    mut v_a_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Lean_Doc_instFromDocArgDocScope___private__1(
        v_v_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_,
    );
    lean_dec(v_a_1023_);
    lean_dec_ref(v_a_1022_);
    lean_dec(v_a_1021_);
    lean_dec_ref(v_a_1020_);
    lean_dec(v_a_1019_);
    lean_dec_ref(v_a_1018_);
    return v_res_1025_;
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___lam__2(
    mut v___f_1026_: *mut LeanObject,
    mut v___f_1027_: *mut LeanObject,
    mut v_v_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
    mut v___y_1030_: *mut LeanObject,
    mut v___y_1031_: *mut LeanObject,
    mut v___y_1032_: *mut LeanObject,
    mut v___y_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v_toFunctor_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___f_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v_toFunctor_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___f_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyEnv_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1121_: u8 = 0;
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306__overap_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_val_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317__overap_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v_fileName_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1158_: u8 = 0;
    let mut v_cancelTk_x3f_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1160_: u8 = 0;
    let mut v_inheritedTraceOptions_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327__overap_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358__overap_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1187_: usize = 0;
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut v_a_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1200_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_reuseFailAlloc_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_unused_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_unused_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_unused_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_unused_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__1,
                );
                v_toApplicative_1037_ = lean_ctor_get(v___x_1036_, 0);
                v_toFunctor_1038_ = lean_ctor_get(v_toApplicative_1037_, 0);
                v_toSeq_1039_ = lean_ctor_get(v_toApplicative_1037_, 2);
                v_toSeqLeft_1040_ = lean_ctor_get(v_toApplicative_1037_, 3);
                v_toSeqRight_1041_ = lean_ctor_get(v_toApplicative_1037_, 4);
                v___f_1042_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__2;
                v___f_1043_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__3;
                lean_inc_ref_n(v_toFunctor_1038_, 2);
                v___f_1044_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1044_, 0, v_toFunctor_1038_);
                v___f_1045_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1045_, 0, v_toFunctor_1038_);
                v___x_1046_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1046_, 0, v___f_1044_);
                lean_ctor_set(v___x_1046_, 1, v___f_1045_);
                lean_inc(v_toSeqRight_1041_);
                v___f_1047_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1047_, 0, v_toSeqRight_1041_);
                lean_inc(v_toSeqLeft_1040_);
                v___f_1048_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1048_, 0, v_toSeqLeft_1040_);
                lean_inc(v_toSeq_1039_);
                v___f_1049_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1049_, 0, v_toSeq_1039_);
                v___x_1050_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1050_, 0, v___x_1046_);
                lean_ctor_set(v___x_1050_, 1, v___f_1042_);
                lean_ctor_set(v___x_1050_, 2, v___f_1049_);
                lean_ctor_set(v___x_1050_, 3, v___f_1048_);
                lean_ctor_set(v___x_1050_, 4, v___f_1047_);
                v___x_1051_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1051_, 0, v___x_1050_);
                lean_ctor_set(v___x_1051_, 1, v___f_1043_);
                v___x_1052_ = l_StateRefT_x27_instMonad___redArg(v___x_1051_);
                v_toApplicative_1053_ = lean_ctor_get(v___x_1052_, 0);
                v_isSharedCheck_1216_ = (!lean_is_exclusive(v___x_1052_)) as u8;
                if v_isSharedCheck_1216_ == 0 {
                    v_unused_1217_ = lean_ctor_get(v___x_1052_, 1);
                    lean_dec(v_unused_1217_);
                    v___x_1055_ = v___x_1052_;
                    v_isShared_1056_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1053_);
                    lean_dec(v___x_1052_);
                    v___x_1055_ = lean_box(0);
                    v_isShared_1056_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1057_ = lean_ctor_get(v_toApplicative_1053_, 0);
                v_toSeq_1058_ = lean_ctor_get(v_toApplicative_1053_, 2);
                v_toSeqLeft_1059_ = lean_ctor_get(v_toApplicative_1053_, 3);
                v_toSeqRight_1060_ = lean_ctor_get(v_toApplicative_1053_, 4);
                v_isSharedCheck_1214_ = (!lean_is_exclusive(v_toApplicative_1053_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v_unused_1215_ = lean_ctor_get(v_toApplicative_1053_, 1);
                    lean_dec(v_unused_1215_);
                    v___x_1062_ = v_toApplicative_1053_;
                    v_isShared_1063_ = v_isSharedCheck_1214_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1060_);
                    lean_inc(v_toSeqLeft_1059_);
                    lean_inc(v_toSeq_1058_);
                    lean_inc(v_toFunctor_1057_);
                    lean_dec(v_toApplicative_1053_);
                    v___x_1062_ = lean_box(0);
                    v_isShared_1063_ = v_isSharedCheck_1214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1064_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__4;
                v___f_1065_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__5;
                lean_inc_ref(v_toFunctor_1057_);
                v___f_1066_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1066_, 0, v_toFunctor_1057_);
                v___f_1067_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1067_, 0, v_toFunctor_1057_);
                v___x_1068_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1068_, 0, v___f_1066_);
                lean_ctor_set(v___x_1068_, 1, v___f_1067_);
                v___f_1069_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1069_, 0, v_toSeqRight_1060_);
                v___f_1070_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1070_, 0, v_toSeqLeft_1059_);
                v___f_1071_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1071_, 0, v_toSeq_1058_);
                if v_isShared_1063_ == 0 {
                    lean_ctor_set(v___x_1062_, 4, v___f_1069_);
                    lean_ctor_set(v___x_1062_, 3, v___f_1070_);
                    lean_ctor_set(v___x_1062_, 2, v___f_1071_);
                    lean_ctor_set(v___x_1062_, 1, v___f_1064_);
                    lean_ctor_set(v___x_1062_, 0, v___x_1068_);
                    v___x_1073_ = v___x_1062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1068_);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___f_1064_);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 2, v___f_1071_);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 3, v___f_1070_);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___f_1069_);
                    v___x_1073_ = v_reuseFailAlloc_1213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1056_ == 0 {
                    lean_ctor_set(v___x_1055_, 1, v___f_1065_);
                    lean_ctor_set(v___x_1055_, 0, v___x_1073_);
                    v___x_1075_ = v___x_1055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___f_1065_);
                    v___x_1075_ = v_reuseFailAlloc_1212_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1076_ = l_StateRefT_x27_instMonad___redArg(v___x_1075_);
                v_toApplicative_1077_ = lean_ctor_get(v___x_1076_, 0);
                v_isSharedCheck_1210_ = (!lean_is_exclusive(v___x_1076_)) as u8;
                if v_isSharedCheck_1210_ == 0 {
                    v_unused_1211_ = lean_ctor_get(v___x_1076_, 1);
                    lean_dec(v_unused_1211_);
                    v___x_1079_ = v___x_1076_;
                    v_isShared_1080_ = v_isSharedCheck_1210_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1077_);
                    lean_dec(v___x_1076_);
                    v___x_1079_ = lean_box(0);
                    v_isShared_1080_ = v_isSharedCheck_1210_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1081_ = lean_ctor_get(v_toApplicative_1077_, 0);
                v_toSeq_1082_ = lean_ctor_get(v_toApplicative_1077_, 2);
                v_toSeqLeft_1083_ = lean_ctor_get(v_toApplicative_1077_, 3);
                v_toSeqRight_1084_ = lean_ctor_get(v_toApplicative_1077_, 4);
                v_isSharedCheck_1208_ = (!lean_is_exclusive(v_toApplicative_1077_)) as u8;
                if v_isSharedCheck_1208_ == 0 {
                    v_unused_1209_ = lean_ctor_get(v_toApplicative_1077_, 1);
                    lean_dec(v_unused_1209_);
                    v___x_1086_ = v_toApplicative_1077_;
                    v_isShared_1087_ = v_isSharedCheck_1208_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1084_);
                    lean_inc(v_toSeqLeft_1083_);
                    lean_inc(v_toSeq_1082_);
                    lean_inc(v_toFunctor_1081_);
                    lean_dec(v_toApplicative_1077_);
                    v___x_1086_ = lean_box(0);
                    v_isShared_1087_ = v_isSharedCheck_1208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1088_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__6;
                v___f_1089_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__7;
                lean_inc_ref(v_toFunctor_1081_);
                v___f_1090_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1090_, 0, v_toFunctor_1081_);
                v___f_1091_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1091_, 0, v_toFunctor_1081_);
                v___x_1092_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1092_, 0, v___f_1090_);
                lean_ctor_set(v___x_1092_, 1, v___f_1091_);
                v___f_1093_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1093_, 0, v_toSeqRight_1084_);
                v___f_1094_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1094_, 0, v_toSeqLeft_1083_);
                v___f_1095_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1095_, 0, v_toSeq_1082_);
                if v_isShared_1087_ == 0 {
                    lean_ctor_set(v___x_1086_, 4, v___f_1093_);
                    lean_ctor_set(v___x_1086_, 3, v___f_1094_);
                    lean_ctor_set(v___x_1086_, 2, v___f_1095_);
                    lean_ctor_set(v___x_1086_, 1, v___f_1088_);
                    lean_ctor_set(v___x_1086_, 0, v___x_1092_);
                    v___x_1097_ = v___x_1086_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1092_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___f_1088_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 2, v___f_1095_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___f_1094_);
                    lean_ctor_set(v_reuseFailAlloc_1207_, 4, v___f_1093_);
                    v___x_1097_ = v_reuseFailAlloc_1207_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1080_ == 0 {
                    lean_ctor_set(v___x_1079_, 1, v___f_1089_);
                    lean_ctor_set(v___x_1079_, 0, v___x_1097_);
                    v___x_1099_ = v___x_1079_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1097_);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___f_1089_);
                    v___x_1099_ = v_reuseFailAlloc_1206_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1100_ = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
                v_toMonadQuotation_1101_ = lean_ctor_get(v___x_1100_, 0);
                v_toMonadRef_1102_ = lean_ctor_get(v_toMonadQuotation_1101_, 0);
                v___f_1103_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__8;
                v___x_1104_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__9;
                v___x_1105_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__13,
                );
                v_toMonadFileMap_1106_ = lean_ctor_get(v___x_1105_, 0);
                v___x_1107_ = l_Lean_Meta_instMonadEnvMetaM;
                v_getEnv_1108_ = lean_ctor_get(v___x_1107_, 0);
                v_modifyEnv_1109_ = lean_ctor_get(v___x_1107_, 1);
                lean_inc(v_modifyEnv_1109_);
                v___f_1110_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1110_, 0, v_modifyEnv_1109_);
                lean_closure_set(v___f_1110_, 1, v___x_1104_);
                lean_inc(v_getEnv_1108_);
                v___x_1111_ = lean_alloc_closure(
                    l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___x_1111_, 0, lean_box(0));
                lean_closure_set(v___x_1111_, 1, lean_box(0));
                lean_closure_set(v___x_1111_, 2, lean_box(0));
                lean_closure_set(v___x_1111_, 3, lean_box(0));
                lean_closure_set(v___x_1111_, 4, v_getEnv_1108_);
                v___f_1112_ = lean_alloc_closure(
                    l_Lean_instMonadEnvOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1112_, 0, v___f_1110_);
                lean_closure_set(v___f_1112_, 1, v___f_1103_);
                v___x_1113_ = lean_alloc_closure(
                    l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_1113_, 0, lean_box(0));
                lean_closure_set(v___x_1113_, 1, v___x_1111_);
                v___x_1114_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1114_, 0, v___x_1113_);
                lean_ctor_set(v___x_1114_, 1, v___f_1112_);
                v___x_1115_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25_once
                    ),
                    _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__25,
                );
                v___x_1116_ = l_Lean_Elab_Term_instAddErrorMessageContextTermElabM;
                lean_inc_ref(v_toMonadRef_1102_);
                v___x_1117_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1117_, 0, v___x_1115_);
                lean_ctor_set(v___x_1117_, 1, v_toMonadRef_1102_);
                lean_ctor_set(v___x_1117_, 2, v___x_1116_);
                match lean_obj_tag(v_v_1028_) {
                    0 => {
                        lean_dec_ref_known(v___x_1114_, 2);
                        lean_dec_ref(v___f_1027_);
                        lean_dec_ref(v___f_1026_);
                        v_val_1118_ = lean_ctor_get(v_v_1028_, 0);
                        v_isSharedCheck_1133_ = (!lean_is_exclusive(v_v_1028_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v___x_1120_ = v_v_1028_;
                            v_isShared_1121_ = v_isSharedCheck_1133_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_val_1118_);
                            lean_dec(v_v_1028_);
                            v___x_1120_ = lean_box(0);
                            v_isShared_1121_ = v_isSharedCheck_1133_;
                            state = 9;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec_ref_known(v___x_1114_, 2);
                        lean_dec_ref(v___f_1027_);
                        lean_dec_ref(v___f_1026_);
                        v_val_1134_ = lean_ctor_get(v_v_1028_, 0);
                        lean_inc_n(v_val_1134_, 2);
                        lean_dec_ref_known(v_v_1028_, 1);
                        v___x_1135_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31_once
                            ),
                            _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__31,
                        );
                        v___x_1136_ = l_Lean_MessageData_ofSyntax(v_val_1134_);
                        v___x_1137_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1137_, 0, v___x_1135_);
                        lean_ctor_set(v___x_1137_, 1, v___x_1136_);
                        v___x_1138_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once
                            ),
                            _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33,
                        );
                        v___x_1139_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1139_, 0, v___x_1137_);
                        lean_ctor_set(v___x_1139_, 1, v___x_1138_);
                        v___x_317__overap_1140_ = l_Lean_throwErrorAt___redArg(
                            v___x_1099_,
                            v___x_1117_,
                            v_val_1134_,
                            v___x_1139_,
                        );
                        lean_inc(v___y_1034_);
                        lean_inc_ref(v___y_1033_);
                        lean_inc(v___y_1032_);
                        lean_inc_ref(v___y_1031_);
                        lean_inc(v___y_1030_);
                        lean_inc_ref(v___y_1029_);
                        v___x_1141_ = lean_apply_7(
                            v___x_317__overap_1140_,
                            v___y_1029_,
                            v___y_1030_,
                            v___y_1031_,
                            v___y_1032_,
                            v___y_1033_,
                            v___y_1034_,
                            lean_box(0),
                        );
                        return v___x_1141_;
                    }
                    _ => {
                        v_val_1142_ = lean_ctor_get(v_v_1028_, 0);
                        v_isSharedCheck_1205_ = (!lean_is_exclusive(v_v_1028_)) as u8;
                        if v_isSharedCheck_1205_ == 0 {
                            v___x_1144_ = v_v_1028_;
                            v_isShared_1145_ = v_isSharedCheck_1205_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_val_1142_);
                            lean_dec(v_v_1028_);
                            v___x_1144_ = lean_box(0);
                            v_isShared_1145_ = v_isSharedCheck_1205_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_1122_ = l_Lean_TSyntax_getId(v_val_1118_);
                v_y_1123_ = lean_erase_macro_scopes(v___x_1122_);
                v___x_1124_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__27;
                v___x_1125_ = lean_name_eq(v_y_1123_, v___x_1124_);
                lean_dec(v_y_1123_);
                if v___x_1125_ == 0 {
                    lean_del_object(v___x_1120_);
                    v___x_1126_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__29,
                    );
                    v___x_306__overap_1127_ = l_Lean_throwErrorAt___redArg(
                        v___x_1099_,
                        v___x_1117_,
                        v_val_1118_,
                        v___x_1126_,
                    );
                    lean_inc(v___y_1034_);
                    lean_inc_ref(v___y_1033_);
                    lean_inc(v___y_1032_);
                    lean_inc_ref(v___y_1031_);
                    lean_inc(v___y_1030_);
                    lean_inc_ref(v___y_1029_);
                    v___x_1128_ = lean_apply_7(
                        v___x_306__overap_1127_,
                        v___y_1029_,
                        v___y_1030_,
                        v___y_1031_,
                        v___y_1032_,
                        v___y_1033_,
                        v___y_1034_,
                        lean_box(0),
                    );
                    return v___x_1128_;
                } else {
                    lean_dec(v_val_1118_);
                    lean_dec_ref_known(v___x_1117_, 3);
                    lean_dec_ref(v___x_1099_);
                    v___x_1129_ = lean_box(0);
                    if v_isShared_1121_ == 0 {
                        lean_ctor_set(v___x_1120_, 0, v___x_1129_);
                        v___x_1131_ = v___x_1120_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
                        v___x_1131_ = v_reuseFailAlloc_1132_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1131_;
            }
            11 => {
                v_fileName_1146_ = lean_ctor_get(v___y_1033_, 0);
                v_fileMap_1147_ = lean_ctor_get(v___y_1033_, 1);
                v_options_1148_ = lean_ctor_get(v___y_1033_, 2);
                v_currRecDepth_1149_ = lean_ctor_get(v___y_1033_, 3);
                v_maxRecDepth_1150_ = lean_ctor_get(v___y_1033_, 4);
                v_ref_1151_ = lean_ctor_get(v___y_1033_, 5);
                v_currNamespace_1152_ = lean_ctor_get(v___y_1033_, 6);
                v_openDecls_1153_ = lean_ctor_get(v___y_1033_, 7);
                v_initHeartbeats_1154_ = lean_ctor_get(v___y_1033_, 8);
                v_maxHeartbeats_1155_ = lean_ctor_get(v___y_1033_, 9);
                v_quotContext_1156_ = lean_ctor_get(v___y_1033_, 10);
                v_currMacroScope_1157_ = lean_ctor_get(v___y_1033_, 11);
                v_diag_1158_ = lean_ctor_get_uint8(
                    v___y_1033_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1159_ = lean_ctor_get(v___y_1033_, 12);
                v_suppressElabErrors_1160_ = lean_ctor_get_uint8(
                    v___y_1033_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1161_ = lean_ctor_get(v___y_1033_, 13);
                v___x_1162_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__39;
                v___x_1163_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__40;
                v___f_1164_ = lean_alloc_closure(
                    l_Lean_Doc_instFromDocArgDocScope___private__1___lam__1
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_1164_, 0, v___x_1163_);
                lean_closure_set(v___f_1164_, 1, v___f_1026_);
                v_ref_1165_ = l_Lean_replaceRef(v_val_1142_, v_ref_1151_);
                lean_inc_ref(v_inheritedTraceOptions_1161_);
                lean_inc(v_cancelTk_x3f_1159_);
                lean_inc(v_currMacroScope_1157_);
                lean_inc(v_quotContext_1156_);
                lean_inc(v_maxHeartbeats_1155_);
                lean_inc(v_initHeartbeats_1154_);
                lean_inc(v_openDecls_1153_);
                lean_inc(v_currNamespace_1152_);
                lean_inc(v_maxRecDepth_1150_);
                lean_inc(v_currRecDepth_1149_);
                lean_inc_ref(v_options_1148_);
                lean_inc_ref(v_fileMap_1147_);
                lean_inc_ref(v_fileName_1146_);
                v___x_1166_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_1166_, 0, v_fileName_1146_);
                lean_ctor_set(v___x_1166_, 1, v_fileMap_1147_);
                lean_ctor_set(v___x_1166_, 2, v_options_1148_);
                lean_ctor_set(v___x_1166_, 3, v_currRecDepth_1149_);
                lean_ctor_set(v___x_1166_, 4, v_maxRecDepth_1150_);
                lean_ctor_set(v___x_1166_, 5, v_ref_1165_);
                lean_ctor_set(v___x_1166_, 6, v_currNamespace_1152_);
                lean_ctor_set(v___x_1166_, 7, v_openDecls_1153_);
                lean_ctor_set(v___x_1166_, 8, v_initHeartbeats_1154_);
                lean_ctor_set(v___x_1166_, 9, v_maxHeartbeats_1155_);
                lean_ctor_set(v___x_1166_, 10, v_quotContext_1156_);
                lean_ctor_set(v___x_1166_, 11, v_currMacroScope_1157_);
                lean_ctor_set(v___x_1166_, 12, v_cancelTk_x3f_1159_);
                lean_ctor_set(v___x_1166_, 13, v_inheritedTraceOptions_1161_);
                lean_ctor_set_uint8(
                    v___x_1166_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_1158_,
                );
                lean_ctor_set_uint8(
                    v___x_1166_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1160_,
                );
                lean_inc_ref(v___x_1117_);
                lean_inc(v_toMonadFileMap_1106_);
                lean_inc_ref(v___x_1099_);
                v___x_327__overap_1167_ = l_Lean_Doc_parseQuotedStrLit___redArg(
                    v___x_1099_,
                    v_toMonadFileMap_1106_,
                    v___x_1114_,
                    v___x_1117_,
                    v___x_1105_,
                    v___x_1162_,
                    v___f_1164_,
                    v_val_1142_,
                );
                lean_inc(v___y_1034_);
                lean_inc(v___y_1032_);
                lean_inc_ref(v___y_1031_);
                lean_inc(v___y_1030_);
                lean_inc_ref(v___y_1029_);
                v___x_1168_ = lean_apply_7(
                    v___x_327__overap_1167_,
                    v___y_1029_,
                    v___y_1030_,
                    v___y_1031_,
                    v___y_1032_,
                    v___x_1166_,
                    v___y_1034_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1168_) == 0 {
                    v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
                    v_isSharedCheck_1196_ = (!lean_is_exclusive(v___x_1168_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v___x_1171_ = v___x_1168_;
                        v_isShared_1172_ = v_isSharedCheck_1196_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1169_);
                        lean_dec(v___x_1168_);
                        v___x_1171_ = lean_box(0);
                        v_isShared_1172_ = v_isSharedCheck_1196_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1144_);
                    lean_dec_ref_known(v___x_1117_, 3);
                    lean_dec_ref(v___x_1099_);
                    lean_dec_ref(v___f_1027_);
                    v_a_1197_ = lean_ctor_get(v___x_1168_, 0);
                    v_isSharedCheck_1204_ = (!lean_is_exclusive(v___x_1168_)) as u8;
                    if v_isSharedCheck_1204_ == 0 {
                        v___x_1199_ = v___x_1168_;
                        v_isShared_1200_ = v_isSharedCheck_1204_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1197_);
                        lean_dec(v___x_1168_);
                        v___x_1199_ = lean_box(0);
                        v_isShared_1200_ = v_isSharedCheck_1204_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_1173_ = lean_unsigned_to_nat(0);
                v___x_1174_ =
                    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports___closed__17;
                lean_inc(v_a_1169_);
                v___x_1175_ = l_Lean_Syntax_isOfKind(v_a_1169_, v___x_1174_);
                if v___x_1175_ == 0 {
                    lean_del_object(v___x_1171_);
                    lean_del_object(v___x_1144_);
                    lean_dec_ref(v___f_1027_);
                    v___x_1176_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__43,
                    );
                    lean_inc(v_a_1169_);
                    v___x_1177_ = l_Lean_MessageData_ofSyntax(v_a_1169_);
                    v___x_1178_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1178_, 0, v___x_1176_);
                    lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                    v___x_1179_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33_once
                        ),
                        _init_l_Lean_Doc_instFromDocArgDocScope___private__1___closed__33,
                    );
                    v___x_1180_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1180_, 0, v___x_1178_);
                    lean_ctor_set(v___x_1180_, 1, v___x_1179_);
                    v___x_358__overap_1181_ = l_Lean_throwErrorAt___redArg(
                        v___x_1099_,
                        v___x_1117_,
                        v_a_1169_,
                        v___x_1180_,
                    );
                    lean_inc(v___y_1034_);
                    lean_inc_ref(v___y_1033_);
                    lean_inc(v___y_1032_);
                    lean_inc_ref(v___y_1031_);
                    lean_inc(v___y_1030_);
                    lean_inc_ref(v___y_1029_);
                    v___x_1182_ = lean_apply_7(
                        v___x_358__overap_1181_,
                        v___y_1029_,
                        v___y_1030_,
                        v___y_1031_,
                        v___y_1032_,
                        v___y_1033_,
                        v___y_1034_,
                        lean_box(0),
                    );
                    return v___x_1182_;
                } else {
                    lean_dec_ref_known(v___x_1117_, 3);
                    lean_dec_ref(v___x_1099_);
                    v___x_1183_ = l_Lean_Syntax_getArg(v_a_1169_, v___x_1173_);
                    lean_dec(v_a_1169_);
                    v___x_1184_ = l_Lean_Syntax_getArgs(v___x_1183_);
                    lean_dec(v___x_1183_);
                    v___x_1185_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1184_);
                    lean_dec_ref(v___x_1184_);
                    v___x_1186_ = l_Lean_Doc_instFromDocArgDocScope___private__1___closed__54;
                    v_sz_1187_ = lean_array_size(v___x_1185_);
                    v___x_1188_ = 0usize;
                    v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1186_,
                        v___f_1027_,
                        v_sz_1187_,
                        v___x_1188_,
                        v___x_1185_,
                    );
                    if v_isShared_1145_ == 0 {
                        lean_ctor_set_tag(v___x_1144_, 1);
                        lean_ctor_set(v___x_1144_, 0, v___x_1189_);
                        v___x_1191_ = v___x_1144_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1189_);
                        v___x_1191_ = v_reuseFailAlloc_1195_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_1172_ == 0 {
                    lean_ctor_set(v___x_1171_, 0, v___x_1191_);
                    v___x_1193_ = v___x_1171_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1193_;
            }
            15 => {
                if v_isShared_1200_ == 0 {
                    v___x_1202_ = v___x_1199_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
                    v___x_1202_ = v_reuseFailAlloc_1203_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_instFromDocArgDocScope___lam__2___boxed(
    mut v___f_1218_: *mut LeanObject,
    mut v___f_1219_: *mut LeanObject,
    mut v_v_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1228_: *mut LeanObject = core::ptr::null_mut();
    v_res_1228_ = l_Lean_Doc_instFromDocArgDocScope___lam__2(
        v___f_1218_,
        v___f_1219_,
        v_v_1220_,
        v___y_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
        v___y_1225_,
        v___y_1226_,
    );
    lean_dec(v___y_1226_);
    lean_dec_ref(v___y_1225_);
    lean_dec(v___y_1224_);
    lean_dec_ref(v___y_1223_);
    lean_dec(v___y_1222_);
    lean_dec_ref(v___y_1221_);
    return v_res_1228_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports =
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports();
    lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_imports);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM =
        _init_l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM();
    lean_mark_persistent(l___private_Lean_Elab_DocString_Builtin_Scopes_0__Lean_Doc_importsM);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DocString_Builtin_Scopes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DocString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_DocString_Builtin_Scopes(builtin);
}
