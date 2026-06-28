// Lean compiler output
// Module: Lean.Elab.Deriving.Util
// Imports: Lean.Elab.Command Lean.Elab.DeclNameGen
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_mkCIdent, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_List_lengthTR___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_InductiveVal_isNested, l_Lean_instInhabitedInductiveVal_default,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg, l_Lean_Elab_Command_withScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::DeclNameGen::{
    initialize_Lean_Elab_DeclNameGen, l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27,
    runtime_initialize_Lean_Elab_DeclNameGen,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::l_Lean_Expr_fvarId_x21;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getDecl___redArg,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_isTypeCorrect;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::Parser::Term::Basic::{
    l_Lean_Parser_Term_explicitBinder, l_Lean_Parser_Term_implicitBinder,
    l_Lean_Parser_Term_instBinder,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_Deriving_implicitBinderF___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_implicitBinderF___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_implicitBinderF: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_instBinderF: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Deriving_explicitBinderF___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_explicitBinderF___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_explicitBinderF: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value:
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
    m_fun: l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Deriving_mkInductArgNames___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13290931718435096973 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [64, 0],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,6962862263136859431 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,16363371701764479942 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value) as *mut crate::leanh::LeanObject,7499624980761693169 as *mut crate::leanh::LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 115, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,9363914857124557226 as *mut crate::leanh::LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 96, 100, 101, 114, 105, 118, 105, 110,
        103, 32, 46, 46, 46, 32, 64, 91, 101, 120, 112, 111, 115, 101, 93, 96, 32, 119, 105, 116,
        104, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        96, 32, 97, 115, 32, 105, 116, 32, 104, 97, 115, 32, 111, 110, 101, 32, 111, 114, 32, 109,
        111, 114, 101, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkInstName___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [105, 110, 115, 116, 0],
    };
static mut l_Lean_Elab_Deriving_mkInstName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInstName___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12843180897352504333 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Deriving_mkContext___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__1_value)
                as *mut crate::leanh::LeanObject,
            3113176348997436611 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__3_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkContext___closed__6_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 78, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkContext___closed__8_value: crate::leanh::LeanStringObject<15> =
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
            32, 97, 117, 120, 70, 117, 110, 78, 97, 109, 101, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 99, 97, 108, 105, 110, 115, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,850437327472445489 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,13429426995999683896 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,8036185514257755965 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value) as *mut crate::leanh::LeanObject,17116161260408496210 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value) as *mut crate::leanh::LeanObject,13708106407786339395 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,146480343229376155 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,17404204824591055365 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0],
};
static mut l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9383794970646754147 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,17201320286889277233 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = 0;
    v___x_2913_ = l_Lean_Parser_Term_implicitBinder(v___x_2912_);
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_implicitBinderF() -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_implicitBinderF___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_implicitBinderF___closed__0_once),
        _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0,
    );
    return v___x_2914_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_instBinderF() -> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Parser_Term_instBinder;
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = 0;
    v___x_2917_ = l_Lean_Parser_Term_explicitBinder(v___x_2916_);
    return v___x_2917_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_explicitBinderF() -> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_explicitBinderF___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_explicitBinderF___closed__0_once),
        _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0,
    );
    return v___x_2918_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(
    mut v_k_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v_b_2922_: *mut crate::leanh::LeanObject,
    mut v_c_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2927_);
    crate::leanh::lean_inc_ref(v___y_2926_);
    crate::leanh::lean_inc(v___y_2925_);
    crate::leanh::lean_inc_ref(v___y_2924_);
    crate::leanh::lean_inc(v___y_2921_);
    crate::leanh::lean_inc_ref(v___y_2920_);
    v___x_2929_ = crate::leanh::lean_apply_9(
        v_k_2919_,
        v_b_2922_,
        v_c_2923_,
        v___y_2920_,
        v___y_2921_,
        v___y_2924_,
        v___y_2925_,
        v___y_2926_,
        v___y_2927_,
        crate::leanh::lean_box(0),
    );
    return v___x_2929_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed(
    mut v_k_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v_b_2933_: *mut crate::leanh::LeanObject,
    mut v_c_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(v_k_2930_, v___y_2931_, v___y_2932_, v_b_2933_, v_c_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
    crate::leanh::lean_dec(v___y_2938_);
    crate::leanh::lean_dec_ref(v___y_2937_);
    crate::leanh::lean_dec(v___y_2936_);
    crate::leanh::lean_dec_ref(v___y_2935_);
    crate::leanh::lean_dec(v___y_2932_);
    crate::leanh::lean_dec_ref(v___y_2931_);
    return v_res_2940_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(
    mut v_type_2941_: *mut crate::leanh::LeanObject,
    mut v_k_2942_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2943_: u8,
    mut v_whnfType_2944_: u8,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2946_);
                crate::leanh::lean_inc_ref(v___y_2945_);
                v___f_2952_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_2952_, 0, v_k_2942_);
                crate::leanh::lean_closure_set(v___f_2952_, 1, v___y_2945_);
                crate::leanh::lean_closure_set(v___f_2952_, 2, v___y_2946_);
                v___x_2953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_2941_,
                    v___f_2952_,
                    v_cleanupAnnotations_2943_,
                    v_whnfType_2944_,
                    v___y_2947_,
                    v___y_2948_,
                    v___y_2949_,
                    v___y_2950_,
                );
                if crate::leanh::lean_obj_tag(v___x_2953_) == 0 {
                    return v___x_2953_;
                } else {
                    v_a_2954_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
                    v_isSharedCheck_2961_ = (!crate::leanh::lean_is_exclusive(v___x_2953_)) as u8;
                    if v_isSharedCheck_2961_ == 0 {
                        v___x_2956_ = v___x_2953_;
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2954_);
                        crate::leanh::lean_dec(v___x_2953_);
                        v___x_2956_ = crate::leanh::lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2957_ == 0 {
                    v___x_2959_ = v___x_2956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___boxed(
    mut v_type_2962_: *mut crate::leanh::LeanObject,
    mut v_k_2963_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2964_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2973_: u8 = 0;
    let mut v_whnfType_boxed_2974_: u8 = 0;
    let mut v_res_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2973_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2964_) as u8);
    v_whnfType_boxed_2974_ = (crate::leanh::lean_unbox(v_whnfType_2965_) as u8);
    v_res_2975_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_2962_, v_k_2963_, v_cleanupAnnotations_boxed_2973_, v_whnfType_boxed_2974_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
    crate::leanh::lean_dec(v___y_2971_);
    crate::leanh::lean_dec_ref(v___y_2970_);
    crate::leanh::lean_dec(v___y_2969_);
    crate::leanh::lean_dec_ref(v___y_2968_);
    crate::leanh::lean_dec(v___y_2967_);
    crate::leanh::lean_dec_ref(v___y_2966_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(
    mut v_00_u03b1_2976_: *mut crate::leanh::LeanObject,
    mut v_type_2977_: *mut crate::leanh::LeanObject,
    mut v_k_2978_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2979_: u8,
    mut v_whnfType_2980_: u8,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_2977_, v_k_2978_, v_cleanupAnnotations_2979_, v_whnfType_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___boxed(
    mut v_00_u03b1_2989_: *mut crate::leanh::LeanObject,
    mut v_type_2990_: *mut crate::leanh::LeanObject,
    mut v_k_2991_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2992_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3001_: u8 = 0;
    let mut v_whnfType_boxed_3002_: u8 = 0;
    let mut v_res_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3001_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2992_) as u8);
    v_whnfType_boxed_3002_ = (crate::leanh::lean_unbox(v_whnfType_2993_) as u8);
    v_res_3003_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(
            v_00_u03b1_2989_,
            v_type_2990_,
            v_k_2991_,
            v_cleanupAnnotations_boxed_3001_,
            v_whnfType_boxed_3002_,
            v___y_2994_,
            v___y_2995_,
            v___y_2996_,
            v___y_2997_,
            v___y_2998_,
            v___y_2999_,
        );
    crate::leanh::lean_dec(v___y_2999_);
    crate::leanh::lean_dec_ref(v___y_2998_);
    crate::leanh::lean_dec(v___y_2997_);
    crate::leanh::lean_dec_ref(v___y_2996_);
    crate::leanh::lean_dec(v___y_2995_);
    crate::leanh::lean_dec_ref(v___y_2994_);
    return v_res_3003_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(
    mut v_as_3004_: *mut crate::leanh::LeanObject,
    mut v_sz_3005_: usize,
    mut v_i_3006_: usize,
    mut v_b_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    let mut v_a_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v_a_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3012_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
                if v___x_3012_ == 0 {
                    v___x_3013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3013_, 0, v_b_3007_);
                    return v___x_3013_;
                } else {
                    v_a_3014_ = lean_array_uget_borrowed(v_as_3004_, v_i_3006_);
                    v___x_3015_ = l_Lean_Expr_fvarId_x21(v_a_3014_);
                    v___x_3016_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_3015_,
                        v___y_3008_,
                        v___y_3009_,
                        v___y_3010_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3016_) == 0 {
                        v_a_3017_ = crate::leanh::lean_ctor_get(v___x_3016_, 0);
                        crate::leanh::lean_inc(v_a_3017_);
                        crate::leanh::lean_dec_ref_known(v___x_3016_, 1);
                        v___x_3018_ = l_Lean_LocalDecl_userName(v_a_3017_);
                        crate::leanh::lean_dec(v_a_3017_);
                        v___x_3019_ = lean_erase_macro_scopes(v___x_3018_);
                        v___x_3020_ =
                            l_Lean_Core_mkFreshUserName(v___x_3019_, v___y_3009_, v___y_3010_);
                        if crate::leanh::lean_obj_tag(v___x_3020_) == 0 {
                            v_a_3021_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                            crate::leanh::lean_inc(v_a_3021_);
                            crate::leanh::lean_dec_ref_known(v___x_3020_, 1);
                            v___x_3022_ = lean_array_push(v_b_3007_, v_a_3021_);
                            v___x_3023_ = 1usize;
                            v___x_3024_ = lean_usize_add(v_i_3006_, v___x_3023_);
                            v_i_3006_ = v___x_3024_;
                            v_b_3007_ = v___x_3022_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3007_);
                            v_a_3026_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3033_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3033_ == 0 {
                                v___x_3028_ = v___x_3020_;
                                v_isShared_3029_ = v_isSharedCheck_3033_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3026_);
                                crate::leanh::lean_dec(v___x_3020_);
                                v___x_3028_ = crate::leanh::lean_box(0);
                                v_isShared_3029_ = v_isSharedCheck_3033_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3007_);
                        v_a_3034_ = crate::leanh::lean_ctor_get(v___x_3016_, 0);
                        v_isSharedCheck_3041_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3016_)) as u8;
                        if v_isSharedCheck_3041_ == 0 {
                            v___x_3036_ = v___x_3016_;
                            v_isShared_3037_ = v_isSharedCheck_3041_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3034_);
                            crate::leanh::lean_dec(v___x_3016_);
                            v___x_3036_ = crate::leanh::lean_box(0);
                            v_isShared_3037_ = v_isSharedCheck_3041_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3029_ == 0 {
                    v___x_3031_ = v___x_3028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
                    v___x_3031_ = v_reuseFailAlloc_3032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3031_;
            }
            3 => {
                if v_isShared_3037_ == 0 {
                    v___x_3039_ = v___x_3036_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
                    v___x_3039_ = v_reuseFailAlloc_3040_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg___boxed(
    mut v_as_3042_: *mut crate::leanh::LeanObject,
    mut v_sz_3043_: *mut crate::leanh::LeanObject,
    mut v_i_3044_: *mut crate::leanh::LeanObject,
    mut v_b_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3050_: usize = 0;
    let mut v_i_boxed_3051_: usize = 0;
    let mut v_res_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3050_ = crate::leanh::lean_unbox_usize(v_sz_3043_);
    crate::leanh::lean_dec(v_sz_3043_);
    v_i_boxed_3051_ = crate::leanh::lean_unbox_usize(v_i_3044_);
    crate::leanh::lean_dec(v_i_3044_);
    v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_3042_, v_sz_boxed_3050_, v_i_boxed_3051_, v_b_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
    crate::leanh::lean_dec(v___y_3048_);
    crate::leanh::lean_dec_ref(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    crate::leanh::lean_dec_ref(v_as_3042_);
    return v_res_3052_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___lam__0(
    mut v_xs_3055_: *mut crate::leanh::LeanObject,
    mut v_x_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_argNames_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_argNames_3064_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
    v_sz_3065_ = lean_array_size(v_xs_3055_);
    v___x_3066_ = 0usize;
    v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_xs_3055_, v_sz_3065_, v___x_3066_, v_argNames_3064_, v___y_3059_, v___y_3061_, v___y_3062_);
    return v___x_3067_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed(
    mut v_xs_3068_: *mut crate::leanh::LeanObject,
    mut v_x_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0(
        v_xs_3068_,
        v_x_3069_,
        v___y_3070_,
        v___y_3071_,
        v___y_3072_,
        v___y_3073_,
        v___y_3074_,
        v___y_3075_,
    );
    crate::leanh::lean_dec(v___y_3075_);
    crate::leanh::lean_dec_ref(v___y_3074_);
    crate::leanh::lean_dec(v___y_3073_);
    crate::leanh::lean_dec_ref(v___y_3072_);
    crate::leanh::lean_dec(v___y_3071_);
    crate::leanh::lean_dec_ref(v___y_3070_);
    crate::leanh::lean_dec_ref(v_x_3069_);
    crate::leanh::lean_dec_ref(v_xs_3068_);
    return v_res_3077_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames(
    mut v_indVal_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_3087_ = crate::leanh::lean_ctor_get(v_indVal_3079_, 0);
    crate::leanh::lean_inc_ref(v_toConstantVal_3087_);
    crate::leanh::lean_dec_ref(v_indVal_3079_);
    v_type_3088_ = crate::leanh::lean_ctor_get(v_toConstantVal_3087_, 2);
    crate::leanh::lean_inc_ref(v_type_3088_);
    crate::leanh::lean_dec_ref(v_toConstantVal_3087_);
    v___f_3089_ = l_Lean_Elab_Deriving_mkInductArgNames___closed__0;
    v___x_3090_ = 0;
    v___x_3091_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_3088_, v___f_3089_, v___x_3090_, v___x_3090_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
    return v___x_3091_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___boxed(
    mut v_indVal_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Lean_Elab_Deriving_mkInductArgNames(
        v_indVal_3092_,
        v_a_3093_,
        v_a_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
    );
    crate::leanh::lean_dec(v_a_3098_);
    crate::leanh::lean_dec_ref(v_a_3097_);
    crate::leanh::lean_dec(v_a_3096_);
    crate::leanh::lean_dec_ref(v_a_3095_);
    crate::leanh::lean_dec(v_a_3094_);
    crate::leanh::lean_dec_ref(v_a_3093_);
    return v_res_3100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(
    mut v_as_3101_: *mut crate::leanh::LeanObject,
    mut v_sz_3102_: usize,
    mut v_i_3103_: usize,
    mut v_b_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_3101_, v_sz_3102_, v_i_3103_, v_b_3104_, v___y_3107_, v___y_3109_, v___y_3110_);
    return v___x_3112_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___boxed(
    mut v_as_3113_: *mut crate::leanh::LeanObject,
    mut v_sz_3114_: *mut crate::leanh::LeanObject,
    mut v_i_3115_: *mut crate::leanh::LeanObject,
    mut v_b_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3124_: usize = 0;
    let mut v_i_boxed_3125_: usize = 0;
    let mut v_res_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3124_ = crate::leanh::lean_unbox_usize(v_sz_3114_);
    crate::leanh::lean_dec(v_sz_3114_);
    v_i_boxed_3125_ = crate::leanh::lean_unbox_usize(v_i_3115_);
    crate::leanh::lean_dec(v_i_3115_);
    v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(v_as_3113_, v_sz_boxed_3124_, v_i_boxed_3125_, v_b_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
    crate::leanh::lean_dec(v___y_3122_);
    crate::leanh::lean_dec_ref(v___y_3121_);
    crate::leanh::lean_dec(v___y_3120_);
    crate::leanh::lean_dec_ref(v___y_3119_);
    crate::leanh::lean_dec(v___y_3118_);
    crate::leanh::lean_dec_ref(v___y_3117_);
    crate::leanh::lean_dec_ref(v_as_3113_);
    return v_res_3126_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(
    mut v_sz_3127_: usize,
    mut v_i_3128_: usize,
    mut v_bs_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: u8 = 0;
    let mut v_v_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: usize = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3130_ = lean_usize_dec_lt(v_i_3128_, v_sz_3127_);
                if v___x_3130_ == 0 {
                    return v_bs_3129_;
                } else {
                    v_v_3131_ = lean_array_uget(v_bs_3129_, v_i_3128_);
                    v___x_3132_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3133_ = lean_array_uset(v_bs_3129_, v_i_3128_, v___x_3132_);
                    v___x_3134_ = 1usize;
                    v___x_3135_ = lean_usize_add(v_i_3128_, v___x_3134_);
                    v___x_3136_ = lean_array_uset(v_bs_x27_3133_, v_i_3128_, v_v_3131_);
                    v_i_3128_ = v___x_3135_;
                    v_bs_3129_ = v___x_3136_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1___boxed(
    mut v_sz_3138_: *mut crate::leanh::LeanObject,
    mut v_i_3139_: *mut crate::leanh::LeanObject,
    mut v_bs_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3141_: usize = 0;
    let mut v_i_boxed_3142_: usize = 0;
    let mut v_res_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3141_ = crate::leanh::lean_unbox_usize(v_sz_3138_);
    crate::leanh::lean_dec(v_sz_3138_);
    v_i_boxed_3142_ = crate::leanh::lean_unbox_usize(v_i_3139_);
    crate::leanh::lean_dec(v_i_3139_);
    v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_boxed_3141_, v_i_boxed_3142_, v_bs_3140_);
    return v_res_3143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(
    mut v_sz_3144_: usize,
    mut v_i_3145_: usize,
    mut v_bs_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: u8 = 0;
    let mut v_v_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: usize = 0;
    let mut v___x_3153_: usize = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3147_ = lean_usize_dec_lt(v_i_3145_, v_sz_3144_);
                if v___x_3147_ == 0 {
                    return v_bs_3146_;
                } else {
                    v_v_3148_ = lean_array_uget(v_bs_3146_, v_i_3145_);
                    v___x_3149_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3150_ = lean_array_uset(v_bs_3146_, v_i_3145_, v___x_3149_);
                    v___x_3151_ = lean_mk_syntax_ident(v_v_3148_);
                    v___x_3152_ = 1usize;
                    v___x_3153_ = lean_usize_add(v_i_3145_, v___x_3152_);
                    v___x_3154_ = lean_array_uset(v_bs_x27_3150_, v_i_3145_, v___x_3151_);
                    v_i_3145_ = v___x_3153_;
                    v_bs_3146_ = v___x_3154_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0___boxed(
    mut v_sz_3156_: *mut crate::leanh::LeanObject,
    mut v_i_3157_: *mut crate::leanh::LeanObject,
    mut v_bs_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3159_: usize = 0;
    let mut v_i_boxed_3160_: usize = 0;
    let mut v_res_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3159_ = crate::leanh::lean_unbox_usize(v_sz_3156_);
    crate::leanh::lean_dec(v_sz_3156_);
    v_i_boxed_3160_ = crate::leanh::lean_unbox_usize(v_i_3157_);
    crate::leanh::lean_dec(v_i_3157_);
    v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_boxed_3159_, v_i_boxed_3160_, v_bs_3158_);
    return v_res_3161_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3181_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___redArg(
    mut v_indVal_3182_: *mut crate::leanh::LeanObject,
    mut v_argNames_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v_ref_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3192_: usize = 0;
    let mut v_f_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: usize = 0;
    let mut v_args_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3205_: usize = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_unused_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_3186_ = crate::leanh::lean_ctor_get(v_indVal_3182_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_3186_);
                crate::leanh::lean_dec_ref(v_indVal_3182_);
                v_name_3187_ = crate::leanh::lean_ctor_get(v_toConstantVal_3186_, 0);
                v_isSharedCheck_3213_ =
                    (!crate::leanh::lean_is_exclusive(v_toConstantVal_3186_)) as u8;
                if v_isSharedCheck_3213_ == 0 {
                    v_unused_3214_ = crate::leanh::lean_ctor_get(v_toConstantVal_3186_, 2);
                    crate::leanh::lean_dec(v_unused_3214_);
                    v_unused_3215_ = crate::leanh::lean_ctor_get(v_toConstantVal_3186_, 1);
                    crate::leanh::lean_dec(v_unused_3215_);
                    v___x_3189_ = v_toConstantVal_3186_;
                    v_isShared_3190_ = v_isSharedCheck_3213_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_3187_);
                    crate::leanh::lean_dec(v_toConstantVal_3186_);
                    v___x_3189_ = crate::leanh::lean_box(0);
                    v_isShared_3190_ = v_isSharedCheck_3213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_3191_ = crate::leanh::lean_ctor_get(v_a_3184_, 5);
                v_sz_3192_ = lean_array_size(v_argNames_3183_);
                v_f_3193_ = l_Lean_mkCIdent(v_name_3187_);
                v___x_3194_ = 0usize;
                v_args_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_3192_, v___x_3194_, v_argNames_3183_);
                v___x_3196_ = 0;
                v___x_3197_ = l_Lean_SourceInfo_fromRef(v_ref_3191_, v___x_3196_);
                v___x_3198_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                v___x_3199_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6;
                v___x_3200_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7;
                crate::leanh::lean_inc_n(v___x_3197_, 3);
                v___x_3201_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3201_, 0, v___x_3197_);
                crate::leanh::lean_ctor_set(v___x_3201_, 1, v___x_3200_);
                v___x_3202_ = l_Lean_Syntax_node2(v___x_3197_, v___x_3199_, v___x_3201_, v_f_3193_);
                v___x_3203_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                v___x_3204_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                );
                v_sz_3205_ = lean_array_size(v_args_3195_);
                v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_3205_, v___x_3194_, v_args_3195_);
                v___x_3207_ = l_Array_append___redArg(v___x_3204_, v___x_3206_);
                crate::leanh::lean_dec_ref(v___x_3206_);
                if v_isShared_3190_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3189_, 1);
                    crate::leanh::lean_ctor_set(v___x_3189_, 2, v___x_3207_);
                    crate::leanh::lean_ctor_set(v___x_3189_, 1, v___x_3203_);
                    crate::leanh::lean_ctor_set(v___x_3189_, 0, v___x_3197_);
                    v___x_3209_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 2, v___x_3207_);
                    v___x_3209_ = v_reuseFailAlloc_3212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3210_ =
                    l_Lean_Syntax_node2(v___x_3197_, v___x_3198_, v___x_3202_, v___x_3209_);
                v___x_3211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                return v___x_3211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___redArg___boxed(
    mut v_indVal_3216_: *mut crate::leanh::LeanObject,
    mut v_argNames_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3220_ =
        l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_3216_, v_argNames_3217_, v_a_3218_);
    crate::leanh::lean_dec_ref(v_a_3218_);
    return v_res_3220_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp(
    mut v_indVal_3221_: *mut crate::leanh::LeanObject,
    mut v_argNames_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
    mut v_a_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ =
        l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_3221_, v_argNames_3222_, v_a_3227_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___boxed(
    mut v_indVal_3231_: *mut crate::leanh::LeanObject,
    mut v_argNames_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Elab_Deriving_mkInductiveApp(
        v_indVal_3231_,
        v_argNames_3232_,
        v_a_3233_,
        v_a_3234_,
        v_a_3235_,
        v_a_3236_,
        v_a_3237_,
        v_a_3238_,
    );
    crate::leanh::lean_dec(v_a_3238_);
    crate::leanh::lean_dec_ref(v_a_3237_);
    crate::leanh::lean_dec(v_a_3236_);
    crate::leanh::lean_dec_ref(v_a_3235_);
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    return v_res_3240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(
    mut v_sz_3249_: usize,
    mut v_i_3250_: usize,
    mut v_bs_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: usize = 0;
    let mut v___x_3274_: usize = 0;
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3254_ = lean_usize_dec_lt(v_i_3250_, v_sz_3249_);
                if v___x_3254_ == 0 {
                    v___x_3255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v_bs_3251_);
                    return v___x_3255_;
                } else {
                    v_ref_3256_ = crate::leanh::lean_ctor_get(v___y_3252_, 5);
                    v_v_3257_ = lean_array_uget(v_bs_3251_, v_i_3250_);
                    v___x_3258_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3259_ = lean_array_uset(v_bs_3251_, v_i_3250_, v___x_3258_);
                    v___x_3260_ = 0;
                    v___x_3261_ = l_Lean_SourceInfo_fromRef(v_ref_3256_, v___x_3260_);
                    v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1;
                    v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2;
                    crate::leanh::lean_inc_n(v___x_3261_, 4);
                    v___x_3264_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3261_);
                    crate::leanh::lean_ctor_set(v___x_3264_, 1, v___x_3263_);
                    v___x_3265_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_3266_ = lean_mk_syntax_ident(v_v_3257_);
                    v___x_3267_ = l_Lean_Syntax_node1(v___x_3261_, v___x_3265_, v___x_3266_);
                    v___x_3268_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_3269_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3261_);
                    crate::leanh::lean_ctor_set(v___x_3269_, 1, v___x_3265_);
                    crate::leanh::lean_ctor_set(v___x_3269_, 2, v___x_3268_);
                    v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3;
                    v___x_3271_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3271_, 0, v___x_3261_);
                    crate::leanh::lean_ctor_set(v___x_3271_, 1, v___x_3270_);
                    v___x_3272_ = l_Lean_Syntax_node4(
                        v___x_3261_,
                        v___x_3262_,
                        v___x_3264_,
                        v___x_3267_,
                        v___x_3269_,
                        v___x_3271_,
                    );
                    v___x_3273_ = 1usize;
                    v___x_3274_ = lean_usize_add(v_i_3250_, v___x_3273_);
                    v___x_3275_ = lean_array_uset(v_bs_x27_3259_, v_i_3250_, v___x_3272_);
                    v_i_3250_ = v___x_3274_;
                    v_bs_3251_ = v___x_3275_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___boxed(
    mut v_sz_3277_: *mut crate::leanh::LeanObject,
    mut v_i_3278_: *mut crate::leanh::LeanObject,
    mut v_bs_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3282_: usize = 0;
    let mut v_i_boxed_3283_: usize = 0;
    let mut v_res_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3282_ = crate::leanh::lean_unbox_usize(v_sz_3277_);
    crate::leanh::lean_dec(v_sz_3277_);
    v_i_boxed_3283_ = crate::leanh::lean_unbox_usize(v_i_3278_);
    crate::leanh::lean_dec(v_i_3278_);
    v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_boxed_3282_, v_i_boxed_3283_, v_bs_3279_, v___y_3280_);
    crate::leanh::lean_dec_ref(v___y_3280_);
    return v_res_3284_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkImplicitBinders(
    mut v_argNames_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3293_: usize = 0;
    let mut v___x_3294_: usize = 0;
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_3293_ = lean_array_size(v_argNames_3285_);
    v___x_3294_ = 0usize;
    v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_3293_, v___x_3294_, v_argNames_3285_, v_a_3290_);
    return v___x_3295_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkImplicitBinders___boxed(
    mut v_argNames_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_Lean_Elab_Deriving_mkImplicitBinders(
        v_argNames_3296_,
        v_a_3297_,
        v_a_3298_,
        v_a_3299_,
        v_a_3300_,
        v_a_3301_,
        v_a_3302_,
    );
    crate::leanh::lean_dec(v_a_3302_);
    crate::leanh::lean_dec_ref(v_a_3301_);
    crate::leanh::lean_dec(v_a_3300_);
    crate::leanh::lean_dec_ref(v_a_3299_);
    crate::leanh::lean_dec(v_a_3298_);
    crate::leanh::lean_dec_ref(v_a_3297_);
    return v_res_3304_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(
    mut v_sz_3305_: usize,
    mut v_i_3306_: usize,
    mut v_bs_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_3305_, v_i_3306_, v_bs_3307_, v___y_3312_);
    return v___x_3315_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___boxed(
    mut v_sz_3316_: *mut crate::leanh::LeanObject,
    mut v_i_3317_: *mut crate::leanh::LeanObject,
    mut v_bs_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3326_: usize = 0;
    let mut v_i_boxed_3327_: usize = 0;
    let mut v_res_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3326_ = crate::leanh::lean_unbox_usize(v_sz_3316_);
    crate::leanh::lean_dec(v_sz_3316_);
    v_i_boxed_3327_ = crate::leanh::lean_unbox_usize(v_i_3317_);
    crate::leanh::lean_dec(v_i_3317_);
    v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(v_sz_boxed_3326_, v_i_boxed_3327_, v_bs_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
    crate::leanh::lean_dec(v___y_3324_);
    crate::leanh::lean_dec_ref(v___y_3323_);
    crate::leanh::lean_dec(v___y_3322_);
    crate::leanh::lean_dec_ref(v___y_3321_);
    crate::leanh::lean_dec(v___y_3320_);
    crate::leanh::lean_dec_ref(v___y_3319_);
    return v_res_3328_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(
    mut v_type_3329_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_3330_: *mut crate::leanh::LeanObject,
    mut v_k_3331_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3332_: u8,
    mut v_whnfType_3333_: u8,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3346_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3335_);
                crate::leanh::lean_inc_ref(v___y_3334_);
                v___f_3341_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_3341_, 0, v_k_3331_);
                crate::leanh::lean_closure_set(v___f_3341_, 1, v___y_3334_);
                crate::leanh::lean_closure_set(v___f_3341_, 2, v___y_3335_);
                v___x_3342_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_3329_,
                    v_maxFVars_x3f_3330_,
                    v___f_3341_,
                    v_cleanupAnnotations_3332_,
                    v_whnfType_3333_,
                    v___y_3336_,
                    v___y_3337_,
                    v___y_3338_,
                    v___y_3339_,
                );
                if crate::leanh::lean_obj_tag(v___x_3342_) == 0 {
                    return v___x_3342_;
                } else {
                    v_a_3343_ = crate::leanh::lean_ctor_get(v___x_3342_, 0);
                    v_isSharedCheck_3350_ = (!crate::leanh::lean_is_exclusive(v___x_3342_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3345_ = v___x_3342_;
                        v_isShared_3346_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3343_);
                        crate::leanh::lean_dec(v___x_3342_);
                        v___x_3345_ = crate::leanh::lean_box(0);
                        v_isShared_3346_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3346_ == 0 {
                    v___x_3348_ = v___x_3345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg___boxed(
    mut v_type_3351_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_3352_: *mut crate::leanh::LeanObject,
    mut v_k_3353_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3354_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3363_: u8 = 0;
    let mut v_whnfType_boxed_3364_: u8 = 0;
    let mut v_res_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3363_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3354_) as u8);
    v_whnfType_boxed_3364_ = (crate::leanh::lean_unbox(v_whnfType_3355_) as u8);
    v_res_3365_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3351_, v_maxFVars_x3f_3352_, v_k_3353_, v_cleanupAnnotations_boxed_3363_, v_whnfType_boxed_3364_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    crate::leanh::lean_dec(v___y_3361_);
    crate::leanh::lean_dec_ref(v___y_3360_);
    crate::leanh::lean_dec(v___y_3359_);
    crate::leanh::lean_dec_ref(v___y_3358_);
    crate::leanh::lean_dec(v___y_3357_);
    crate::leanh::lean_dec_ref(v___y_3356_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(
    mut v_00_u03b1_3366_: *mut crate::leanh::LeanObject,
    mut v_type_3367_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_3368_: *mut crate::leanh::LeanObject,
    mut v_k_3369_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3370_: u8,
    mut v_whnfType_3371_: u8,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3367_, v_maxFVars_x3f_3368_, v_k_3369_, v_cleanupAnnotations_3370_, v_whnfType_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___boxed(
    mut v_00_u03b1_3380_: *mut crate::leanh::LeanObject,
    mut v_type_3381_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_3382_: *mut crate::leanh::LeanObject,
    mut v_k_3383_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3384_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3393_: u8 = 0;
    let mut v_whnfType_boxed_3394_: u8 = 0;
    let mut v_res_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3393_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3384_) as u8);
    v_whnfType_boxed_3394_ = (crate::leanh::lean_unbox(v_whnfType_3385_) as u8);
    v_res_3395_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(v_00_u03b1_3380_, v_type_3381_, v_maxFVars_x3f_3382_, v_k_3383_, v_cleanupAnnotations_boxed_3393_, v_whnfType_boxed_3394_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec_ref(v___y_3390_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v___y_3388_);
    crate::leanh::lean_dec(v___y_3387_);
    crate::leanh::lean_dec_ref(v___y_3386_);
    return v_res_3395_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(
    mut v_upperBound_3404_: *mut crate::leanh::LeanObject,
    mut v_xs_3405_: *mut crate::leanh::LeanObject,
    mut v_className_3406_: *mut crate::leanh::LeanObject,
    mut v_argNames_3407_: *mut crate::leanh::LeanObject,
    mut v_a_3408_: *mut crate::leanh::LeanObject,
    mut v_b_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v_ref_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3428_ = lean_nat_dec_lt(v_a_3408_, v_upperBound_3404_);
                if v___x_3428_ == 0 {
                    crate::leanh::lean_dec(v_a_3408_);
                    crate::leanh::lean_dec(v_className_3406_);
                    v___x_3429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3429_, 0, v_b_3409_);
                    return v___x_3429_;
                } else {
                    v___x_3430_ = lean_array_fget_borrowed(v_xs_3405_, v_a_3408_);
                    v___x_3431_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3432_ = lean_mk_empty_array_with_capacity(v___x_3431_);
                    crate::leanh::lean_inc(v___x_3430_);
                    v___x_3433_ = lean_array_push(v___x_3432_, v___x_3430_);
                    crate::leanh::lean_inc(v_className_3406_);
                    v___x_3434_ = l_Lean_Meta_mkAppM(
                        v_className_3406_,
                        v___x_3433_,
                        v___y_3410_,
                        v___y_3411_,
                        v___y_3412_,
                        v___y_3413_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3434_) == 0 {
                        v_a_3435_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                        crate::leanh::lean_inc(v_a_3435_);
                        crate::leanh::lean_dec_ref_known(v___x_3434_, 1);
                        v___x_3436_ = l_Lean_Meta_isTypeCorrect(
                            v_a_3435_,
                            v___y_3410_,
                            v___y_3411_,
                            v___y_3412_,
                            v___y_3413_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3436_) == 0 {
                            v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                            crate::leanh::lean_inc(v_a_3437_);
                            crate::leanh::lean_dec_ref_known(v___x_3436_, 1);
                            v___x_3438_ = (crate::leanh::lean_unbox(v_a_3437_) as u8);
                            crate::leanh::lean_dec(v_a_3437_);
                            if v___x_3438_ == 0 {
                                v_snd_3416_ = v_b_3409_;
                                state = 1;
                                continue;
                            } else {
                                v_ref_3439_ = crate::leanh::lean_ctor_get(v___y_3412_, 5);
                                v___x_3440_ = crate::leanh::lean_box(0);
                                v___x_3441_ = lean_array_get_borrowed(
                                    v___x_3440_,
                                    v_argNames_3407_,
                                    v_a_3408_,
                                );
                                v___x_3442_ = 0;
                                v___x_3443_ = l_Lean_SourceInfo_fromRef(v_ref_3439_, v___x_3442_);
                                v___x_3444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1;
                                v___x_3445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2;
                                crate::leanh::lean_inc_n(v___x_3443_, 5);
                                v___x_3446_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3443_);
                                crate::leanh::lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                                v___x_3447_ =
                                    l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                v___x_3448_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once), _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
                                v___x_3449_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3443_);
                                crate::leanh::lean_ctor_set(v___x_3449_, 1, v___x_3447_);
                                crate::leanh::lean_ctor_set(v___x_3449_, 2, v___x_3448_);
                                v___x_3450_ =
                                    l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                crate::leanh::lean_inc(v_className_3406_);
                                v___x_3451_ = l_Lean_mkCIdent(v_className_3406_);
                                crate::leanh::lean_inc(v___x_3441_);
                                v___x_3452_ = lean_mk_syntax_ident(v___x_3441_);
                                v___x_3453_ =
                                    l_Lean_Syntax_node1(v___x_3443_, v___x_3447_, v___x_3452_);
                                v___x_3454_ = l_Lean_Syntax_node2(
                                    v___x_3443_,
                                    v___x_3450_,
                                    v___x_3451_,
                                    v___x_3453_,
                                );
                                v___x_3455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3;
                                v___x_3456_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3443_);
                                crate::leanh::lean_ctor_set(v___x_3456_, 1, v___x_3455_);
                                v___x_3457_ = l_Lean_Syntax_node4(
                                    v___x_3443_,
                                    v___x_3444_,
                                    v___x_3446_,
                                    v___x_3449_,
                                    v___x_3454_,
                                    v___x_3456_,
                                );
                                v___x_3458_ = lean_array_push(v_b_3409_, v___x_3457_);
                                v_snd_3416_ = v___x_3458_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3459_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                            crate::leanh::lean_inc(v_a_3459_);
                            crate::leanh::lean_dec_ref_known(v___x_3436_, 1);
                            v_a_3425_ = v_a_3459_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3460_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                        crate::leanh::lean_inc(v_a_3460_);
                        crate::leanh::lean_dec_ref_known(v___x_3434_, 1);
                        v_a_3425_ = v_a_3460_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3417_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3418_ = lean_nat_add(v_a_3408_, v___x_3417_);
                crate::leanh::lean_dec(v_a_3408_);
                v_a_3408_ = v___x_3418_;
                v_b_3409_ = v_snd_3416_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3422_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3421_);
                    v_snd_3416_ = v_b_3409_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3409_);
                    crate::leanh::lean_dec(v_a_3408_);
                    crate::leanh::lean_dec(v_className_3406_);
                    v___x_3423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3423_, 0, v___y_3421_);
                    return v___x_3423_;
                }
            }
            3 => {
                v___x_3426_ = l_Lean_Exception_isInterrupt(v_a_3425_);
                if v___x_3426_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3425_);
                    v___x_3427_ = l_Lean_Exception_isRuntime(v_a_3425_);
                    v___y_3421_ = v_a_3425_;
                    v___y_3422_ = v___x_3427_;
                    state = 2;
                    continue;
                } else {
                    v___y_3421_ = v_a_3425_;
                    v___y_3422_ = v___x_3426_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___boxed(
    mut v_upperBound_3461_: *mut crate::leanh::LeanObject,
    mut v_xs_3462_: *mut crate::leanh::LeanObject,
    mut v_className_3463_: *mut crate::leanh::LeanObject,
    mut v_argNames_3464_: *mut crate::leanh::LeanObject,
    mut v_a_3465_: *mut crate::leanh::LeanObject,
    mut v_b_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3472_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_3461_, v_xs_3462_, v_className_3463_, v_argNames_3464_, v_a_3465_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
    crate::leanh::lean_dec(v___y_3470_);
    crate::leanh::lean_dec_ref(v___y_3469_);
    crate::leanh::lean_dec(v___y_3468_);
    crate::leanh::lean_dec_ref(v___y_3467_);
    crate::leanh::lean_dec_ref(v_argNames_3464_);
    crate::leanh::lean_dec_ref(v_xs_3462_);
    crate::leanh::lean_dec(v_upperBound_3461_);
    return v_res_3472_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(
    mut v_className_3475_: *mut crate::leanh::LeanObject,
    mut v_argNames_3476_: *mut crate::leanh::LeanObject,
    mut v_xs_3477_: *mut crate::leanh::LeanObject,
    mut v_x_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_array_get_size(v_xs_3477_);
    v___x_3487_ = crate::leanh::lean_unsigned_to_nat(0);
    v_binders_3488_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
    v___x_3489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v___x_3486_, v_xs_3477_, v_className_3475_, v_argNames_3476_, v___x_3487_, v_binders_3488_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    return v___x_3489_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(
    mut v_className_3490_: *mut crate::leanh::LeanObject,
    mut v_argNames_3491_: *mut crate::leanh::LeanObject,
    mut v_xs_3492_: *mut crate::leanh::LeanObject,
    mut v_x_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(
        v_className_3490_,
        v_argNames_3491_,
        v_xs_3492_,
        v_x_3493_,
        v___y_3494_,
        v___y_3495_,
        v___y_3496_,
        v___y_3497_,
        v___y_3498_,
        v___y_3499_,
    );
    crate::leanh::lean_dec(v___y_3499_);
    crate::leanh::lean_dec_ref(v___y_3498_);
    crate::leanh::lean_dec(v___y_3497_);
    crate::leanh::lean_dec_ref(v___y_3496_);
    crate::leanh::lean_dec(v___y_3495_);
    crate::leanh::lean_dec_ref(v___y_3494_);
    crate::leanh::lean_dec_ref(v_x_3493_);
    crate::leanh::lean_dec_ref(v_xs_3492_);
    crate::leanh::lean_dec_ref(v_argNames_3491_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders(
    mut v_className_3502_: *mut crate::leanh::LeanObject,
    mut v_indVal_3503_: *mut crate::leanh::LeanObject,
    mut v_argNames_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
    mut v_a_3509_: *mut crate::leanh::LeanObject,
    mut v_a_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_3512_ = crate::leanh::lean_ctor_get(v_indVal_3503_, 0);
    crate::leanh::lean_inc_ref(v_toConstantVal_3512_);
    v_numParams_3513_ = crate::leanh::lean_ctor_get(v_indVal_3503_, 1);
    crate::leanh::lean_inc(v_numParams_3513_);
    crate::leanh::lean_dec_ref(v_indVal_3503_);
    v_type_3514_ = crate::leanh::lean_ctor_get(v_toConstantVal_3512_, 2);
    crate::leanh::lean_inc_ref(v_type_3514_);
    crate::leanh::lean_dec_ref(v_toConstantVal_3512_);
    v___f_3515_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3515_, 0, v_className_3502_);
    crate::leanh::lean_closure_set(v___f_3515_, 1, v_argNames_3504_);
    v___x_3516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3516_, 0, v_numParams_3513_);
    v___x_3517_ = 0;
    v___x_3518_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3514_, v___x_3516_, v___f_3515_, v___x_3517_, v___x_3517_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(
    mut v_className_3519_: *mut crate::leanh::LeanObject,
    mut v_indVal_3520_: *mut crate::leanh::LeanObject,
    mut v_argNames_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3529_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
        v_className_3519_,
        v_indVal_3520_,
        v_argNames_3521_,
        v_a_3522_,
        v_a_3523_,
        v_a_3524_,
        v_a_3525_,
        v_a_3526_,
        v_a_3527_,
    );
    crate::leanh::lean_dec(v_a_3527_);
    crate::leanh::lean_dec_ref(v_a_3526_);
    crate::leanh::lean_dec(v_a_3525_);
    crate::leanh::lean_dec_ref(v_a_3524_);
    crate::leanh::lean_dec(v_a_3523_);
    crate::leanh::lean_dec_ref(v_a_3522_);
    return v_res_3529_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(
    mut v_upperBound_3530_: *mut crate::leanh::LeanObject,
    mut v_xs_3531_: *mut crate::leanh::LeanObject,
    mut v_className_3532_: *mut crate::leanh::LeanObject,
    mut v_argNames_3533_: *mut crate::leanh::LeanObject,
    mut v_inst_3534_: *mut crate::leanh::LeanObject,
    mut v_R_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_b_3537_: *mut crate::leanh::LeanObject,
    mut v_c_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
    mut v___y_3542_: *mut crate::leanh::LeanObject,
    mut v___y_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_3530_, v_xs_3531_, v_className_3532_, v_argNames_3533_, v_a_3536_, v_b_3537_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
    return v___x_3546_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(
    mut v_upperBound_3547_: *mut crate::leanh::LeanObject,
    mut v_xs_3548_: *mut crate::leanh::LeanObject,
    mut v_className_3549_: *mut crate::leanh::LeanObject,
    mut v_argNames_3550_: *mut crate::leanh::LeanObject,
    mut v_inst_3551_: *mut crate::leanh::LeanObject,
    mut v_R_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_b_3554_: *mut crate::leanh::LeanObject,
    mut v_c_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3563_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(
            v_upperBound_3547_,
            v_xs_3548_,
            v_className_3549_,
            v_argNames_3550_,
            v_inst_3551_,
            v_R_3552_,
            v_a_3553_,
            v_b_3554_,
            v_c_3555_,
            v___y_3556_,
            v___y_3557_,
            v___y_3558_,
            v___y_3559_,
            v___y_3560_,
            v___y_3561_,
        );
    crate::leanh::lean_dec(v___y_3561_);
    crate::leanh::lean_dec_ref(v___y_3560_);
    crate::leanh::lean_dec(v___y_3559_);
    crate::leanh::lean_dec_ref(v___y_3558_);
    crate::leanh::lean_dec(v___y_3557_);
    crate::leanh::lean_dec_ref(v___y_3556_);
    crate::leanh::lean_dec_ref(v_argNames_3550_);
    crate::leanh::lean_dec_ref(v_xs_3548_);
    crate::leanh::lean_dec(v_upperBound_3547_);
    return v_res_3563_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
    mut v___x_3586_: u8,
    mut v_a_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___y_3596_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: u8 = 0;
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: u8 = 0;
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3587_) == 0 {
                    v___x_3589_ = l_List_reverse___redArg(v_a_3588_);
                    return v___x_3589_;
                } else {
                    v_head_3590_ = crate::leanh::lean_ctor_get(v_a_3587_, 0);
                    v_tail_3591_ = crate::leanh::lean_ctor_get(v_a_3587_, 1);
                    v_isSharedCheck_3620_ = (!crate::leanh::lean_is_exclusive(v_a_3587_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3593_ = v_a_3587_;
                        v_isShared_3594_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3591_);
                        crate::leanh::lean_inc(v_head_3590_);
                        crate::leanh::lean_dec(v_a_3587_);
                        v___x_3593_ = crate::leanh::lean_box(0);
                        v_isShared_3594_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3602_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1;
                crate::leanh::lean_inc(v_head_3590_);
                v___x_3603_ = l_Lean_Syntax_isOfKind(v_head_3590_, v___x_3602_);
                if v___x_3603_ == 0 {
                    v___y_3596_ = v___x_3586_;
                    state = 2;
                    continue;
                } else {
                    v___x_3604_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3605_ = l_Lean_Syntax_getArg(v_head_3590_, v___x_3604_);
                    v___x_3606_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3;
                    crate::leanh::lean_inc(v___x_3605_);
                    v___x_3607_ = l_Lean_Syntax_isOfKind(v___x_3605_, v___x_3606_);
                    if v___x_3607_ == 0 {
                        crate::leanh::lean_dec(v___x_3605_);
                        v___y_3596_ = v___x_3586_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3608_ = l_Lean_Syntax_getArg(v___x_3605_, v___x_3604_);
                        crate::leanh::lean_dec(v___x_3605_);
                        v___x_3609_ = l_Lean_Syntax_matchesNull(v___x_3608_, v___x_3604_);
                        if v___x_3609_ == 0 {
                            v___y_3596_ = v___x_3607_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3610_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3611_ = l_Lean_Syntax_getArg(v_head_3590_, v___x_3610_);
                            v___x_3612_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6;
                            crate::leanh::lean_inc(v___x_3611_);
                            v___x_3613_ = l_Lean_Syntax_isOfKind(v___x_3611_, v___x_3612_);
                            if v___x_3613_ == 0 {
                                crate::leanh::lean_dec(v___x_3611_);
                                v___y_3596_ = v___x_3609_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3614_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3604_);
                                v___x_3615_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8;
                                v___x_3616_ = l_Lean_Syntax_matchesIdent(v___x_3614_, v___x_3615_);
                                crate::leanh::lean_dec(v___x_3614_);
                                if v___x_3616_ == 0 {
                                    crate::leanh::lean_dec(v___x_3611_);
                                    v___y_3596_ = v___x_3613_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3617_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3610_);
                                    crate::leanh::lean_dec(v___x_3611_);
                                    v___x_3618_ =
                                        l_Lean_Syntax_matchesNull(v___x_3617_, v___x_3604_);
                                    if v___x_3618_ == 0 {
                                        v___y_3596_ = v___x_3616_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_3593_);
                                        crate::leanh::lean_dec(v_head_3590_);
                                        v_a_3587_ = v_tail_3591_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                if v___y_3596_ == 0 {
                    crate::leanh::lean_del_object(v___x_3593_);
                    crate::leanh::lean_dec(v_head_3590_);
                    v_a_3587_ = v_tail_3591_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_3594_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3593_, 1, v_a_3588_);
                        v___x_3599_ = v___x_3593_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_head_3590_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_a_3588_);
                        v___x_3599_ = v_reuseFailAlloc_3601_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_a_3587_ = v_tail_3591_;
                v_a_3588_ = v___x_3599_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___boxed(
    mut v___x_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5393__boxed_3624_: u8 = 0;
    let mut v_res_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5393__boxed_3624_ = (crate::leanh::lean_unbox(v___x_3621_) as u8);
    v_res_3625_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
        v___x_5393__boxed_3624_,
        v_a_3622_,
        v_a_3623_,
    );
    return v_res_3625_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(
    mut v___x_3626_: u8,
    mut v_sc_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_header_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varDecls_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varUIds_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_includedVars_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_3637_: u8 = 0;
    let mut v_isPublic_3638_: u8 = 0;
    let mut v_isMeta_3639_: u8 = 0;
    let mut v_attrs_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_3628_ = crate::leanh::lean_ctor_get(v_sc_3627_, 0);
                v_opts_3629_ = crate::leanh::lean_ctor_get(v_sc_3627_, 1);
                v_currNamespace_3630_ = crate::leanh::lean_ctor_get(v_sc_3627_, 2);
                v_openDecls_3631_ = crate::leanh::lean_ctor_get(v_sc_3627_, 3);
                v_levelNames_3632_ = crate::leanh::lean_ctor_get(v_sc_3627_, 4);
                v_varDecls_3633_ = crate::leanh::lean_ctor_get(v_sc_3627_, 5);
                v_varUIds_3634_ = crate::leanh::lean_ctor_get(v_sc_3627_, 6);
                v_includedVars_3635_ = crate::leanh::lean_ctor_get(v_sc_3627_, 7);
                v_omittedVars_3636_ = crate::leanh::lean_ctor_get(v_sc_3627_, 8);
                v_isNoncomputable_3637_ = crate::leanh::lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isPublic_3638_ = crate::leanh::lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_3639_ = crate::leanh::lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_3640_ = crate::leanh::lean_ctor_get(v_sc_3627_, 9);
                v_isSharedCheck_3649_ = (!crate::leanh::lean_is_exclusive(v_sc_3627_)) as u8;
                if v_isSharedCheck_3649_ == 0 {
                    v___x_3642_ = v_sc_3627_;
                    v_isShared_3643_ = v_isSharedCheck_3649_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_attrs_3640_);
                    crate::leanh::lean_inc(v_omittedVars_3636_);
                    crate::leanh::lean_inc(v_includedVars_3635_);
                    crate::leanh::lean_inc(v_varUIds_3634_);
                    crate::leanh::lean_inc(v_varDecls_3633_);
                    crate::leanh::lean_inc(v_levelNames_3632_);
                    crate::leanh::lean_inc(v_openDecls_3631_);
                    crate::leanh::lean_inc(v_currNamespace_3630_);
                    crate::leanh::lean_inc(v_opts_3629_);
                    crate::leanh::lean_inc(v_header_3628_);
                    crate::leanh::lean_dec(v_sc_3627_);
                    v___x_3642_ = crate::leanh::lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3644_ = crate::leanh::lean_box(0);
                v___x_3645_ =
                    l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
                        v___x_3626_,
                        v_attrs_3640_,
                        v___x_3644_,
                    );
                if v_isShared_3643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3642_, 9, v___x_3645_);
                    v___x_3647_ = v___x_3642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = crate::leanh::lean_alloc_ctor(0, 10, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_header_3628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_opts_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_currNamespace_3630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_openDecls_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_levelNames_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 5, v_varDecls_3633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 6, v_varUIds_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 7, v_includedVars_3635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 8, v_omittedVars_3636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 9, v___x_3645_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_isNoncomputable_3637_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 1) as u32,
                        v_isPublic_3638_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 2) as u32,
                        v_isMeta_3639_,
                    );
                    v___x_3647_ = v_reuseFailAlloc_3648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed(
    mut v___x_3650_: *mut crate::leanh::LeanObject,
    mut v_sc_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5488__boxed_3652_: u8 = 0;
    let mut v_res_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5488__boxed_3652_ = (crate::leanh::lean_unbox(v___x_3650_) as u8);
    v_res_3653_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(
        v___x_5488__boxed_3652_,
        v_sc_3651_,
    );
    return v_res_3653_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3654_ = crate::leanh::lean_box(1);
    v___x_3655_ = l_Lean_MessageData_ofFormat(v___x_3654_);
    return v___x_3655_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2;
    v___x_3660_ = l_Lean_MessageData_ofFormat(v___x_3659_);
    return v___x_3660_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(
    mut v_x_3661_: *mut crate::leanh::LeanObject,
    mut v_x_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v_before_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3662_) == 0 {
                    return v_x_3661_;
                } else {
                    v_head_3663_ = crate::leanh::lean_ctor_get(v_x_3662_, 0);
                    v_tail_3664_ = crate::leanh::lean_ctor_get(v_x_3662_, 1);
                    v_isSharedCheck_3686_ = (!crate::leanh::lean_is_exclusive(v_x_3662_)) as u8;
                    if v_isSharedCheck_3686_ == 0 {
                        v___x_3666_ = v_x_3662_;
                        v_isShared_3667_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3664_);
                        crate::leanh::lean_inc(v_head_3663_);
                        crate::leanh::lean_dec(v_x_3662_);
                        v___x_3666_ = crate::leanh::lean_box(0);
                        v_isShared_3667_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3668_ = crate::leanh::lean_ctor_get(v_head_3663_, 0);
                v_isSharedCheck_3684_ = (!crate::leanh::lean_is_exclusive(v_head_3663_)) as u8;
                if v_isSharedCheck_3684_ == 0 {
                    v_unused_3685_ = crate::leanh::lean_ctor_get(v_head_3663_, 1);
                    crate::leanh::lean_dec(v_unused_3685_);
                    v___x_3670_ = v_head_3663_;
                    v_isShared_3671_ = v_isSharedCheck_3684_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3668_);
                    crate::leanh::lean_dec(v_head_3663_);
                    v___x_3670_ = crate::leanh::lean_box(0);
                    v_isShared_3671_ = v_isSharedCheck_3684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3672_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3671_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3670_, 7);
                    crate::leanh::lean_ctor_set(v___x_3670_, 1, v___x_3672_);
                    crate::leanh::lean_ctor_set(v___x_3670_, 0, v_x_3661_);
                    v___x_3674_ = v___x_3670_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_x_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___x_3672_);
                    v___x_3674_ = v_reuseFailAlloc_3683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3);
                if v_isShared_3667_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3666_, 7);
                    crate::leanh::lean_ctor_set(v___x_3666_, 1, v___x_3675_);
                    crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3674_);
                    v___x_3677_ = v___x_3666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3675_);
                    v___x_3677_ = v_reuseFailAlloc_3682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3678_ = l_Lean_MessageData_ofSyntax(v_before_3668_);
                v___x_3679_ = l_Lean_indentD(v___x_3678_);
                v___x_3680_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3680_, 0, v___x_3677_);
                crate::leanh::lean_ctor_set(v___x_3680_, 1, v___x_3679_);
                v_x_3661_ = v___x_3680_;
                v_x_3662_ = v_tail_3664_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(
    mut v_opts_3687_: *mut crate::leanh::LeanObject,
    mut v_opt_3688_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3689_ = crate::leanh::lean_ctor_get(v_opt_3688_, 0);
    v_defValue_3690_ = crate::leanh::lean_ctor_get(v_opt_3688_, 1);
    v_map_3691_ = crate::leanh::lean_ctor_get(v_opts_3687_, 0);
    v___x_3692_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3691_,
            v_name_3689_,
        );
    if crate::leanh::lean_obj_tag(v___x_3692_) == 0 {
        let mut v___x_3693_: u8 = 0;
        v___x_3693_ = (crate::leanh::lean_unbox(v_defValue_3690_) as u8);
        return v___x_3693_;
    } else {
        let mut v_val_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3694_ = crate::leanh::lean_ctor_get(v___x_3692_, 0);
        crate::leanh::lean_inc(v_val_3694_);
        crate::leanh::lean_dec_ref_known(v___x_3692_, 1);
        if crate::leanh::lean_obj_tag(v_val_3694_) == 1 {
            let mut v_v_3695_: u8 = 0;
            v_v_3695_ = crate::leanh::lean_ctor_get_uint8(v_val_3694_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3694_, 0);
            return v_v_3695_;
        } else {
            let mut v___x_3696_: u8 = 0;
            crate::leanh::lean_dec(v_val_3694_);
            v___x_3696_ = (crate::leanh::lean_unbox(v_defValue_3690_) as u8);
            return v___x_3696_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(
    mut v_opts_3697_: *mut crate::leanh::LeanObject,
    mut v_opt_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3699_: u8 = 0;
    let mut v_r_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_3697_, v_opt_3698_);
    crate::leanh::lean_dec_ref(v_opt_3698_);
    crate::leanh::lean_dec_ref(v_opts_3697_);
    v_r_3700_ = crate::leanh::lean_box((v_res_3699_) as usize);
    return v_r_3700_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3704_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1;
    v___x_3705_ = l_Lean_MessageData_ofFormat(v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(
    mut v_msgData_3706_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3710_ = lean_st_ref_get(v___y_3708_);
                v_scopes_3711_ = crate::leanh::lean_ctor_get(v___x_3710_, 2);
                crate::leanh::lean_inc(v_scopes_3711_);
                crate::leanh::lean_dec(v___x_3710_);
                v___x_3712_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3713_ = l_List_head_x21___redArg(v___x_3712_, v_scopes_3711_);
                crate::leanh::lean_dec(v_scopes_3711_);
                v_opts_3714_ = crate::leanh::lean_ctor_get(v___x_3713_, 1);
                crate::leanh::lean_inc_ref(v_opts_3714_);
                crate::leanh::lean_dec(v___x_3713_);
                v___x_3715_ = l_Lean_Elab_pp_macroStack;
                v___x_3716_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_3714_, v___x_3715_);
                crate::leanh::lean_dec_ref(v_opts_3714_);
                if v___x_3716_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3707_);
                    v___x_3717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_msgData_3706_);
                    return v___x_3717_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3707_) == 0 {
                        v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3718_, 0, v_msgData_3706_);
                        return v___x_3718_;
                    } else {
                        v_head_3719_ = crate::leanh::lean_ctor_get(v_macroStack_3707_, 0);
                        crate::leanh::lean_inc(v_head_3719_);
                        v_after_3720_ = crate::leanh::lean_ctor_get(v_head_3719_, 1);
                        v_isSharedCheck_3735_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3719_)) as u8;
                        if v_isSharedCheck_3735_ == 0 {
                            v_unused_3736_ = crate::leanh::lean_ctor_get(v_head_3719_, 0);
                            crate::leanh::lean_dec(v_unused_3736_);
                            v___x_3722_ = v_head_3719_;
                            v_isShared_3723_ = v_isSharedCheck_3735_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3720_);
                            crate::leanh::lean_dec(v_head_3719_);
                            v___x_3722_ = crate::leanh::lean_box(0);
                            v_isShared_3723_ = v_isSharedCheck_3735_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3724_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3723_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3722_, 7);
                    crate::leanh::lean_ctor_set(v___x_3722_, 1, v___x_3724_);
                    crate::leanh::lean_ctor_set(v___x_3722_, 0, v_msgData_3706_);
                    v___x_3726_ = v___x_3722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_msgData_3706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3724_);
                    v___x_3726_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3727_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
                v___x_3728_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3728_, 0, v___x_3726_);
                crate::leanh::lean_ctor_set(v___x_3728_, 1, v___x_3727_);
                v___x_3729_ = l_Lean_MessageData_ofSyntax(v_after_3720_);
                v___x_3730_ = l_Lean_indentD(v___x_3729_);
                v_msgData_3731_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3731_, 0, v___x_3728_);
                crate::leanh::lean_ctor_set(v_msgData_3731_, 1, v___x_3730_);
                v___x_3732_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_3731_, v_macroStack_3707_);
                v___x_3733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3733_, 0, v___x_3732_);
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(
    mut v_msgData_3737_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_3737_, v_macroStack_3738_, v___y_3739_);
    crate::leanh::lean_dec(v___y_3739_);
    return v_res_3741_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0);
    v___x_3744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3744_, 0, v___x_3743_);
    return v___x_3744_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
    v___x_3746_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3747_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3747_, 0, v___x_3746_);
    crate::leanh::lean_ctor_set(v___x_3747_, 1, v___x_3746_);
    crate::leanh::lean_ctor_set(v___x_3747_, 2, v___x_3746_);
    crate::leanh::lean_ctor_set(v___x_3747_, 3, v___x_3746_);
    crate::leanh::lean_ctor_set(v___x_3747_, 4, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3747_, 5, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3747_, 6, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3747_, 7, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3747_, 8, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3747_, 9, v___x_3745_);
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3749_ = lean_mk_empty_array_with_capacity(v___x_3748_);
    v___x_3750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3750_, 0, v___x_3749_);
    return v___x_3750_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: usize = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = 5usize;
    v___x_3752_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3753_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
    v___x_3755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3);
    v___x_3756_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3755_);
    crate::leanh::lean_ctor_set(v___x_3756_, 1, v___x_3754_);
    crate::leanh::lean_ctor_set(v___x_3756_, 2, v___x_3752_);
    crate::leanh::lean_ctor_set(v___x_3756_, 3, v___x_3752_);
    crate::leanh::lean_ctor_set_usize(v___x_3756_, 4, v___x_3751_);
    return v___x_3756_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = crate::leanh::lean_box(1);
    v___x_3758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4);
    v___x_3759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
    v___x_3760_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
    crate::leanh::lean_ctor_set(v___x_3760_, 1, v___x_3758_);
    crate::leanh::lean_ctor_set(v___x_3760_, 2, v___x_3757_);
    return v___x_3760_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(
    mut v_msgData_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3764_ = lean_st_ref_get(v___y_3762_);
    v_env_3765_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
    crate::leanh::lean_inc_ref(v_env_3765_);
    crate::leanh::lean_dec(v___x_3764_);
    v___x_3766_ = lean_st_ref_get(v___y_3762_);
    v_scopes_3767_ = crate::leanh::lean_ctor_get(v___x_3766_, 2);
    crate::leanh::lean_inc(v_scopes_3767_);
    crate::leanh::lean_dec(v___x_3766_);
    v___x_3768_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3769_ = l_List_head_x21___redArg(v___x_3768_, v_scopes_3767_);
    crate::leanh::lean_dec(v_scopes_3767_);
    v_opts_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 1);
    crate::leanh::lean_inc_ref(v_opts_3770_);
    crate::leanh::lean_dec(v___x_3769_);
    v___x_3771_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
    v___x_3772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
    v___x_3773_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3773_, 0, v_env_3765_);
    crate::leanh::lean_ctor_set(v___x_3773_, 1, v___x_3771_);
    crate::leanh::lean_ctor_set(v___x_3773_, 2, v___x_3772_);
    crate::leanh::lean_ctor_set(v___x_3773_, 3, v_opts_3770_);
    v___x_3774_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3774_, 0, v___x_3773_);
    crate::leanh::lean_ctor_set(v___x_3774_, 1, v_msgData_3761_);
    v___x_3775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3775_, 0, v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(
    mut v_msgData_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3779_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_3776_, v___y_3777_);
    crate::leanh::lean_dec(v___y_3777_);
    return v_res_3779_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
    mut v_msg_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_a_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3784_ = l_Lean_Elab_Command_getRef___redArg(v___y_3781_);
                if crate::leanh::lean_obj_tag(v___x_3784_) == 0 {
                    v_a_3785_ = crate::leanh::lean_ctor_get(v___x_3784_, 0);
                    crate::leanh::lean_inc(v_a_3785_);
                    crate::leanh::lean_dec_ref_known(v___x_3784_, 1);
                    v_macroStack_3786_ = crate::leanh::lean_ctor_get(v___y_3781_, 4);
                    v___x_3787_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msg_3780_, v___y_3782_);
                    v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3787_, 0);
                    crate::leanh::lean_inc(v_a_3788_);
                    crate::leanh::lean_dec_ref(v___x_3787_);
                    v___x_3789_ = l_Lean_Elab_getBetterRef(v_a_3785_, v_macroStack_3786_);
                    crate::leanh::lean_dec(v_a_3785_);
                    crate::leanh::lean_inc(v_macroStack_3786_);
                    v___x_3790_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_a_3788_, v_macroStack_3786_, v___y_3782_);
                    v_a_3791_ = crate::leanh::lean_ctor_get(v___x_3790_, 0);
                    v_isSharedCheck_3799_ = (!crate::leanh::lean_is_exclusive(v___x_3790_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3793_ = v___x_3790_;
                        v_isShared_3794_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3791_);
                        crate::leanh::lean_dec(v___x_3790_);
                        v___x_3793_ = crate::leanh::lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_3780_);
                    v_a_3800_ = crate::leanh::lean_ctor_get(v___x_3784_, 0);
                    v_isSharedCheck_3807_ = (!crate::leanh::lean_is_exclusive(v___x_3784_)) as u8;
                    if v_isSharedCheck_3807_ == 0 {
                        v___x_3802_ = v___x_3784_;
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3800_);
                        crate::leanh::lean_dec(v___x_3784_);
                        v___x_3802_ = crate::leanh::lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3795_, 0, v___x_3789_);
                crate::leanh::lean_ctor_set(v___x_3795_, 1, v_a_3791_);
                if v_isShared_3794_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3793_, 1);
                    crate::leanh::lean_ctor_set(v___x_3793_, 0, v___x_3795_);
                    v___x_3797_ = v___x_3793_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
                    v___x_3797_ = v_reuseFailAlloc_3798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3797_;
            }
            3 => {
                if v_isShared_3803_ == 0 {
                    v___x_3805_ = v___x_3802_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
                    v___x_3805_ = v_reuseFailAlloc_3806_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg___boxed(
    mut v_msg_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3812_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
            v_msg_3808_,
            v___y_3809_,
            v___y_3810_,
        );
    crate::leanh::lean_dec(v___y_3810_);
    crate::leanh::lean_dec_ref(v___y_3809_);
    return v_res_3812_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0;
    v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2;
    v___x_3818_ = l_Lean_stringToMessageData(v___x_3817_);
    return v___x_3818_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(
    mut v_constName_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3823_ = lean_st_ref_get(v___y_3821_);
                v_env_3824_ = crate::leanh::lean_ctor_get(v___x_3823_, 0);
                crate::leanh::lean_inc_ref(v_env_3824_);
                crate::leanh::lean_dec(v___x_3823_);
                crate::leanh::lean_inc(v_constName_3819_);
                v___x_3825_ = l_Lean_isInductiveCore_x3f(v_env_3824_, v_constName_3819_);
                if crate::leanh::lean_obj_tag(v___x_3825_) == 0 {
                    v___x_3826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
                    v___x_3827_ = 0;
                    v___x_3828_ = l_Lean_MessageData_ofConstName(v_constName_3819_, v___x_3827_);
                    v___x_3829_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3826_);
                    crate::leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
                    v___x_3830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
                    v___x_3831_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3831_, 0, v___x_3829_);
                    crate::leanh::lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                    v___x_3832_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_3831_, v___y_3820_, v___y_3821_);
                    return v___x_3832_;
                } else {
                    crate::leanh::lean_dec(v_constName_3819_);
                    v_val_3833_ = crate::leanh::lean_ctor_get(v___x_3825_, 0);
                    v_isSharedCheck_3840_ = (!crate::leanh::lean_is_exclusive(v___x_3825_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3825_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3833_);
                        crate::leanh::lean_dec(v___x_3825_);
                        v___x_3835_ = crate::leanh::lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3836_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3835_, 0);
                    v___x_3838_ = v___x_3835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_val_3833_);
                    v___x_3838_ = v_reuseFailAlloc_3839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___boxed(
    mut v_constName_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3845_ =
        l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(
            v_constName_3841_,
            v___y_3842_,
            v___y_3843_,
        );
    crate::leanh::lean_dec(v___y_3843_);
    crate::leanh::lean_dec_ref(v___y_3842_);
    return v_res_3845_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(
    mut v_as_x27_3846_: *mut crate::leanh::LeanObject,
    mut v_b_3847_: *mut crate::leanh::LeanObject,
    mut v___y_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3846_) == 0 {
                    v___x_3851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3851_, 0, v_b_3847_);
                    return v___x_3851_;
                } else {
                    v_head_3852_ = crate::leanh::lean_ctor_get(v_as_x27_3846_, 0);
                    v_tail_3853_ = crate::leanh::lean_ctor_get(v_as_x27_3846_, 1);
                    crate::leanh::lean_inc(v_head_3852_);
                    v___x_3854_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_head_3852_, v___y_3848_, v___y_3849_);
                    if crate::leanh::lean_obj_tag(v___x_3854_) == 0 {
                        v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                        crate::leanh::lean_inc(v_a_3855_);
                        crate::leanh::lean_dec_ref_known(v___x_3854_, 1);
                        v___x_3856_ = lean_array_push(v_b_3847_, v_a_3855_);
                        v_as_x27_3846_ = v_tail_3853_;
                        v_b_3847_ = v___x_3856_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3847_);
                        v_a_3858_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                        v_isSharedCheck_3865_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3854_)) as u8;
                        if v_isSharedCheck_3865_ == 0 {
                            v___x_3860_ = v___x_3854_;
                            v_isShared_3861_ = v_isSharedCheck_3865_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3858_);
                            crate::leanh::lean_dec(v___x_3854_);
                            v___x_3860_ = crate::leanh::lean_box(0);
                            v_isShared_3861_ = v_isSharedCheck_3865_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3861_ == 0 {
                    v___x_3863_ = v___x_3860_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg___boxed(
    mut v_as_x27_3866_: *mut crate::leanh::LeanObject,
    mut v_b_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(
            v_as_x27_3866_,
            v_b_3867_,
            v___y_3868_,
            v___y_3869_,
        );
    crate::leanh::lean_dec(v___y_3869_);
    crate::leanh::lean_dec_ref(v___y_3868_);
    crate::leanh::lean_dec(v_as_x27_3866_);
    return v_res_3871_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(
    mut v___x_3872_: u8,
    mut v_x_3873_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3874_: u8 = 0;
    let mut v_head_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3878_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3873_) == 0 {
                    v___x_3874_ = 0;
                    return v___x_3874_;
                } else {
                    v_head_3875_ = crate::leanh::lean_ctor_get(v_x_3873_, 0);
                    crate::leanh::lean_inc_n(v_head_3875_, 2);
                    v_tail_3876_ = crate::leanh::lean_ctor_get(v_x_3873_, 1);
                    crate::leanh::lean_inc(v_tail_3876_);
                    crate::leanh::lean_dec_ref_known(v_x_3873_, 2);
                    v___x_3880_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1;
                    v___x_3881_ = l_Lean_Syntax_isOfKind(v_head_3875_, v___x_3880_);
                    if v___x_3881_ == 0 {
                        crate::leanh::lean_dec(v_head_3875_);
                        v___y_3878_ = v___x_3881_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3882_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3883_ = l_Lean_Syntax_getArg(v_head_3875_, v___x_3882_);
                        v___x_3884_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3;
                        crate::leanh::lean_inc(v___x_3883_);
                        v___x_3885_ = l_Lean_Syntax_isOfKind(v___x_3883_, v___x_3884_);
                        if v___x_3885_ == 0 {
                            crate::leanh::lean_dec(v___x_3883_);
                            crate::leanh::lean_dec(v_head_3875_);
                            v___y_3878_ = v___x_3885_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3886_ = l_Lean_Syntax_getArg(v___x_3883_, v___x_3882_);
                            crate::leanh::lean_dec(v___x_3883_);
                            v___x_3887_ = l_Lean_Syntax_matchesNull(v___x_3886_, v___x_3882_);
                            if v___x_3887_ == 0 {
                                crate::leanh::lean_dec(v_head_3875_);
                                v___y_3878_ = v___x_3887_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3888_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3889_ = l_Lean_Syntax_getArg(v_head_3875_, v___x_3888_);
                                crate::leanh::lean_dec(v_head_3875_);
                                v___x_3890_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6;
                                crate::leanh::lean_inc(v___x_3889_);
                                v___x_3891_ = l_Lean_Syntax_isOfKind(v___x_3889_, v___x_3890_);
                                if v___x_3891_ == 0 {
                                    crate::leanh::lean_dec(v___x_3889_);
                                    v___y_3878_ = v___x_3891_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3892_ = l_Lean_Syntax_getArg(v___x_3889_, v___x_3882_);
                                    v___x_3893_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8;
                                    v___x_3894_ =
                                        l_Lean_Syntax_matchesIdent(v___x_3892_, v___x_3893_);
                                    crate::leanh::lean_dec(v___x_3892_);
                                    if v___x_3894_ == 0 {
                                        crate::leanh::lean_dec(v___x_3889_);
                                        v___y_3878_ = v___x_3894_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3895_ =
                                            l_Lean_Syntax_getArg(v___x_3889_, v___x_3888_);
                                        crate::leanh::lean_dec(v___x_3889_);
                                        v___x_3896_ =
                                            l_Lean_Syntax_matchesNull(v___x_3895_, v___x_3882_);
                                        if v___x_3896_ == 0 {
                                            v___y_3878_ = v___x_3896_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___y_3878_ = v___x_3872_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_3878_ == 0 {
                    v_x_3873_ = v_tail_3876_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_3876_);
                    return v___y_3878_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(
    mut v___x_3897_: *mut crate::leanh::LeanObject,
    mut v_x_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5940__boxed_3899_: u8 = 0;
    let mut v_res_3900_: u8 = 0;
    let mut v_r_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5940__boxed_3899_ = (crate::leanh::lean_unbox(v___x_3897_) as u8);
    v_res_3900_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(
        v___x_5940__boxed_3899_,
        v_x_3898_,
    );
    v_r_3901_ = crate::leanh::lean_box((v_res_3900_) as usize);
    return v_r_3901_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(
    mut v_x_3902_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3903_: u8 = 0;
    let mut v_head_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3902_) == 0 {
                    v___x_3903_ = 0;
                    return v___x_3903_;
                } else {
                    v_head_3904_ = crate::leanh::lean_ctor_get(v_x_3902_, 0);
                    v_tail_3905_ = crate::leanh::lean_ctor_get(v_x_3902_, 1);
                    v___x_3906_ = l_Lean_isPrivateName(v_head_3904_);
                    if v___x_3906_ == 0 {
                        v_x_3902_ = v_tail_3905_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3906_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0___boxed(
    mut v_x_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: u8 = 0;
    let mut v_r_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_3908_);
    crate::leanh::lean_dec(v_x_3908_);
    v_r_3910_ = crate::leanh::lean_box((v_res_3909_) as usize);
    return v_r_3910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(
    mut v_as_3911_: *mut crate::leanh::LeanObject,
    mut v_i_3912_: usize,
    mut v_stop_3913_: usize,
) -> u8 {
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: usize = 0;
    let mut v___x_3919_: usize = 0;
    let mut v___x_3921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3914_ = lean_usize_dec_eq(v_i_3912_, v_stop_3913_);
                if v___x_3914_ == 0 {
                    v___x_3915_ = lean_array_uget_borrowed(v_as_3911_, v_i_3912_);
                    v_ctors_3916_ = crate::leanh::lean_ctor_get(v___x_3915_, 4);
                    v___x_3917_ =
                        l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(
                            v_ctors_3916_,
                        );
                    if v___x_3917_ == 0 {
                        v___x_3918_ = 1usize;
                        v___x_3919_ = lean_usize_add(v_i_3912_, v___x_3918_);
                        v_i_3912_ = v___x_3919_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3917_;
                    }
                } else {
                    v___x_3921_ = 0;
                    return v___x_3921_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3___boxed(
    mut v_as_3922_: *mut crate::leanh::LeanObject,
    mut v_i_3923_: *mut crate::leanh::LeanObject,
    mut v_stop_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3925_: usize = 0;
    let mut v_stop_boxed_3926_: usize = 0;
    let mut v_res_3927_: u8 = 0;
    let mut v_r_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3925_ = crate::leanh::lean_unbox_usize(v_i_3923_);
    crate::leanh::lean_dec(v_i_3923_);
    v_stop_boxed_3926_ = crate::leanh::lean_unbox_usize(v_stop_3924_);
    crate::leanh::lean_dec(v_stop_3924_);
    v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_3922_, v_i_boxed_3925_, v_stop_boxed_3926_);
    crate::leanh::lean_dec_ref(v_as_3922_);
    v_r_3928_ = crate::leanh::lean_box((v_res_3927_) as usize);
    return v_r_3928_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1;
    v___x_3933_ = l_Lean_stringToMessageData(v___x_3932_);
    return v___x_3933_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3935_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3;
    v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
    mut v_typeName_3937_: *mut crate::leanh::LeanObject,
    mut v_cont_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_typeName_3937_);
                v___x_3942_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_typeName_3937_, v_a_3939_, v_a_3940_);
                if crate::leanh::lean_obj_tag(v___x_3942_) == 0 {
                    v_a_3943_ = crate::leanh::lean_ctor_get(v___x_3942_, 0);
                    crate::leanh::lean_inc(v_a_3943_);
                    crate::leanh::lean_dec_ref_known(v___x_3942_, 1);
                    v_all_3944_ = crate::leanh::lean_ctor_get(v_a_3943_, 3);
                    crate::leanh::lean_inc(v_all_3944_);
                    crate::leanh::lean_dec(v_a_3943_);
                    v___x_3945_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3946_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0;
                    v___x_3947_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_all_3944_, v___x_3946_, v_a_3939_, v_a_3940_);
                    crate::leanh::lean_dec(v_all_3944_);
                    if crate::leanh::lean_obj_tag(v___x_3947_) == 0 {
                        v_a_3948_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                        crate::leanh::lean_inc(v_a_3948_);
                        crate::leanh::lean_dec_ref_known(v___x_3947_, 1);
                        v___x_3949_ = lean_array_get_size(v_a_3948_);
                        v___x_3950_ = lean_nat_dec_lt(v___x_3945_, v___x_3949_);
                        if v___x_3950_ == 0 {
                            crate::leanh::lean_dec(v_a_3948_);
                            crate::leanh::lean_dec(v_typeName_3937_);
                            crate::leanh::lean_inc(v_a_3940_);
                            crate::leanh::lean_inc_ref(v_a_3939_);
                            v___x_3951_ = crate::leanh::lean_apply_3(
                                v_cont_3938_,
                                v_a_3939_,
                                v_a_3940_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3951_;
                        } else {
                            if v___x_3950_ == 0 {
                                crate::leanh::lean_dec(v_a_3948_);
                                crate::leanh::lean_dec(v_typeName_3937_);
                                crate::leanh::lean_inc(v_a_3940_);
                                crate::leanh::lean_inc_ref(v_a_3939_);
                                v___x_3952_ = crate::leanh::lean_apply_3(
                                    v_cont_3938_,
                                    v_a_3939_,
                                    v_a_3940_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_3952_;
                            } else {
                                v___x_3953_ = 0usize;
                                v___x_3954_ = lean_usize_of_nat(v___x_3949_);
                                v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_a_3948_, v___x_3953_, v___x_3954_);
                                crate::leanh::lean_dec(v_a_3948_);
                                if v___x_3955_ == 0 {
                                    crate::leanh::lean_dec(v_typeName_3937_);
                                    crate::leanh::lean_inc(v_a_3940_);
                                    crate::leanh::lean_inc_ref(v_a_3939_);
                                    v___x_3956_ = crate::leanh::lean_apply_3(
                                        v_cont_3938_,
                                        v_a_3939_,
                                        v_a_3940_,
                                        crate::leanh::lean_box(0),
                                    );
                                    return v___x_3956_;
                                } else {
                                    v___x_3957_ = crate::leanh::lean_box((v___x_3955_) as usize);
                                    v___f_3958_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                                    crate::leanh::lean_closure_set(v___f_3958_, 0, v___x_3957_);
                                    v___x_3959_ = l_Lean_isPrivateName(v_typeName_3937_);
                                    if v___x_3959_ == 0 {
                                        v___x_3960_ =
                                            l_Lean_Elab_Command_getScope___redArg(v_a_3940_);
                                        if crate::leanh::lean_obj_tag(v___x_3960_) == 0 {
                                            v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                                            crate::leanh::lean_inc(v_a_3961_);
                                            crate::leanh::lean_dec_ref_known(v___x_3960_, 1);
                                            v_attrs_3962_ =
                                                crate::leanh::lean_ctor_get(v_a_3961_, 9);
                                            crate::leanh::lean_inc(v_attrs_3962_);
                                            crate::leanh::lean_dec(v_a_3961_);
                                            v___x_3963_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___x_3955_, v_attrs_3962_);
                                            if v___x_3963_ == 0 {
                                                crate::leanh::lean_dec(v_typeName_3937_);
                                                v___x_3964_ =
                                                    l_Lean_Elab_Command_withScope___redArg(
                                                        v___f_3958_,
                                                        v_cont_3938_,
                                                        v_a_3939_,
                                                        v_a_3940_,
                                                    );
                                                return v___x_3964_;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___f_3958_);
                                                crate::leanh::lean_dec_ref(v_cont_3938_);
                                                v___x_3965_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once), _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2);
                                                v___x_3966_ = l_Lean_MessageData_ofConstName(
                                                    v_typeName_3937_,
                                                    v___x_3959_,
                                                );
                                                v___x_3967_ =
                                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3967_,
                                                    0,
                                                    v___x_3965_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3967_,
                                                    1,
                                                    v___x_3966_,
                                                );
                                                v___x_3968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once), _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4);
                                                v___x_3969_ =
                                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3969_,
                                                    0,
                                                    v___x_3967_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3969_,
                                                    1,
                                                    v___x_3968_,
                                                );
                                                v___x_3970_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_3969_, v_a_3939_, v_a_3940_);
                                                v_a_3971_ =
                                                    crate::leanh::lean_ctor_get(v___x_3970_, 0);
                                                v_isSharedCheck_3978_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3970_))
                                                        as u8;
                                                if v_isSharedCheck_3978_ == 0 {
                                                    v___x_3973_ = v___x_3970_;
                                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3971_);
                                                    crate::leanh::lean_dec(v___x_3970_);
                                                    v___x_3973_ = crate::leanh::lean_box(0);
                                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___f_3958_);
                                            crate::leanh::lean_dec_ref(v_cont_3938_);
                                            crate::leanh::lean_dec(v_typeName_3937_);
                                            v_a_3979_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                                            v_isSharedCheck_3986_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3960_))
                                                    as u8;
                                            if v_isSharedCheck_3986_ == 0 {
                                                v___x_3981_ = v___x_3960_;
                                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3979_);
                                                crate::leanh::lean_dec(v___x_3960_);
                                                v___x_3981_ = crate::leanh::lean_box(0);
                                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_typeName_3937_);
                                        v___x_3987_ = l_Lean_Elab_Command_withScope___redArg(
                                            v___f_3958_,
                                            v_cont_3938_,
                                            v_a_3939_,
                                            v_a_3940_,
                                        );
                                        return v___x_3987_;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cont_3938_);
                        crate::leanh::lean_dec(v_typeName_3937_);
                        v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                        v_isSharedCheck_3995_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                        if v_isSharedCheck_3995_ == 0 {
                            v___x_3990_ = v___x_3947_;
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3988_);
                            crate::leanh::lean_dec(v___x_3947_);
                            v___x_3990_ = crate::leanh::lean_box(0);
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cont_3938_);
                    crate::leanh::lean_dec(v_typeName_3937_);
                    v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3942_, 0);
                    v_isSharedCheck_4003_ = (!crate::leanh::lean_is_exclusive(v___x_3942_)) as u8;
                    if v_isSharedCheck_4003_ == 0 {
                        v___x_3998_ = v___x_3942_;
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3996_);
                        crate::leanh::lean_dec(v___x_3942_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3974_ == 0 {
                    v___x_3976_ = v___x_3973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3976_;
            }
            3 => {
                if v_isShared_3982_ == 0 {
                    v___x_3984_ = v___x_3981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
                    v___x_3984_ = v_reuseFailAlloc_3985_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3984_;
            }
            5 => {
                if v_isShared_3991_ == 0 {
                    v___x_3993_ = v___x_3990_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
                    v___x_3993_ = v_reuseFailAlloc_3994_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3993_;
            }
            7 => {
                if v_isShared_3999_ == 0 {
                    v___x_4001_ = v___x_3998_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___boxed(
    mut v_typeName_4004_: *mut crate::leanh::LeanObject,
    mut v_cont_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_typeName_4004_,
        v_cont_4005_,
        v_a_4006_,
        v_a_4007_,
    );
    crate::leanh::lean_dec(v_a_4007_);
    crate::leanh::lean_dec_ref(v_a_4006_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors(
    mut v_00_u03b1_4010_: *mut crate::leanh::LeanObject,
    mut v_typeName_4011_: *mut crate::leanh::LeanObject,
    mut v_cont_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4016_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_typeName_4011_,
        v_cont_4012_,
        v_a_4013_,
        v_a_4014_,
    );
    return v___x_4016_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(
    mut v_00_u03b1_4017_: *mut crate::leanh::LeanObject,
    mut v_typeName_4018_: *mut crate::leanh::LeanObject,
    mut v_cont_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(
        v_00_u03b1_4017_,
        v_typeName_4018_,
        v_cont_4019_,
        v_a_4020_,
        v_a_4021_,
    );
    crate::leanh::lean_dec(v_a_4021_);
    crate::leanh::lean_dec_ref(v_a_4020_);
    return v_res_4023_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(
    mut v_as_4024_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4025_: *mut crate::leanh::LeanObject,
    mut v_b_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(
            v_as_x27_4025_,
            v_b_4026_,
            v___y_4028_,
            v___y_4029_,
        );
    return v___x_4031_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___boxed(
    mut v_as_4032_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4033_: *mut crate::leanh::LeanObject,
    mut v_b_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(
        v_as_4032_,
        v_as_x27_4033_,
        v_b_4034_,
        v_a_4035_,
        v___y_4036_,
        v___y_4037_,
    );
    crate::leanh::lean_dec(v___y_4037_);
    crate::leanh::lean_dec_ref(v___y_4036_);
    crate::leanh::lean_dec(v_as_x27_4033_);
    crate::leanh::lean_dec(v_as_4032_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(
    mut v_msgData_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4044_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_4040_, v___y_4042_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(
    mut v_msgData_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_4045_, v___y_4046_, v___y_4047_);
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    return v_res_4049_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(
    mut v_00_u03b1_4050_: *mut crate::leanh::LeanObject,
    mut v_msg_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
            v_msg_4051_,
            v___y_4052_,
            v___y_4053_,
        );
    return v___x_4055_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(
    mut v_00_u03b1_4056_: *mut crate::leanh::LeanObject,
    mut v_msg_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(
        v_00_u03b1_4056_,
        v_msg_4057_,
        v___y_4058_,
        v___y_4059_,
    );
    crate::leanh::lean_dec(v___y_4059_);
    crate::leanh::lean_dec_ref(v___y_4058_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(
    mut v_msgData_4062_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_4062_, v_macroStack_4063_, v___y_4065_);
    return v___x_4067_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(
    mut v_msgData_4068_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_4068_, v_macroStack_4069_, v___y_4070_, v___y_4071_);
    crate::leanh::lean_dec(v___y_4071_);
    crate::leanh::lean_dec_ref(v___y_4070_);
    return v_res_4073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(
    mut v_sz_4074_: usize,
    mut v_i_4075_: usize,
    mut v_bs_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4077_: u8 = 0;
    let mut v_v_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4077_ = lean_usize_dec_lt(v_i_4075_, v_sz_4074_);
                if v___x_4077_ == 0 {
                    return v_bs_4076_;
                } else {
                    v_v_4078_ = lean_array_uget(v_bs_4076_, v_i_4075_);
                    v___x_4079_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4080_ = lean_array_uset(v_bs_4076_, v_i_4075_, v___x_4079_);
                    v___x_4081_ = 1usize;
                    v___x_4082_ = lean_usize_add(v_i_4075_, v___x_4081_);
                    v___x_4083_ = lean_array_uset(v_bs_x27_4080_, v_i_4075_, v_v_4078_);
                    v_i_4075_ = v___x_4082_;
                    v_bs_4076_ = v___x_4083_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(
    mut v_sz_4085_: *mut crate::leanh::LeanObject,
    mut v_i_4086_: *mut crate::leanh::LeanObject,
    mut v_bs_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4088_: usize = 0;
    let mut v_i_boxed_4089_: usize = 0;
    let mut v_res_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4088_ = crate::leanh::lean_unbox_usize(v_sz_4085_);
    crate::leanh::lean_dec(v_sz_4085_);
    v_i_boxed_4089_ = crate::leanh::lean_unbox_usize(v_i_4086_);
    crate::leanh::lean_dec(v_i_4086_);
    v_res_4090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_4088_, v_i_boxed_4089_, v_bs_4087_);
    return v_res_4090_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(
    mut v_msgData_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4097_ = lean_st_ref_get(v___y_4095_);
    v_env_4098_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
    crate::leanh::lean_inc_ref(v_env_4098_);
    crate::leanh::lean_dec(v___x_4097_);
    v___x_4099_ = lean_st_ref_get(v___y_4093_);
    v_mctx_4100_ = crate::leanh::lean_ctor_get(v___x_4099_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4100_);
    crate::leanh::lean_dec(v___x_4099_);
    v_lctx_4101_ = crate::leanh::lean_ctor_get(v___y_4092_, 2);
    v_options_4102_ = crate::leanh::lean_ctor_get(v___y_4094_, 2);
    crate::leanh::lean_inc_ref(v_options_4102_);
    crate::leanh::lean_inc_ref(v_lctx_4101_);
    v___x_4103_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4103_, 0, v_env_4098_);
    crate::leanh::lean_ctor_set(v___x_4103_, 1, v_mctx_4100_);
    crate::leanh::lean_ctor_set(v___x_4103_, 2, v_lctx_4101_);
    crate::leanh::lean_ctor_set(v___x_4103_, 3, v_options_4102_);
    v___x_4104_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4104_, 0, v___x_4103_);
    crate::leanh::lean_ctor_set(v___x_4104_, 1, v_msgData_4091_);
    v___x_4105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4105_, 0, v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    crate::leanh::lean_dec(v___y_4110_);
    crate::leanh::lean_dec_ref(v___y_4109_);
    crate::leanh::lean_dec(v___y_4108_);
    crate::leanh::lean_dec_ref(v___y_4107_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_4113_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v_unused_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4117_ = crate::leanh::lean_ctor_get(v___y_4115_, 2);
                v___x_4118_ = l_Lean_Elab_pp_macroStack;
                v___x_4119_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_options_4117_, v___x_4118_);
                if v___x_4119_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_4114_);
                    v___x_4120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4120_, 0, v_msgData_4113_);
                    return v___x_4120_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_4114_) == 0 {
                        v___x_4121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4121_, 0, v_msgData_4113_);
                        return v___x_4121_;
                    } else {
                        v_head_4122_ = crate::leanh::lean_ctor_get(v_macroStack_4114_, 0);
                        crate::leanh::lean_inc(v_head_4122_);
                        v_after_4123_ = crate::leanh::lean_ctor_get(v_head_4122_, 1);
                        v_isSharedCheck_4138_ =
                            (!crate::leanh::lean_is_exclusive(v_head_4122_)) as u8;
                        if v_isSharedCheck_4138_ == 0 {
                            v_unused_4139_ = crate::leanh::lean_ctor_get(v_head_4122_, 0);
                            crate::leanh::lean_dec(v_unused_4139_);
                            v___x_4125_ = v_head_4122_;
                            v_isShared_4126_ = v_isSharedCheck_4138_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_4123_);
                            crate::leanh::lean_dec(v_head_4122_);
                            v___x_4125_ = crate::leanh::lean_box(0);
                            v_isShared_4126_ = v_isSharedCheck_4138_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4127_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_4126_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4125_, 7);
                    crate::leanh::lean_ctor_set(v___x_4125_, 1, v___x_4127_);
                    crate::leanh::lean_ctor_set(v___x_4125_, 0, v_msgData_4113_);
                    v___x_4129_ = v___x_4125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_msgData_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 1, v___x_4127_);
                    v___x_4129_ = v_reuseFailAlloc_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
                v___x_4131_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4129_);
                crate::leanh::lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                v___x_4132_ = l_Lean_MessageData_ofSyntax(v_after_4123_);
                v___x_4133_ = l_Lean_indentD(v___x_4132_);
                v_msgData_4134_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_4134_, 0, v___x_4131_);
                crate::leanh::lean_ctor_set(v_msgData_4134_, 1, v___x_4133_);
                v___x_4135_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_4134_, v_macroStack_4114_);
                v___x_4136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                return v___x_4136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_4140_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4144_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_4140_, v_macroStack_4141_, v___y_4142_);
    crate::leanh::lean_dec_ref(v___y_4142_);
    return v_res_4144_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(
    mut v_msg_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4153_ = crate::leanh::lean_ctor_get(v___y_4150_, 5);
                v___x_4154_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_4145_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
                v_a_4155_ = crate::leanh::lean_ctor_get(v___x_4154_, 0);
                crate::leanh::lean_inc(v_a_4155_);
                crate::leanh::lean_dec_ref(v___x_4154_);
                v_macroStack_4156_ = crate::leanh::lean_ctor_get(v___y_4146_, 1);
                v___x_4157_ = l_Lean_Elab_getBetterRef(v_ref_4153_, v_macroStack_4156_);
                crate::leanh::lean_inc(v_macroStack_4156_);
                v___x_4158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_4155_, v_macroStack_4156_, v___y_4150_);
                v_a_4159_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                v_isSharedCheck_4167_ = (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                if v_isSharedCheck_4167_ == 0 {
                    v___x_4161_ = v___x_4158_;
                    v_isShared_4162_ = v_isSharedCheck_4167_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4159_);
                    crate::leanh::lean_dec(v___x_4158_);
                    v___x_4161_ = crate::leanh::lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4163_, 0, v___x_4157_);
                crate::leanh::lean_ctor_set(v___x_4163_, 1, v_a_4159_);
                if v_isShared_4162_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4161_, 1);
                    crate::leanh::lean_ctor_set(v___x_4161_, 0, v___x_4163_);
                    v___x_4165_ = v___x_4161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
                    v___x_4165_ = v_reuseFailAlloc_4166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(
    mut v_msg_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4176_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    crate::leanh::lean_dec(v___y_4174_);
    crate::leanh::lean_dec_ref(v___y_4173_);
    crate::leanh::lean_dec(v___y_4172_);
    crate::leanh::lean_dec_ref(v___y_4171_);
    crate::leanh::lean_dec(v___y_4170_);
    crate::leanh::lean_dec_ref(v___y_4169_);
    return v_res_4176_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
    mut v_constName_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4185_ = lean_st_ref_get(v___y_4183_);
                v_env_4186_ = crate::leanh::lean_ctor_get(v___x_4185_, 0);
                crate::leanh::lean_inc_ref(v_env_4186_);
                crate::leanh::lean_dec(v___x_4185_);
                crate::leanh::lean_inc(v_constName_4177_);
                v___x_4187_ = l_Lean_isInductiveCore_x3f(v_env_4186_, v_constName_4177_);
                if crate::leanh::lean_obj_tag(v___x_4187_) == 0 {
                    v___x_4188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
                    v___x_4189_ = 0;
                    v___x_4190_ = l_Lean_MessageData_ofConstName(v_constName_4177_, v___x_4189_);
                    v___x_4191_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4191_, 0, v___x_4188_);
                    crate::leanh::lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                    v___x_4192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
                    v___x_4193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4191_);
                    crate::leanh::lean_ctor_set(v___x_4193_, 1, v___x_4192_);
                    v___x_4194_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_4193_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
                    return v___x_4194_;
                } else {
                    crate::leanh::lean_dec(v_constName_4177_);
                    v_val_4195_ = crate::leanh::lean_ctor_get(v___x_4187_, 0);
                    v_isSharedCheck_4202_ = (!crate::leanh::lean_is_exclusive(v___x_4187_)) as u8;
                    if v_isSharedCheck_4202_ == 0 {
                        v___x_4197_ = v___x_4187_;
                        v_isShared_4198_ = v_isSharedCheck_4202_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4195_);
                        crate::leanh::lean_dec(v___x_4187_);
                        v___x_4197_ = crate::leanh::lean_box(0);
                        v_isShared_4198_ = v_isSharedCheck_4202_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4198_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4197_, 0);
                    v___x_4200_ = v___x_4197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4195_);
                    v___x_4200_ = v_reuseFailAlloc_4201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(
    mut v_constName_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
        v_constName_4203_,
        v___y_4204_,
        v___y_4205_,
        v___y_4206_,
        v___y_4207_,
        v___y_4208_,
        v___y_4209_,
    );
    crate::leanh::lean_dec(v___y_4209_);
    crate::leanh::lean_dec_ref(v___y_4208_);
    crate::leanh::lean_dec(v___y_4207_);
    crate::leanh::lean_dec_ref(v___y_4206_);
    crate::leanh::lean_dec(v___y_4205_);
    crate::leanh::lean_dec_ref(v___y_4204_);
    return v_res_4211_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstName(
    mut v_className_4213_: *mut crate::leanh::LeanObject,
    mut v_indName_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4239_: usize = 0;
    let mut v___x_4240_: usize = 0;
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4250_: u8 = 0;
    let mut v_a_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4222_ =
                    l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
                        v_indName_4214_,
                        v_a_4215_,
                        v_a_4216_,
                        v_a_4217_,
                        v_a_4218_,
                        v_a_4219_,
                        v_a_4220_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4222_) == 0 {
                    v_a_4223_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    crate::leanh::lean_inc_n(v_a_4223_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4222_, 1);
                    v___x_4224_ = l_Lean_Elab_Deriving_mkInductArgNames(
                        v_a_4223_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4224_) == 0 {
                        v_a_4225_ = crate::leanh::lean_ctor_get(v___x_4224_, 0);
                        crate::leanh::lean_inc_n(v_a_4225_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4224_, 1);
                        v___x_4226_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                            v_a_4225_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_,
                            v_a_4220_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4226_) == 0 {
                            v_a_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                            crate::leanh::lean_inc(v_a_4227_);
                            crate::leanh::lean_dec_ref_known(v___x_4226_, 1);
                            v___x_4228_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                v_a_4223_, v_a_4225_, v_a_4219_,
                            );
                            v_a_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                            crate::leanh::lean_inc(v_a_4229_);
                            crate::leanh::lean_dec_ref(v___x_4228_);
                            v_ref_4230_ = crate::leanh::lean_ctor_get(v_a_4219_, 5);
                            v___x_4231_ = 0;
                            v___x_4232_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4231_);
                            v___x_4233_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                            v___x_4234_ = l_Lean_mkCIdent(v_className_4213_);
                            v___x_4235_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                            crate::leanh::lean_inc(v___x_4232_);
                            v___x_4236_ = l_Lean_Syntax_node1(v___x_4232_, v___x_4235_, v_a_4229_);
                            v___x_4237_ = l_Lean_Syntax_node2(
                                v___x_4232_,
                                v___x_4233_,
                                v___x_4234_,
                                v___x_4236_,
                            );
                            v___x_4238_ = l_Lean_Elab_Deriving_mkInstName___closed__0;
                            v_sz_4239_ = lean_array_size(v_a_4227_);
                            v___x_4240_ = 0usize;
                            v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_4239_, v___x_4240_, v_a_4227_);
                            v___x_4242_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(
                                v___x_4238_,
                                v___x_4241_,
                                v___x_4237_,
                                v_a_4215_,
                                v_a_4216_,
                                v_a_4217_,
                                v_a_4218_,
                                v_a_4219_,
                                v_a_4220_,
                            );
                            return v___x_4242_;
                        } else {
                            crate::leanh::lean_dec(v_a_4225_);
                            crate::leanh::lean_dec(v_a_4223_);
                            crate::leanh::lean_dec(v_className_4213_);
                            v_a_4243_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                            v_isSharedCheck_4250_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4226_)) as u8;
                            if v_isSharedCheck_4250_ == 0 {
                                v___x_4245_ = v___x_4226_;
                                v_isShared_4246_ = v_isSharedCheck_4250_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4243_);
                                crate::leanh::lean_dec(v___x_4226_);
                                v___x_4245_ = crate::leanh::lean_box(0);
                                v_isShared_4246_ = v_isSharedCheck_4250_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4223_);
                        crate::leanh::lean_dec(v_className_4213_);
                        v_a_4251_ = crate::leanh::lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4258_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4258_ == 0 {
                            v___x_4253_ = v___x_4224_;
                            v_isShared_4254_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4251_);
                            crate::leanh::lean_dec(v___x_4224_);
                            v___x_4253_ = crate::leanh::lean_box(0);
                            v_isShared_4254_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_className_4213_);
                    v_a_4259_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4266_ = (!crate::leanh::lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4222_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4259_);
                        crate::leanh::lean_dec(v___x_4222_);
                        v___x_4261_ = crate::leanh::lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4246_ == 0 {
                    v___x_4248_ = v___x_4245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
                    v___x_4248_ = v_reuseFailAlloc_4249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4248_;
            }
            3 => {
                if v_isShared_4254_ == 0 {
                    v___x_4256_ = v___x_4253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
                    v___x_4256_ = v_reuseFailAlloc_4257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4256_;
            }
            5 => {
                if v_isShared_4262_ == 0 {
                    v___x_4264_ = v___x_4261_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
                    v___x_4264_ = v_reuseFailAlloc_4265_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstName___boxed(
    mut v_className_4267_: *mut crate::leanh::LeanObject,
    mut v_indName_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_Elab_Deriving_mkInstName(
        v_className_4267_,
        v_indName_4268_,
        v_a_4269_,
        v_a_4270_,
        v_a_4271_,
        v_a_4272_,
        v_a_4273_,
        v_a_4274_,
    );
    crate::leanh::lean_dec(v_a_4274_);
    crate::leanh::lean_dec_ref(v_a_4273_);
    crate::leanh::lean_dec(v_a_4272_);
    crate::leanh::lean_dec_ref(v_a_4271_);
    crate::leanh::lean_dec(v_a_4270_);
    crate::leanh::lean_dec_ref(v_a_4269_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(
    mut v_00_u03b1_4277_: *mut crate::leanh::LeanObject,
    mut v_msg_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
    return v___x_4286_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(
    mut v_00_u03b1_4287_: *mut crate::leanh::LeanObject,
    mut v_msg_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_4287_, v_msg_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
    crate::leanh::lean_dec(v___y_4294_);
    crate::leanh::lean_dec_ref(v___y_4293_);
    crate::leanh::lean_dec(v___y_4292_);
    crate::leanh::lean_dec_ref(v___y_4291_);
    crate::leanh::lean_dec(v___y_4290_);
    crate::leanh::lean_dec_ref(v___y_4289_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(
    mut v_msgData_4297_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_4297_, v_macroStack_4298_, v___y_4303_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_4307_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
    mut v___y_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_4307_, v_macroStack_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
    crate::leanh::lean_dec(v___y_4314_);
    crate::leanh::lean_dec_ref(v___y_4313_);
    crate::leanh::lean_dec(v___y_4312_);
    crate::leanh::lean_dec_ref(v___y_4311_);
    crate::leanh::lean_dec(v___y_4310_);
    crate::leanh::lean_dec_ref(v___y_4309_);
    return v_res_4316_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(
    mut v_as_x27_4317_: *mut crate::leanh::LeanObject,
    mut v_b_4318_: *mut crate::leanh::LeanObject,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4317_) == 0 {
                    v___x_4326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4326_, 0, v_b_4318_);
                    return v___x_4326_;
                } else {
                    v_head_4327_ = crate::leanh::lean_ctor_get(v_as_x27_4317_, 0);
                    v_tail_4328_ = crate::leanh::lean_ctor_get(v_as_x27_4317_, 1);
                    crate::leanh::lean_inc(v_head_4327_);
                    v___x_4329_ =
                        l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
                            v_head_4327_,
                            v___y_4319_,
                            v___y_4320_,
                            v___y_4321_,
                            v___y_4322_,
                            v___y_4323_,
                            v___y_4324_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4329_) == 0 {
                        v_a_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                        crate::leanh::lean_inc(v_a_4330_);
                        crate::leanh::lean_dec_ref_known(v___x_4329_, 1);
                        v___x_4331_ = lean_array_push(v_b_4318_, v_a_4330_);
                        v_as_x27_4317_ = v_tail_4328_;
                        v_b_4318_ = v___x_4331_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4318_);
                        v_a_4333_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                        v_isSharedCheck_4340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4329_)) as u8;
                        if v_isSharedCheck_4340_ == 0 {
                            v___x_4335_ = v___x_4329_;
                            v_isShared_4336_ = v_isSharedCheck_4340_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4333_);
                            crate::leanh::lean_dec(v___x_4329_);
                            v___x_4335_ = crate::leanh::lean_box(0);
                            v_isShared_4336_ = v_isSharedCheck_4340_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4336_ == 0 {
                    v___x_4338_ = v___x_4335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
                    v___x_4338_ = v_reuseFailAlloc_4339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(
    mut v_as_x27_4341_: *mut crate::leanh::LeanObject,
    mut v_b_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(
        v_as_x27_4341_,
        v_b_4342_,
        v___y_4343_,
        v___y_4344_,
        v___y_4345_,
        v___y_4346_,
        v___y_4347_,
        v___y_4348_,
    );
    crate::leanh::lean_dec(v___y_4348_);
    crate::leanh::lean_dec_ref(v___y_4347_);
    crate::leanh::lean_dec(v___y_4346_);
    crate::leanh::lean_dec_ref(v___y_4345_);
    crate::leanh::lean_dec(v___y_4344_);
    crate::leanh::lean_dec_ref(v___y_4343_);
    crate::leanh::lean_dec(v_as_x27_4341_);
    return v_res_4350_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4351_) == 0 {
                    v___x_4353_ = l_List_reverse___redArg(v_a_4352_);
                    return v___x_4353_;
                } else {
                    v_head_4354_ = crate::leanh::lean_ctor_get(v_a_4351_, 0);
                    v_tail_4355_ = crate::leanh::lean_ctor_get(v_a_4351_, 1);
                    v_isSharedCheck_4364_ = (!crate::leanh::lean_is_exclusive(v_a_4351_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4357_ = v_a_4351_;
                        v_isShared_4358_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4355_);
                        crate::leanh::lean_inc(v_head_4354_);
                        crate::leanh::lean_dec(v_a_4351_);
                        v___x_4357_ = crate::leanh::lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4359_ = l_Lean_MessageData_ofName(v_head_4354_);
                if v_isShared_4358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4357_, 1, v_a_4352_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4359_);
                    v___x_4361_ = v___x_4357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_a_4352_);
                    v___x_4361_ = v_reuseFailAlloc_4363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4351_ = v_tail_4355_;
                v_a_4352_ = v___x_4361_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: f64 = 0.0;
    v___x_4365_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4366_ = lean_float_of_nat(v___x_4365_);
    return v___x_4366_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
    mut v_cls_4370_: *mut crate::leanh::LeanObject,
    mut v_msg_4371_: *mut crate::leanh::LeanObject,
    mut v___y_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4395_: u8 = 0;
    let mut v_tid_4396_: u64 = 0;
    let mut v_traces_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: f64 = 0.0;
    let mut v___x_4403_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4377_ = crate::leanh::lean_ctor_get(v___y_4374_, 5);
                v___x_4378_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
                v_a_4379_ = crate::leanh::lean_ctor_get(v___x_4378_, 0);
                v_isSharedCheck_4423_ = (!crate::leanh::lean_is_exclusive(v___x_4378_)) as u8;
                if v_isSharedCheck_4423_ == 0 {
                    v___x_4381_ = v___x_4378_;
                    v_isShared_4382_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4379_);
                    crate::leanh::lean_dec(v___x_4378_);
                    v___x_4381_ = crate::leanh::lean_box(0);
                    v_isShared_4382_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4383_ = lean_st_ref_take(v___y_4375_);
                v_traceState_4384_ = crate::leanh::lean_ctor_get(v___x_4383_, 4);
                v_env_4385_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                v_nextMacroScope_4386_ = crate::leanh::lean_ctor_get(v___x_4383_, 1);
                v_ngen_4387_ = crate::leanh::lean_ctor_get(v___x_4383_, 2);
                v_auxDeclNGen_4388_ = crate::leanh::lean_ctor_get(v___x_4383_, 3);
                v_cache_4389_ = crate::leanh::lean_ctor_get(v___x_4383_, 5);
                v_messages_4390_ = crate::leanh::lean_ctor_get(v___x_4383_, 6);
                v_infoState_4391_ = crate::leanh::lean_ctor_get(v___x_4383_, 7);
                v_snapshotTasks_4392_ = crate::leanh::lean_ctor_get(v___x_4383_, 8);
                v_isSharedCheck_4422_ = (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                if v_isSharedCheck_4422_ == 0 {
                    v___x_4394_ = v___x_4383_;
                    v_isShared_4395_ = v_isSharedCheck_4422_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4392_);
                    crate::leanh::lean_inc(v_infoState_4391_);
                    crate::leanh::lean_inc(v_messages_4390_);
                    crate::leanh::lean_inc(v_cache_4389_);
                    crate::leanh::lean_inc(v_traceState_4384_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4388_);
                    crate::leanh::lean_inc(v_ngen_4387_);
                    crate::leanh::lean_inc(v_nextMacroScope_4386_);
                    crate::leanh::lean_inc(v_env_4385_);
                    crate::leanh::lean_dec(v___x_4383_);
                    v___x_4394_ = crate::leanh::lean_box(0);
                    v_isShared_4395_ = v_isSharedCheck_4422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4396_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4384_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4397_ = crate::leanh::lean_ctor_get(v_traceState_4384_, 0);
                v_isSharedCheck_4421_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4384_)) as u8;
                if v_isSharedCheck_4421_ == 0 {
                    v___x_4399_ = v_traceState_4384_;
                    v_isShared_4400_ = v_isSharedCheck_4421_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4397_);
                    crate::leanh::lean_dec(v_traceState_4384_);
                    v___x_4399_ = crate::leanh::lean_box(0);
                    v_isShared_4400_ = v_isSharedCheck_4421_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4401_ = crate::leanh::lean_box(0);
                v___x_4402_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
                v___x_4403_ = 0;
                v___x_4404_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1;
                v___x_4405_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4405_, 0, v_cls_4370_);
                crate::leanh::lean_ctor_set(v___x_4405_, 1, v___x_4401_);
                crate::leanh::lean_ctor_set(v___x_4405_, 2, v___x_4404_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4402_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4402_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4403_,
                );
                v___x_4406_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2;
                v___x_4407_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4407_, 0, v___x_4405_);
                crate::leanh::lean_ctor_set(v___x_4407_, 1, v_a_4379_);
                crate::leanh::lean_ctor_set(v___x_4407_, 2, v___x_4406_);
                crate::leanh::lean_inc(v_ref_4377_);
                v___x_4408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4408_, 0, v_ref_4377_);
                crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4407_);
                v___x_4409_ = l_Lean_PersistentArray_push___redArg(v_traces_4397_, v___x_4408_);
                if v_isShared_4400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4399_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4399_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4420_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4409_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4420_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4396_,
                    );
                    v___x_4411_ = v_reuseFailAlloc_4420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4394_, 4, v___x_4411_);
                    v___x_4413_ = v___x_4394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_env_4385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_nextMacroScope_4386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_ngen_4387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_auxDeclNGen_4388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 4, v___x_4411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 5, v_cache_4389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 6, v_messages_4390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 7, v_infoState_4391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 8, v_snapshotTasks_4392_);
                    v___x_4413_ = v_reuseFailAlloc_4419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4414_ = lean_st_ref_set(v___y_4375_, v___x_4413_);
                v___x_4415_ = crate::leanh::lean_box(0);
                if v_isShared_4382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4415_);
                    v___x_4417_ = v___x_4381_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(
    mut v_cls_4424_: *mut crate::leanh::LeanObject,
    mut v_msg_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
        v_cls_4424_,
        v_msg_4425_,
        v___y_4426_,
        v___y_4427_,
        v___y_4428_,
        v___y_4429_,
    );
    crate::leanh::lean_dec(v___y_4429_);
    crate::leanh::lean_dec_ref(v___y_4428_);
    crate::leanh::lean_dec(v___y_4427_);
    crate::leanh::lean_dec_ref(v___y_4426_);
    return v_res_4431_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(
    mut v_fnPrefix_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_range_4435_: *mut crate::leanh::LeanObject,
    mut v_b_4436_: *mut crate::leanh::LeanObject,
    mut v_i_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_4439_ = crate::leanh::lean_ctor_get(v_range_4435_, 1);
                v_step_4440_ = crate::leanh::lean_ctor_get(v_range_4435_, 2);
                v___x_4441_ = lean_nat_dec_lt(v_i_4437_, v_stop_4439_);
                if v___x_4441_ == 0 {
                    crate::leanh::lean_dec(v_i_4437_);
                    crate::leanh::lean_dec(v_a_4434_);
                    crate::leanh::lean_dec_ref(v_fnPrefix_4433_);
                    v___x_4442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4442_, 0, v_b_4436_);
                    return v___x_4442_;
                } else {
                    v___x_4443_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4444_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0;
                    crate::leanh::lean_inc_ref(v_fnPrefix_4433_);
                    v___x_4445_ = lean_string_append(v_fnPrefix_4433_, v___x_4444_);
                    v___x_4446_ = lean_nat_add(v_i_4437_, v___x_4443_);
                    v___x_4447_ = l_Nat_reprFast(v___x_4446_);
                    v___x_4448_ = lean_string_append(v___x_4445_, v___x_4447_);
                    crate::leanh::lean_dec_ref(v___x_4447_);
                    v___x_4449_ = crate::leanh::lean_box(0);
                    v___x_4450_ = l_Lean_Name_str___override(v___x_4449_, v___x_4448_);
                    crate::leanh::lean_inc(v_a_4434_);
                    v___x_4451_ = l_Lean_Name_append(v_a_4434_, v___x_4450_);
                    v___x_4452_ = lean_array_push(v_b_4436_, v___x_4451_);
                    v___x_4453_ = lean_nat_add(v_i_4437_, v_step_4440_);
                    crate::leanh::lean_dec(v_i_4437_);
                    v_b_4436_ = v___x_4452_;
                    v_i_4437_ = v___x_4453_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(
    mut v_fnPrefix_4455_: *mut crate::leanh::LeanObject,
    mut v_a_4456_: *mut crate::leanh::LeanObject,
    mut v_range_4457_: *mut crate::leanh::LeanObject,
    mut v_b_4458_: *mut crate::leanh::LeanObject,
    mut v_i_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4461_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4455_, v_a_4456_, v_range_4457_, v_b_4458_, v_i_4459_);
    crate::leanh::lean_dec_ref(v_range_4457_);
    return v_res_4461_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4470_ = l_Lean_Elab_Deriving_mkContext___closed__2;
    v___x_4471_ = l_Lean_Elab_Deriving_mkContext___closed__4;
    v___x_4472_ = l_Lean_Name_append(v___x_4471_, v___x_4470_);
    return v___x_4472_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_Elab_Deriving_mkContext___closed__6;
    v___x_4475_ = l_Lean_stringToMessageData(v___x_4474_);
    return v___x_4475_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Lean_Elab_Deriving_mkContext___closed__8;
    v___x_4478_ = l_Lean_stringToMessageData(v___x_4477_);
    return v___x_4478_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkContext(
    mut v_className_4479_: *mut crate::leanh::LeanObject,
    mut v_fnPrefix_4480_: *mut crate::leanh::LeanObject,
    mut v_typeName_4481_: *mut crate::leanh::LeanObject,
    mut v_supportsRec_4482_: u8,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
    mut v_a_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_a_4486_: *mut crate::leanh::LeanObject,
    mut v_a_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___y_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4505_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4512_: u8 = 0;
    let mut v___y_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v_auxFunNames_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4528_: u8 = 0;
    let mut v_inheritedTraceOptions_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut v_a_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_a_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_typeName_4481_);
                v___x_4490_ =
                    l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
                        v_typeName_4481_,
                        v_a_4483_,
                        v_a_4484_,
                        v_a_4485_,
                        v_a_4486_,
                        v_a_4487_,
                        v_a_4488_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_a_4491_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    crate::leanh::lean_inc(v_a_4491_);
                    crate::leanh::lean_dec_ref_known(v___x_4490_, 1);
                    v_all_4492_ = crate::leanh::lean_ctor_get(v_a_4491_, 3);
                    v_isRec_4493_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4491_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    );
                    v___x_4494_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4495_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0;
                    v___x_4496_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_4492_, v___x_4495_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
                    if crate::leanh::lean_obj_tag(v___x_4496_) == 0 {
                        v_a_4497_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                        crate::leanh::lean_inc(v_a_4497_);
                        crate::leanh::lean_dec_ref_known(v___x_4496_, 1);
                        v___x_4498_ = l_Lean_Elab_Deriving_mkInstName(
                            v_className_4479_,
                            v_typeName_4481_,
                            v_a_4483_,
                            v_a_4484_,
                            v_a_4485_,
                            v_a_4486_,
                            v_a_4487_,
                            v_a_4488_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4498_) == 0 {
                            v_a_4499_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                            v_isSharedCheck_4562_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4498_)) as u8;
                            if v_isSharedCheck_4562_ == 0 {
                                v___x_4501_ = v___x_4498_;
                                v_isShared_4502_ = v_isSharedCheck_4562_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4499_);
                                crate::leanh::lean_dec(v___x_4498_);
                                v___x_4501_ = crate::leanh::lean_box(0);
                                v_isShared_4502_ = v_isSharedCheck_4562_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4497_);
                            crate::leanh::lean_dec(v_a_4491_);
                            crate::leanh::lean_dec_ref(v_fnPrefix_4480_);
                            v_a_4563_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                            v_isSharedCheck_4570_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4498_)) as u8;
                            if v_isSharedCheck_4570_ == 0 {
                                v___x_4565_ = v___x_4498_;
                                v_isShared_4566_ = v_isSharedCheck_4570_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4563_);
                                crate::leanh::lean_dec(v___x_4498_);
                                v___x_4565_ = crate::leanh::lean_box(0);
                                v_isShared_4566_ = v_isSharedCheck_4570_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4491_);
                        crate::leanh::lean_dec(v_typeName_4481_);
                        crate::leanh::lean_dec_ref(v_fnPrefix_4480_);
                        crate::leanh::lean_dec(v_className_4479_);
                        v_a_4571_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4578_ == 0 {
                            v___x_4573_ = v___x_4496_;
                            v_isShared_4574_ = v_isSharedCheck_4578_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4571_);
                            crate::leanh::lean_dec(v___x_4496_);
                            v___x_4573_ = crate::leanh::lean_box(0);
                            v_isShared_4574_ = v_isSharedCheck_4578_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_typeName_4481_);
                    crate::leanh::lean_dec_ref(v_fnPrefix_4480_);
                    crate::leanh::lean_dec(v_className_4479_);
                    v_a_4579_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4586_ = (!crate::leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4586_ == 0 {
                        v___x_4581_ = v___x_4490_;
                        v_isShared_4582_ = v_isSharedCheck_4586_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4579_);
                        crate::leanh::lean_dec(v___x_4490_);
                        v___x_4581_ = crate::leanh::lean_box(0);
                        v_isShared_4582_ = v_isSharedCheck_4586_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4552_ = l_List_lengthTR___redArg(v_all_4492_);
                v___x_4553_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4554_ = lean_nat_dec_eq(v___x_4552_, v___x_4553_);
                if v___x_4554_ == 0 {
                    v___x_4555_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4494_);
                    crate::leanh::lean_ctor_set(v___x_4555_, 1, v___x_4552_);
                    crate::leanh::lean_ctor_set(v___x_4555_, 2, v___x_4553_);
                    crate::leanh::lean_inc(v_a_4499_);
                    v___x_4556_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4480_, v_a_4499_, v___x_4555_, v___x_4495_, v___x_4494_);
                    crate::leanh::lean_dec_ref_known(v___x_4555_, 3);
                    v_a_4557_ = crate::leanh::lean_ctor_get(v___x_4556_, 0);
                    crate::leanh::lean_inc(v_a_4557_);
                    crate::leanh::lean_dec_ref(v___x_4556_);
                    v_auxFunNames_4520_ = v_a_4557_;
                    v___y_4521_ = v_a_4483_;
                    v___y_4522_ = v_a_4484_;
                    v___y_4523_ = v_a_4485_;
                    v___y_4524_ = v_a_4486_;
                    v___y_4525_ = v_a_4487_;
                    v___y_4526_ = v_a_4488_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4552_);
                    v___x_4558_ = crate::leanh::lean_box(0);
                    v___x_4559_ = l_Lean_Name_str___override(v___x_4558_, v_fnPrefix_4480_);
                    crate::leanh::lean_inc(v_a_4499_);
                    v___x_4560_ = l_Lean_Name_append(v_a_4499_, v___x_4559_);
                    v___x_4561_ = lean_array_push(v___x_4495_, v___x_4560_);
                    v_auxFunNames_4520_ = v___x_4561_;
                    v___y_4521_ = v_a_4483_;
                    v___y_4522_ = v_a_4484_;
                    v___y_4523_ = v_a_4485_;
                    v___y_4524_ = v_a_4486_;
                    v___y_4525_ = v_a_4487_;
                    v___y_4526_ = v_a_4488_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v___x_4506_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4506_, 0, v_a_4499_);
                crate::leanh::lean_ctor_set(v___x_4506_, 1, v_a_4497_);
                crate::leanh::lean_ctor_set(v___x_4506_, 2, v___y_4504_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_4505_,
                );
                if v_isShared_4502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4501_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4508_;
            }
            4 => {
                if v___y_4512_ == 0 {
                    if v_isRec_4493_ == 0 {
                        v___y_4504_ = v___y_4511_;
                        v___y_4505_ = v_isRec_4493_;
                        state = 2;
                        continue;
                    } else {
                        if v_supportsRec_4482_ == 0 {
                            v___y_4504_ = v___y_4511_;
                            v___y_4505_ = v_isRec_4493_;
                            state = 2;
                            continue;
                        } else {
                            v___y_4504_ = v___y_4511_;
                            v___y_4505_ = v___y_4512_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___y_4504_ = v___y_4511_;
                    v___y_4505_ = v___y_4512_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_4515_ = l_Lean_InductiveVal_isNested(v_a_4491_);
                crate::leanh::lean_dec(v_a_4491_);
                if v___x_4515_ == 0 {
                    v___x_4516_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4517_ = lean_array_get_size(v_a_4497_);
                    v___x_4518_ = lean_nat_dec_lt(v___x_4516_, v___x_4517_);
                    v___y_4511_ = v___y_4514_;
                    v___y_4512_ = v___x_4518_;
                    state = 4;
                    continue;
                } else {
                    v___y_4511_ = v___y_4514_;
                    v___y_4512_ = v___x_4515_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_options_4527_ = crate::leanh::lean_ctor_get(v___y_4525_, 2);
                v_hasTrace_4528_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4527_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4528_ == 0 {
                    v___y_4514_ = v_auxFunNames_4520_;
                    state = 5;
                    continue;
                } else {
                    v_inheritedTraceOptions_4529_ = crate::leanh::lean_ctor_get(v___y_4525_, 13);
                    v___x_4530_ = l_Lean_Elab_Deriving_mkContext___closed__2;
                    v___x_4531_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__5_once),
                        _init_l_Lean_Elab_Deriving_mkContext___closed__5,
                    );
                    v___x_4532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4529_,
                        v_options_4527_,
                        v___x_4531_,
                    );
                    if v___x_4532_ == 0 {
                        v___y_4514_ = v_auxFunNames_4520_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4533_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Deriving_mkContext___closed__7_once
                            ),
                            _init_l_Lean_Elab_Deriving_mkContext___closed__7,
                        );
                        crate::leanh::lean_inc(v_a_4499_);
                        v___x_4534_ = l_Lean_MessageData_ofName(v_a_4499_);
                        v___x_4535_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4535_, 0, v___x_4533_);
                        crate::leanh::lean_ctor_set(v___x_4535_, 1, v___x_4534_);
                        v___x_4536_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Deriving_mkContext___closed__9_once
                            ),
                            _init_l_Lean_Elab_Deriving_mkContext___closed__9,
                        );
                        v___x_4537_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4537_, 0, v___x_4535_);
                        crate::leanh::lean_ctor_set(v___x_4537_, 1, v___x_4536_);
                        crate::leanh::lean_inc_ref(v_auxFunNames_4520_);
                        v___x_4538_ = lean_array_to_list(v_auxFunNames_4520_);
                        v___x_4539_ = crate::leanh::lean_box(0);
                        v___x_4540_ =
                            l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(
                                v___x_4538_,
                                v___x_4539_,
                            );
                        v___x_4541_ = l_Lean_MessageData_ofList(v___x_4540_);
                        v___x_4542_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4537_);
                        crate::leanh::lean_ctor_set(v___x_4542_, 1, v___x_4541_);
                        v___x_4543_ =
                            l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
                                v___x_4530_,
                                v___x_4542_,
                                v___y_4523_,
                                v___y_4524_,
                                v___y_4525_,
                                v___y_4526_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4543_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4543_, 1);
                            v___y_4514_ = v_auxFunNames_4520_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_auxFunNames_4520_);
                            crate::leanh::lean_del_object(v___x_4501_);
                            crate::leanh::lean_dec(v_a_4499_);
                            crate::leanh::lean_dec(v_a_4497_);
                            crate::leanh::lean_dec(v_a_4491_);
                            v_a_4544_ = crate::leanh::lean_ctor_get(v___x_4543_, 0);
                            v_isSharedCheck_4551_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4543_)) as u8;
                            if v_isSharedCheck_4551_ == 0 {
                                v___x_4546_ = v___x_4543_;
                                v_isShared_4547_ = v_isSharedCheck_4551_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4544_);
                                crate::leanh::lean_dec(v___x_4543_);
                                v___x_4546_ = crate::leanh::lean_box(0);
                                v_isShared_4547_ = v_isSharedCheck_4551_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                if v_isShared_4547_ == 0 {
                    v___x_4549_ = v___x_4546_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
                    v___x_4549_ = v_reuseFailAlloc_4550_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4549_;
            }
            9 => {
                if v_isShared_4566_ == 0 {
                    v___x_4568_ = v___x_4565_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
                    v___x_4568_ = v_reuseFailAlloc_4569_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4568_;
            }
            11 => {
                if v_isShared_4574_ == 0 {
                    v___x_4576_ = v___x_4573_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
                    v___x_4576_ = v_reuseFailAlloc_4577_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4576_;
            }
            13 => {
                if v_isShared_4582_ == 0 {
                    v___x_4584_ = v___x_4581_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
                    v___x_4584_ = v_reuseFailAlloc_4585_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkContext___boxed(
    mut v_className_4587_: *mut crate::leanh::LeanObject,
    mut v_fnPrefix_4588_: *mut crate::leanh::LeanObject,
    mut v_typeName_4589_: *mut crate::leanh::LeanObject,
    mut v_supportsRec_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_supportsRec_boxed_4598_: u8 = 0;
    let mut v_res_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_supportsRec_boxed_4598_ = (crate::leanh::lean_unbox(v_supportsRec_4590_) as u8);
    v_res_4599_ = l_Lean_Elab_Deriving_mkContext(
        v_className_4587_,
        v_fnPrefix_4588_,
        v_typeName_4589_,
        v_supportsRec_boxed_4598_,
        v_a_4591_,
        v_a_4592_,
        v_a_4593_,
        v_a_4594_,
        v_a_4595_,
        v_a_4596_,
    );
    crate::leanh::lean_dec(v_a_4596_);
    crate::leanh::lean_dec_ref(v_a_4595_);
    crate::leanh::lean_dec(v_a_4594_);
    crate::leanh::lean_dec_ref(v_a_4593_);
    crate::leanh::lean_dec(v_a_4592_);
    crate::leanh::lean_dec_ref(v_a_4591_);
    return v_res_4599_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(
    mut v_as_4600_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4601_: *mut crate::leanh::LeanObject,
    mut v_b_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(
        v_as_x27_4601_,
        v_b_4602_,
        v___y_4604_,
        v___y_4605_,
        v___y_4606_,
        v___y_4607_,
        v___y_4608_,
        v___y_4609_,
    );
    return v___x_4611_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(
    mut v_as_4612_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4613_: *mut crate::leanh::LeanObject,
    mut v_b_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(
        v_as_4612_,
        v_as_x27_4613_,
        v_b_4614_,
        v_a_4615_,
        v___y_4616_,
        v___y_4617_,
        v___y_4618_,
        v___y_4619_,
        v___y_4620_,
        v___y_4621_,
    );
    crate::leanh::lean_dec(v___y_4621_);
    crate::leanh::lean_dec_ref(v___y_4620_);
    crate::leanh::lean_dec(v___y_4619_);
    crate::leanh::lean_dec_ref(v___y_4618_);
    crate::leanh::lean_dec(v___y_4617_);
    crate::leanh::lean_dec_ref(v___y_4616_);
    crate::leanh::lean_dec(v_as_x27_4613_);
    crate::leanh::lean_dec(v_as_4612_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(
    mut v_cls_4624_: *mut crate::leanh::LeanObject,
    mut v_msg_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
        v_cls_4624_,
        v_msg_4625_,
        v___y_4628_,
        v___y_4629_,
        v___y_4630_,
        v___y_4631_,
    );
    return v___x_4633_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(
    mut v_cls_4634_: *mut crate::leanh::LeanObject,
    mut v_msg_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
    mut v___y_4642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4643_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(
        v_cls_4634_,
        v_msg_4635_,
        v___y_4636_,
        v___y_4637_,
        v___y_4638_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
    );
    crate::leanh::lean_dec(v___y_4641_);
    crate::leanh::lean_dec_ref(v___y_4640_);
    crate::leanh::lean_dec(v___y_4639_);
    crate::leanh::lean_dec_ref(v___y_4638_);
    crate::leanh::lean_dec(v___y_4637_);
    crate::leanh::lean_dec_ref(v___y_4636_);
    return v_res_4643_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(
    mut v_fnPrefix_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_range_4646_: *mut crate::leanh::LeanObject,
    mut v_b_4647_: *mut crate::leanh::LeanObject,
    mut v_i_4648_: *mut crate::leanh::LeanObject,
    mut v_hs_4649_: *mut crate::leanh::LeanObject,
    mut v_hl_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4658_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4644_, v_a_4645_, v_range_4646_, v_b_4647_, v_i_4648_);
    return v___x_4658_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(
    mut v_fnPrefix_4659_: *mut crate::leanh::LeanObject,
    mut v_a_4660_: *mut crate::leanh::LeanObject,
    mut v_range_4661_: *mut crate::leanh::LeanObject,
    mut v_b_4662_: *mut crate::leanh::LeanObject,
    mut v_i_4663_: *mut crate::leanh::LeanObject,
    mut v_hs_4664_: *mut crate::leanh::LeanObject,
    mut v_hl_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v___y_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4673_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_4659_, v_a_4660_, v_range_4661_, v_b_4662_, v_i_4663_, v_hs_4664_, v_hl_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
    crate::leanh::lean_dec(v___y_4671_);
    crate::leanh::lean_dec_ref(v___y_4670_);
    crate::leanh::lean_dec(v___y_4669_);
    crate::leanh::lean_dec_ref(v___y_4668_);
    crate::leanh::lean_dec(v___y_4667_);
    crate::leanh::lean_dec_ref(v___y_4666_);
    crate::leanh::lean_dec_ref(v_range_4661_);
    return v_res_4673_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(
    mut v_a_4674_: *mut crate::leanh::LeanObject,
    mut v_b_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4676_ = crate::leanh::lean_ctor_get(v_a_4674_, 0);
                v_start_4677_ = crate::leanh::lean_ctor_get(v_a_4674_, 1);
                v_stop_4678_ = crate::leanh::lean_ctor_get(v_a_4674_, 2);
                v_isSharedCheck_4691_ = (!crate::leanh::lean_is_exclusive(v_a_4674_)) as u8;
                if v_isSharedCheck_4691_ == 0 {
                    v___x_4680_ = v_a_4674_;
                    v_isShared_4681_ = v_isSharedCheck_4691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_4678_);
                    crate::leanh::lean_inc(v_start_4677_);
                    crate::leanh::lean_inc(v_array_4676_);
                    crate::leanh::lean_dec(v_a_4674_);
                    v___x_4680_ = crate::leanh::lean_box(0);
                    v_isShared_4681_ = v_isSharedCheck_4691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4682_ = lean_nat_dec_lt(v_start_4677_, v_stop_4678_);
                if v___x_4682_ == 0 {
                    crate::leanh::lean_del_object(v___x_4680_);
                    crate::leanh::lean_dec(v_stop_4678_);
                    crate::leanh::lean_dec(v_start_4677_);
                    crate::leanh::lean_dec_ref(v_array_4676_);
                    return v_b_4675_;
                } else {
                    v___x_4683_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4684_ = lean_nat_add(v_start_4677_, v___x_4683_);
                    crate::leanh::lean_inc_ref(v_array_4676_);
                    if v_isShared_4681_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4684_);
                        v___x_4686_ = v___x_4680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4690_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_array_4676_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 1, v___x_4684_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_stop_4678_);
                        v___x_4686_ = v_reuseFailAlloc_4690_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4687_ = lean_array_fget(v_array_4676_, v_start_4677_);
                crate::leanh::lean_dec(v_start_4677_);
                crate::leanh::lean_dec_ref(v_array_4676_);
                v___x_4688_ = lean_array_push(v_b_4675_, v___x_4687_);
                v_a_4674_ = v___x_4686_;
                v_b_4675_ = v___x_4688_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4699_ = crate::leanh::lean_ctor_get(v___y_4696_, 5);
    v___x_4700_ = 0;
    v___x_4701_ = l_Lean_SourceInfo_fromRef(v_ref_4699_, v___x_4700_);
    v___x_4702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4702_, 0, v___x_4701_);
    return v___x_4702_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
    crate::leanh::lean_dec(v___y_4708_);
    crate::leanh::lean_dec_ref(v___y_4707_);
    crate::leanh::lean_dec(v___y_4706_);
    crate::leanh::lean_dec_ref(v___y_4705_);
    crate::leanh::lean_dec(v___y_4704_);
    crate::leanh::lean_dec_ref(v___y_4703_);
    return v_res_4710_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(
    mut v_upperBound_4748_: *mut crate::leanh::LeanObject,
    mut v___x_4749_: *mut crate::leanh::LeanObject,
    mut v_ctx_4750_: *mut crate::leanh::LeanObject,
    mut v_argNames_4751_: *mut crate::leanh::LeanObject,
    mut v_className_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
    mut v_b_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4762_: u8 = 0;
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: u8 = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4840_: u8 = 0;
    let mut v_a_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_a_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4864_: u8 = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u8 = 0;
    let mut v_a_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4871_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4762_ = lean_nat_dec_lt(v_a_4753_, v_upperBound_4748_);
                if v___x_4762_ == 0 {
                    crate::leanh::lean_dec(v_a_4753_);
                    crate::leanh::lean_dec(v_className_4752_);
                    crate::leanh::lean_dec_ref(v_argNames_4751_);
                    v___x_4763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4763_, 0, v_b_4754_);
                    return v___x_4763_;
                } else {
                    v___x_4764_ = lean_array_fget_borrowed(v___x_4749_, v_a_4753_);
                    crate::leanh::lean_inc(v___x_4764_);
                    v___x_4765_ = l_Lean_Elab_Deriving_mkInductArgNames(
                        v___x_4764_,
                        v___y_4755_,
                        v___y_4756_,
                        v___y_4757_,
                        v___y_4758_,
                        v___y_4759_,
                        v___y_4760_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4765_) == 0 {
                        v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4765_, 0);
                        crate::leanh::lean_inc(v_a_4766_);
                        crate::leanh::lean_dec_ref_known(v___x_4765_, 1);
                        v_auxFunNames_4767_ = crate::leanh::lean_ctor_get(v_ctx_4750_, 2);
                        v_numParams_4768_ = crate::leanh::lean_ctor_get(v___x_4764_, 1);
                        v___x_4769_ = crate::leanh::lean_box(0);
                        v___x_4770_ =
                            lean_array_get_borrowed(v___x_4769_, v_auxFunNames_4767_, v_a_4753_);
                        v___x_4865_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4866_ = lean_array_get_size(v_a_4766_);
                        v___x_4867_ = lean_nat_dec_le(v_numParams_4768_, v___x_4865_);
                        if v___x_4867_ == 0 {
                            crate::leanh::lean_inc(v_numParams_4768_);
                            v_lower_4772_ = v_numParams_4768_;
                            v_upper_4773_ = v___x_4866_;
                            state = 1;
                            continue;
                        } else {
                            v_lower_4772_ = v___x_4865_;
                            v_upper_4773_ = v___x_4866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4754_);
                        crate::leanh::lean_dec(v_a_4753_);
                        crate::leanh::lean_dec(v_className_4752_);
                        crate::leanh::lean_dec_ref(v_argNames_4751_);
                        v_a_4868_ = crate::leanh::lean_ctor_get(v___x_4765_, 0);
                        v_isSharedCheck_4875_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4765_)) as u8;
                        if v_isSharedCheck_4875_ == 0 {
                            v___x_4870_ = v___x_4765_;
                            v_isShared_4871_ = v_isSharedCheck_4875_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4868_);
                            crate::leanh::lean_dec(v___x_4765_);
                            v___x_4870_ = crate::leanh::lean_box(0);
                            v_isShared_4871_ = v_isSharedCheck_4875_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4774_ = l_Array_toSubarray___redArg(v_a_4766_, v_lower_4772_, v_upper_4773_);
                crate::leanh::lean_inc_ref(v___x_4774_);
                v___x_4775_ = l_Subarray_copy___redArg(v___x_4774_);
                v___x_4776_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                    v___x_4775_,
                    v___y_4755_,
                    v___y_4756_,
                    v___y_4757_,
                    v___y_4758_,
                    v___y_4759_,
                    v___y_4760_,
                );
                if crate::leanh::lean_obj_tag(v___x_4776_) == 0 {
                    v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                    crate::leanh::lean_inc(v_a_4777_);
                    crate::leanh::lean_dec_ref_known(v___x_4776_, 1);
                    v___x_4778_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_numParams_4768_);
                    crate::leanh::lean_inc_ref(v_argNames_4751_);
                    v___x_4779_ = l_Array_toSubarray___redArg(
                        v_argNames_4751_,
                        v___x_4778_,
                        v_numParams_4768_,
                    );
                    v___x_4780_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
                    v___x_4781_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_4779_, v___x_4780_);
                    v___x_4782_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_4774_, v___x_4780_);
                    v_a_4783_ = l_Array_append___redArg(v___x_4781_, v___x_4782_);
                    crate::leanh::lean_dec_ref(v___x_4782_);
                    v___x_4784_ = lean_array_get_size(v_a_4783_);
                    v___x_4785_ = l_Array_toSubarray___redArg(v_a_4783_, v___x_4778_, v___x_4784_);
                    v___x_4786_ = l_Subarray_copy___redArg(v___x_4785_);
                    crate::leanh::lean_inc(v___x_4764_);
                    v___x_4787_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                        v___x_4764_,
                        v___x_4786_,
                        v___y_4759_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4787_) == 0 {
                        v_a_4788_ = crate::leanh::lean_ctor_get(v___x_4787_, 0);
                        crate::leanh::lean_inc(v_a_4788_);
                        crate::leanh::lean_dec_ref_known(v___x_4787_, 1);
                        v_ref_4789_ = crate::leanh::lean_ctor_get(v___y_4759_, 5);
                        v___x_4790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
                        if crate::leanh::lean_obj_tag(v___x_4790_) == 0 {
                            v_a_4791_ = crate::leanh::lean_ctor_get(v___x_4790_, 0);
                            crate::leanh::lean_inc(v_a_4791_);
                            crate::leanh::lean_dec_ref_known(v___x_4790_, 1);
                            v___x_4792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1;
                            v___x_4793_ =
                                l_Lean_Core_mkFreshUserName(v___x_4792_, v___y_4759_, v___y_4760_);
                            if crate::leanh::lean_obj_tag(v___x_4793_) == 0 {
                                v_a_4794_ = crate::leanh::lean_ctor_get(v___x_4793_, 0);
                                crate::leanh::lean_inc(v_a_4794_);
                                crate::leanh::lean_dec_ref_known(v___x_4793_, 1);
                                v___x_4795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
                                if crate::leanh::lean_obj_tag(v___x_4795_) == 0 {
                                    v_a_4796_ = crate::leanh::lean_ctor_get(v___x_4795_, 0);
                                    crate::leanh::lean_inc_n(v_a_4796_, 8);
                                    crate::leanh::lean_dec_ref_known(v___x_4795_, 1);
                                    v___x_4797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2;
                                    crate::leanh::lean_inc_n(v_a_4791_, 3);
                                    v___x_4798_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4798_, 0, v_a_4791_);
                                    crate::leanh::lean_ctor_set(v___x_4798_, 1, v___x_4797_);
                                    v___x_4799_ =
                                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                    crate::leanh::lean_inc(v___x_4770_);
                                    v___x_4800_ = lean_mk_syntax_ident(v___x_4770_);
                                    v___x_4801_ =
                                        l_Lean_Syntax_node1(v_a_4791_, v___x_4799_, v___x_4800_);
                                    v___x_4802_ = 0;
                                    v___x_4803_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4789_, v___x_4802_);
                                    crate::leanh::lean_inc(v___x_4803_);
                                    v___x_4804_ =
                                        l_Lean_Syntax_node1(v___x_4803_, v___x_4799_, v_a_4788_);
                                    v___x_4805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3;
                                    v___x_4806_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4806_, 0, v_a_4791_);
                                    crate::leanh::lean_ctor_set(v___x_4806_, 1, v___x_4805_);
                                    v___x_4807_ =
                                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                    crate::leanh::lean_inc(v_className_4752_);
                                    v___x_4808_ = l_Lean_mkCIdent(v_className_4752_);
                                    v___x_4809_ = l_Lean_Syntax_node2(
                                        v___x_4803_,
                                        v___x_4807_,
                                        v___x_4808_,
                                        v___x_4804_,
                                    );
                                    v___x_4810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5;
                                    v___x_4811_ = l_Lean_Syntax_node3(
                                        v_a_4791_,
                                        v___x_4810_,
                                        v___x_4798_,
                                        v___x_4801_,
                                        v___x_4806_,
                                    );
                                    v___x_4812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7;
                                    v___x_4813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9;
                                    v___x_4814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11;
                                    v___x_4815_ = lean_mk_syntax_ident(v_a_4794_);
                                    v___x_4816_ =
                                        l_Lean_Syntax_node1(v_a_4796_, v___x_4814_, v___x_4815_);
                                    v___x_4817_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once), _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
                                    v___x_4818_ = l_Array_append___redArg(v___x_4817_, v_a_4777_);
                                    crate::leanh::lean_dec(v_a_4777_);
                                    v___x_4819_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4819_, 0, v_a_4796_);
                                    crate::leanh::lean_ctor_set(v___x_4819_, 1, v___x_4799_);
                                    crate::leanh::lean_ctor_set(v___x_4819_, 2, v___x_4818_);
                                    v___x_4820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13;
                                    v___x_4821_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                                    v___x_4822_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4822_, 0, v_a_4796_);
                                    crate::leanh::lean_ctor_set(v___x_4822_, 1, v___x_4821_);
                                    v___x_4823_ = l_Lean_Syntax_node2(
                                        v_a_4796_,
                                        v___x_4820_,
                                        v___x_4822_,
                                        v___x_4809_,
                                    );
                                    v___x_4824_ =
                                        l_Lean_Syntax_node1(v_a_4796_, v___x_4799_, v___x_4823_);
                                    v___x_4825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15;
                                    v___x_4826_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4826_, 0, v_a_4796_);
                                    crate::leanh::lean_ctor_set(v___x_4826_, 1, v___x_4825_);
                                    v___x_4827_ = l_Lean_Syntax_node5(
                                        v_a_4796_,
                                        v___x_4813_,
                                        v___x_4816_,
                                        v___x_4819_,
                                        v___x_4824_,
                                        v___x_4826_,
                                        v___x_4811_,
                                    );
                                    v___x_4828_ =
                                        l_Lean_Syntax_node1(v_a_4796_, v___x_4812_, v___x_4827_);
                                    v___x_4829_ = lean_array_push(v_b_4754_, v___x_4828_);
                                    v___x_4830_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_4831_ = lean_nat_add(v_a_4753_, v___x_4830_);
                                    crate::leanh::lean_dec(v_a_4753_);
                                    v_a_4753_ = v___x_4831_;
                                    v_b_4754_ = v___x_4829_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4794_);
                                    crate::leanh::lean_dec(v_a_4791_);
                                    crate::leanh::lean_dec(v_a_4788_);
                                    crate::leanh::lean_dec(v_a_4777_);
                                    crate::leanh::lean_dec_ref(v_b_4754_);
                                    crate::leanh::lean_dec(v_a_4753_);
                                    crate::leanh::lean_dec(v_className_4752_);
                                    crate::leanh::lean_dec_ref(v_argNames_4751_);
                                    v_a_4833_ = crate::leanh::lean_ctor_get(v___x_4795_, 0);
                                    v_isSharedCheck_4840_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4795_)) as u8;
                                    if v_isSharedCheck_4840_ == 0 {
                                        v___x_4835_ = v___x_4795_;
                                        v_isShared_4836_ = v_isSharedCheck_4840_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4833_);
                                        crate::leanh::lean_dec(v___x_4795_);
                                        v___x_4835_ = crate::leanh::lean_box(0);
                                        v_isShared_4836_ = v_isSharedCheck_4840_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4791_);
                                crate::leanh::lean_dec(v_a_4788_);
                                crate::leanh::lean_dec(v_a_4777_);
                                crate::leanh::lean_dec_ref(v_b_4754_);
                                crate::leanh::lean_dec(v_a_4753_);
                                crate::leanh::lean_dec(v_className_4752_);
                                crate::leanh::lean_dec_ref(v_argNames_4751_);
                                v_a_4841_ = crate::leanh::lean_ctor_get(v___x_4793_, 0);
                                v_isSharedCheck_4848_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4793_)) as u8;
                                if v_isSharedCheck_4848_ == 0 {
                                    v___x_4843_ = v___x_4793_;
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4841_);
                                    crate::leanh::lean_dec(v___x_4793_);
                                    v___x_4843_ = crate::leanh::lean_box(0);
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4788_);
                            crate::leanh::lean_dec(v_a_4777_);
                            crate::leanh::lean_dec_ref(v_b_4754_);
                            crate::leanh::lean_dec(v_a_4753_);
                            crate::leanh::lean_dec(v_className_4752_);
                            crate::leanh::lean_dec_ref(v_argNames_4751_);
                            v_a_4849_ = crate::leanh::lean_ctor_get(v___x_4790_, 0);
                            v_isSharedCheck_4856_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4790_)) as u8;
                            if v_isSharedCheck_4856_ == 0 {
                                v___x_4851_ = v___x_4790_;
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4849_);
                                crate::leanh::lean_dec(v___x_4790_);
                                v___x_4851_ = crate::leanh::lean_box(0);
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4777_);
                        crate::leanh::lean_dec_ref(v_b_4754_);
                        crate::leanh::lean_dec(v_a_4753_);
                        crate::leanh::lean_dec(v_className_4752_);
                        crate::leanh::lean_dec_ref(v_argNames_4751_);
                        v_a_4857_ = crate::leanh::lean_ctor_get(v___x_4787_, 0);
                        v_isSharedCheck_4864_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4787_)) as u8;
                        if v_isSharedCheck_4864_ == 0 {
                            v___x_4859_ = v___x_4787_;
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4857_);
                            crate::leanh::lean_dec(v___x_4787_);
                            v___x_4859_ = crate::leanh::lean_box(0);
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4774_);
                    crate::leanh::lean_dec_ref(v_b_4754_);
                    crate::leanh::lean_dec(v_a_4753_);
                    crate::leanh::lean_dec(v_className_4752_);
                    crate::leanh::lean_dec_ref(v_argNames_4751_);
                    return v___x_4776_;
                }
            }
            2 => {
                if v_isShared_4836_ == 0 {
                    v___x_4838_ = v___x_4835_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
                    v___x_4838_ = v_reuseFailAlloc_4839_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4838_;
            }
            4 => {
                if v_isShared_4844_ == 0 {
                    v___x_4846_ = v___x_4843_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
                    v___x_4846_ = v_reuseFailAlloc_4847_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4846_;
            }
            6 => {
                if v_isShared_4852_ == 0 {
                    v___x_4854_ = v___x_4851_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
                    v___x_4854_ = v_reuseFailAlloc_4855_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4854_;
            }
            8 => {
                if v_isShared_4860_ == 0 {
                    v___x_4862_ = v___x_4859_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
                    v___x_4862_ = v_reuseFailAlloc_4863_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4862_;
            }
            10 => {
                if v_isShared_4871_ == 0 {
                    v___x_4873_ = v___x_4870_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
                    v___x_4873_ = v_reuseFailAlloc_4874_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(
    mut v_upperBound_4876_: *mut crate::leanh::LeanObject,
    mut v___x_4877_: *mut crate::leanh::LeanObject,
    mut v_ctx_4878_: *mut crate::leanh::LeanObject,
    mut v_argNames_4879_: *mut crate::leanh::LeanObject,
    mut v_className_4880_: *mut crate::leanh::LeanObject,
    mut v_a_4881_: *mut crate::leanh::LeanObject,
    mut v_b_4882_: *mut crate::leanh::LeanObject,
    mut v___y_4883_: *mut crate::leanh::LeanObject,
    mut v___y_4884_: *mut crate::leanh::LeanObject,
    mut v___y_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_4876_, v___x_4877_, v_ctx_4878_, v_argNames_4879_, v_className_4880_, v_a_4881_, v_b_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
    crate::leanh::lean_dec(v___y_4888_);
    crate::leanh::lean_dec_ref(v___y_4887_);
    crate::leanh::lean_dec(v___y_4886_);
    crate::leanh::lean_dec_ref(v___y_4885_);
    crate::leanh::lean_dec(v___y_4884_);
    crate::leanh::lean_dec_ref(v___y_4883_);
    crate::leanh::lean_dec_ref(v_ctx_4878_);
    crate::leanh::lean_dec_ref(v___x_4877_);
    crate::leanh::lean_dec(v_upperBound_4876_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(
    mut v_ctx_4891_: *mut crate::leanh::LeanObject,
    mut v_className_4892_: *mut crate::leanh::LeanObject,
    mut v_argNames_4893_: *mut crate::leanh::LeanObject,
    mut v_a_4894_: *mut crate::leanh::LeanObject,
    mut v_a_4895_: *mut crate::leanh::LeanObject,
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_a_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDecls_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_typeInfos_4901_ = crate::leanh::lean_ctor_get(v_ctx_4891_, 1);
    v___x_4902_ = lean_array_get_size(v_typeInfos_4901_);
    v___x_4903_ = crate::leanh::lean_unsigned_to_nat(0);
    v_letDecls_4904_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
    v___x_4905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_4902_, v_typeInfos_4901_, v_ctx_4891_, v_argNames_4893_, v_className_4892_, v___x_4903_, v_letDecls_4904_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(
    mut v_ctx_4906_: *mut crate::leanh::LeanObject,
    mut v_className_4907_: *mut crate::leanh::LeanObject,
    mut v_argNames_4908_: *mut crate::leanh::LeanObject,
    mut v_a_4909_: *mut crate::leanh::LeanObject,
    mut v_a_4910_: *mut crate::leanh::LeanObject,
    mut v_a_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
    mut v_a_4914_: *mut crate::leanh::LeanObject,
    mut v_a_4915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4916_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(
        v_ctx_4906_,
        v_className_4907_,
        v_argNames_4908_,
        v_a_4909_,
        v_a_4910_,
        v_a_4911_,
        v_a_4912_,
        v_a_4913_,
        v_a_4914_,
    );
    crate::leanh::lean_dec(v_a_4914_);
    crate::leanh::lean_dec_ref(v_a_4913_);
    crate::leanh::lean_dec(v_a_4912_);
    crate::leanh::lean_dec_ref(v_a_4911_);
    crate::leanh::lean_dec(v_a_4910_);
    crate::leanh::lean_dec_ref(v_a_4909_);
    crate::leanh::lean_dec_ref(v_ctx_4906_);
    return v_res_4916_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(
    mut v_inst_4917_: *mut crate::leanh::LeanObject,
    mut v_R_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_b_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4921_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_4919_, v_b_4920_);
    return v___x_4921_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(
    mut v_upperBound_4922_: *mut crate::leanh::LeanObject,
    mut v___x_4923_: *mut crate::leanh::LeanObject,
    mut v_ctx_4924_: *mut crate::leanh::LeanObject,
    mut v_argNames_4925_: *mut crate::leanh::LeanObject,
    mut v_className_4926_: *mut crate::leanh::LeanObject,
    mut v_inst_4927_: *mut crate::leanh::LeanObject,
    mut v_R_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_b_4930_: *mut crate::leanh::LeanObject,
    mut v_c_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_4922_, v___x_4923_, v_ctx_4924_, v_argNames_4925_, v_className_4926_, v_a_4929_, v_b_4930_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
    return v___x_4939_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_4940_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_4941_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_ctx_4942_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_argNames_4943_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_className_4944_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_4945_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_R_4946_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4947_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_4948_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_c_4949_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4950_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4951_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4952_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4953_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4954_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4955_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4956_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(
            v_upperBound_4940_,
            v___x_4941_,
            v_ctx_4942_,
            v_argNames_4943_,
            v_className_4944_,
            v_inst_4945_,
            v_R_4946_,
            v_a_4947_,
            v_b_4948_,
            v_c_4949_,
            v___y_4950_,
            v___y_4951_,
            v___y_4952_,
            v___y_4953_,
            v___y_4954_,
            v___y_4955_,
        );
    crate::leanh::lean_dec(v___y_4955_);
    crate::leanh::lean_dec_ref(v___y_4954_);
    crate::leanh::lean_dec(v___y_4953_);
    crate::leanh::lean_dec_ref(v___y_4952_);
    crate::leanh::lean_dec(v___y_4951_);
    crate::leanh::lean_dec_ref(v___y_4950_);
    crate::leanh::lean_dec_ref(v_ctx_4942_);
    crate::leanh::lean_dec_ref(v___x_4941_);
    crate::leanh::lean_dec(v_upperBound_4940_);
    return v_res_4957_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(
    mut v_as_4971_: *mut crate::leanh::LeanObject,
    mut v_i_4972_: usize,
    mut v_stop_4973_: usize,
    mut v_b_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4977_: u8 = 0;
    let mut v_ref_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = lean_usize_dec_eq(v_i_4972_, v_stop_4973_);
                if v___x_4977_ == 0 {
                    v_ref_4978_ = crate::leanh::lean_ctor_get(v___y_4975_, 5);
                    v___x_4979_ = 1usize;
                    v___x_4980_ = lean_usize_sub(v_i_4972_, v___x_4979_);
                    v___x_4981_ = lean_array_uget_borrowed(v_as_4971_, v___x_4980_);
                    v___x_4982_ = l_Lean_SourceInfo_fromRef(v_ref_4978_, v___x_4977_);
                    v___x_4983_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0;
                    v___x_4984_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1;
                    crate::leanh::lean_inc_n(v___x_4982_, 4);
                    v___x_4985_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4985_, 0, v___x_4982_);
                    crate::leanh::lean_ctor_set(v___x_4985_, 1, v___x_4983_);
                    v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3;
                    v___x_4987_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_4988_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_4989_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4989_, 0, v___x_4982_);
                    crate::leanh::lean_ctor_set(v___x_4989_, 1, v___x_4987_);
                    crate::leanh::lean_ctor_set(v___x_4989_, 2, v___x_4988_);
                    v___x_4990_ = l_Lean_Syntax_node1(v___x_4982_, v___x_4986_, v___x_4989_);
                    v___x_4991_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4;
                    v___x_4992_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_4982_);
                    crate::leanh::lean_ctor_set(v___x_4992_, 1, v___x_4991_);
                    crate::leanh::lean_inc(v___x_4981_);
                    v___x_4993_ = l_Lean_Syntax_node5(
                        v___x_4982_,
                        v___x_4984_,
                        v___x_4985_,
                        v___x_4990_,
                        v___x_4981_,
                        v___x_4992_,
                        v_b_4974_,
                    );
                    v_i_4972_ = v___x_4980_;
                    v_b_4974_ = v___x_4993_;
                    state = 0;
                    continue;
                } else {
                    v___x_4995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4995_, 0, v_b_4974_);
                    return v___x_4995_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(
    mut v_as_4996_: *mut crate::leanh::LeanObject,
    mut v_i_4997_: *mut crate::leanh::LeanObject,
    mut v_stop_4998_: *mut crate::leanh::LeanObject,
    mut v_b_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5002_: usize = 0;
    let mut v_stop_boxed_5003_: usize = 0;
    let mut v_res_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5002_ = crate::leanh::lean_unbox_usize(v_i_4997_);
    crate::leanh::lean_dec(v_i_4997_);
    v_stop_boxed_5003_ = crate::leanh::lean_unbox_usize(v_stop_4998_);
    crate::leanh::lean_dec(v_stop_4998_);
    v_res_5004_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_4996_, v_i_boxed_5002_, v_stop_boxed_5003_, v_b_4999_, v___y_5000_);
    crate::leanh::lean_dec_ref(v___y_5000_);
    crate::leanh::lean_dec_ref(v_as_4996_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLet(
    mut v_letDecls_5005_: *mut crate::leanh::LeanObject,
    mut v_body_5006_: *mut crate::leanh::LeanObject,
    mut v_a_5007_: *mut crate::leanh::LeanObject,
    mut v_a_5008_: *mut crate::leanh::LeanObject,
    mut v_a_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
    mut v_a_5011_: *mut crate::leanh::LeanObject,
    mut v_a_5012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    v___x_5014_ = lean_array_get_size(v_letDecls_5005_);
    v___x_5015_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5016_ = lean_nat_dec_lt(v___x_5015_, v___x_5014_);
    if v___x_5016_ == 0 {
        let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5017_, 0, v_body_5006_);
        return v___x_5017_;
    } else {
        let mut v___x_5018_: usize = 0;
        let mut v___x_5019_: usize = 0;
        let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5018_ = lean_usize_of_nat(v___x_5014_);
        v___x_5019_ = 0usize;
        v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_5005_, v___x_5018_, v___x_5019_, v_body_5006_, v_a_5011_);
        return v___x_5020_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkLet___boxed(
    mut v_letDecls_5021_: *mut crate::leanh::LeanObject,
    mut v_body_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
    mut v_a_5025_: *mut crate::leanh::LeanObject,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
    mut v_a_5027_: *mut crate::leanh::LeanObject,
    mut v_a_5028_: *mut crate::leanh::LeanObject,
    mut v_a_5029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5030_ = l_Lean_Elab_Deriving_mkLet(
        v_letDecls_5021_,
        v_body_5022_,
        v_a_5023_,
        v_a_5024_,
        v_a_5025_,
        v_a_5026_,
        v_a_5027_,
        v_a_5028_,
    );
    crate::leanh::lean_dec(v_a_5028_);
    crate::leanh::lean_dec_ref(v_a_5027_);
    crate::leanh::lean_dec(v_a_5026_);
    crate::leanh::lean_dec_ref(v_a_5025_);
    crate::leanh::lean_dec(v_a_5024_);
    crate::leanh::lean_dec_ref(v_a_5023_);
    crate::leanh::lean_dec_ref(v_letDecls_5021_);
    return v_res_5030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(
    mut v_as_5031_: *mut crate::leanh::LeanObject,
    mut v_i_5032_: usize,
    mut v_stop_5033_: usize,
    mut v_b_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_5031_, v_i_5032_, v_stop_5033_, v_b_5034_, v___y_5039_);
    return v___x_5042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(
    mut v_as_5043_: *mut crate::leanh::LeanObject,
    mut v_i_5044_: *mut crate::leanh::LeanObject,
    mut v_stop_5045_: *mut crate::leanh::LeanObject,
    mut v_b_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5054_: usize = 0;
    let mut v_stop_boxed_5055_: usize = 0;
    let mut v_res_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5054_ = crate::leanh::lean_unbox_usize(v_i_5044_);
    crate::leanh::lean_dec(v_i_5044_);
    v_stop_boxed_5055_ = crate::leanh::lean_unbox_usize(v_stop_5045_);
    crate::leanh::lean_dec(v_stop_5045_);
    v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_5043_, v_i_boxed_5054_, v_stop_boxed_5055_, v_b_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec_ref(v___y_5051_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v___y_5049_);
    crate::leanh::lean_dec(v___y_5048_);
    crate::leanh::lean_dec_ref(v___y_5047_);
    crate::leanh::lean_dec_ref(v_as_5043_);
    return v_res_5056_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(
    mut v___f_5066_: *mut crate::leanh::LeanObject,
    mut v___x_5067_: *mut crate::leanh::LeanObject,
    mut v___x_5068_: *mut crate::leanh::LeanObject,
    mut v___x_5069_: *mut crate::leanh::LeanObject,
    mut v___x_5070_: *mut crate::leanh::LeanObject,
    mut v_instName_5071_: *mut crate::leanh::LeanObject,
    mut v___x_5072_: *mut crate::leanh::LeanObject,
    mut v___x_5073_: *mut crate::leanh::LeanObject,
    mut v_b_5074_: *mut crate::leanh::LeanObject,
    mut v_____r_5075_: *mut crate::leanh::LeanObject,
    mut v_val_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v_a_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5082_);
                crate::leanh::lean_inc_ref(v___y_5081_);
                crate::leanh::lean_inc(v___y_5080_);
                crate::leanh::lean_inc_ref(v___y_5079_);
                crate::leanh::lean_inc(v___y_5078_);
                crate::leanh::lean_inc_ref(v___y_5077_);
                v___x_5084_ = crate::leanh::lean_apply_7(
                    v___f_5066_,
                    v___y_5077_,
                    v___y_5078_,
                    v___y_5079_,
                    v___y_5080_,
                    v___y_5081_,
                    v___y_5082_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5084_) == 0 {
                    v_a_5085_ = crate::leanh::lean_ctor_get(v___x_5084_, 0);
                    v_isSharedCheck_5134_ = (!crate::leanh::lean_is_exclusive(v___x_5084_)) as u8;
                    if v_isSharedCheck_5134_ == 0 {
                        v___x_5087_ = v___x_5084_;
                        v_isShared_5088_ = v_isSharedCheck_5134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5085_);
                        crate::leanh::lean_dec(v___x_5084_);
                        v___x_5087_ = crate::leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_5076_);
                    crate::leanh::lean_dec_ref(v_b_5074_);
                    crate::leanh::lean_dec(v___x_5073_);
                    crate::leanh::lean_dec(v_instName_5071_);
                    crate::leanh::lean_dec_ref(v___x_5070_);
                    crate::leanh::lean_dec(v___x_5069_);
                    crate::leanh::lean_dec_ref(v___x_5068_);
                    crate::leanh::lean_dec_ref(v___x_5067_);
                    v_a_5135_ = crate::leanh::lean_ctor_get(v___x_5084_, 0);
                    v_isSharedCheck_5142_ = (!crate::leanh::lean_is_exclusive(v___x_5084_)) as u8;
                    if v_isSharedCheck_5142_ == 0 {
                        v___x_5137_ = v___x_5084_;
                        v_isShared_5138_ = v_isSharedCheck_5142_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5135_);
                        crate::leanh::lean_dec(v___x_5084_);
                        v___x_5137_ = crate::leanh::lean_box(0);
                        v_isShared_5138_ = v_isSharedCheck_5142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0;
                v___x_5090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1;
                crate::leanh::lean_inc_ref_n(v___x_5068_, 8);
                crate::leanh::lean_inc_ref_n(v___x_5067_, 8);
                v___x_5091_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5090_);
                v___x_5092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2;
                v___x_5093_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5092_);
                v___x_5094_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                );
                crate::leanh::lean_inc_n(v___x_5069_, 2);
                crate::leanh::lean_inc_n(v_a_5085_, 14);
                v___x_5095_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5095_, 0, v_a_5085_);
                crate::leanh::lean_ctor_set(v___x_5095_, 1, v___x_5069_);
                crate::leanh::lean_ctor_set(v___x_5095_, 2, v___x_5094_);
                crate::leanh::lean_inc_ref_n(v___x_5095_, 12);
                v___x_5096_ = l_Lean_Syntax_node7(
                    v_a_5085_,
                    v___x_5093_,
                    v___x_5095_,
                    v___x_5095_,
                    v___x_5095_,
                    v___x_5095_,
                    v___x_5095_,
                    v___x_5095_,
                    v___x_5095_,
                );
                v___x_5097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3;
                v___x_5098_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5097_);
                v___x_5099_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2;
                crate::leanh::lean_inc_ref(v___x_5070_);
                v___x_5100_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5070_, v___x_5099_);
                v___x_5101_ = l_Lean_Syntax_node1(v_a_5085_, v___x_5100_, v___x_5095_);
                v___x_5102_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5102_, 0, v_a_5085_);
                crate::leanh::lean_ctor_set(v___x_5102_, 1, v___x_5097_);
                v___x_5103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4;
                v___x_5104_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5103_);
                v___x_5105_ = lean_mk_syntax_ident(v_instName_5071_);
                v___x_5106_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5104_, v___x_5105_, v___x_5095_);
                v___x_5107_ = l_Lean_Syntax_node1(v_a_5085_, v___x_5069_, v___x_5106_);
                v___x_5108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5;
                v___x_5109_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5108_);
                v___x_5110_ = l_Array_append___redArg(v___x_5094_, v___x_5072_);
                v___x_5111_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5111_, 0, v_a_5085_);
                crate::leanh::lean_ctor_set(v___x_5111_, 1, v___x_5069_);
                crate::leanh::lean_ctor_set(v___x_5111_, 2, v___x_5110_);
                v___x_5112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12;
                v___x_5113_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5070_, v___x_5112_);
                v___x_5114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                v___x_5115_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5115_, 0, v_a_5085_);
                crate::leanh::lean_ctor_set(v___x_5115_, 1, v___x_5114_);
                v___x_5116_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5113_, v___x_5115_, v___x_5073_);
                v___x_5117_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5109_, v___x_5111_, v___x_5116_);
                v___x_5118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6;
                v___x_5119_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5118_);
                v___x_5120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15;
                v___x_5121_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5121_, 0, v_a_5085_);
                crate::leanh::lean_ctor_set(v___x_5121_, 1, v___x_5120_);
                v___x_5122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7;
                v___x_5123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8;
                v___x_5124_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5122_, v___x_5123_);
                v___x_5125_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5124_, v___x_5095_, v___x_5095_);
                v___x_5126_ = l_Lean_Syntax_node4(
                    v_a_5085_,
                    v___x_5119_,
                    v___x_5121_,
                    v_val_5076_,
                    v___x_5125_,
                    v___x_5095_,
                );
                v___x_5127_ = l_Lean_Syntax_node6(
                    v_a_5085_,
                    v___x_5098_,
                    v___x_5101_,
                    v___x_5102_,
                    v___x_5095_,
                    v___x_5107_,
                    v___x_5117_,
                    v___x_5126_,
                );
                v___x_5128_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5091_, v___x_5096_, v___x_5127_);
                v___x_5129_ = lean_array_push(v_b_5074_, v___x_5128_);
                v___x_5130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5130_, 0, v___x_5129_);
                if v_isShared_5088_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5130_);
                    v___x_5132_ = v___x_5087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5130_);
                    v___x_5132_ = v_reuseFailAlloc_5133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5132_;
            }
            3 => {
                if v_isShared_5138_ == 0 {
                    v___x_5140_ = v___x_5137_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
                    v___x_5140_ = v_reuseFailAlloc_5141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5143_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5144_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5145_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5146_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5147_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_instName_5148_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5149_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5150_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_5151_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_____r_5152_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_val_5153_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5154_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5155_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5156_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5157_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5158_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5159_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5160_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5143_, v___x_5144_, v___x_5145_, v___x_5146_, v___x_5147_, v_instName_5148_, v___x_5149_, v___x_5150_, v_b_5151_, v_____r_5152_, v_val_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
    crate::leanh::lean_dec(v___y_5159_);
    crate::leanh::lean_dec_ref(v___y_5158_);
    crate::leanh::lean_dec(v___y_5157_);
    crate::leanh::lean_dec_ref(v___y_5156_);
    crate::leanh::lean_dec(v___y_5155_);
    crate::leanh::lean_dec_ref(v___y_5154_);
    crate::leanh::lean_dec_ref(v___x_5149_);
    return v_res_5161_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(
    mut v_a_5162_: *mut crate::leanh::LeanObject,
    mut v_as_5163_: *mut crate::leanh::LeanObject,
    mut v_i_5164_: usize,
    mut v_stop_5165_: usize,
) -> u8 {
    let mut v___x_5166_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: u8 = 0;
    let mut v___x_5169_: usize = 0;
    let mut v___x_5170_: usize = 0;
    let mut v___x_5172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5166_ = lean_usize_dec_eq(v_i_5164_, v_stop_5165_);
                if v___x_5166_ == 0 {
                    v___x_5167_ = lean_array_uget_borrowed(v_as_5163_, v_i_5164_);
                    v___x_5168_ = lean_name_eq(v_a_5162_, v___x_5167_);
                    if v___x_5168_ == 0 {
                        v___x_5169_ = 1usize;
                        v___x_5170_ = lean_usize_add(v_i_5164_, v___x_5169_);
                        v_i_5164_ = v___x_5170_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5168_;
                    }
                } else {
                    v___x_5172_ = 0;
                    return v___x_5172_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(
    mut v_a_5173_: *mut crate::leanh::LeanObject,
    mut v_as_5174_: *mut crate::leanh::LeanObject,
    mut v_i_5175_: *mut crate::leanh::LeanObject,
    mut v_stop_5176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5177_: usize = 0;
    let mut v_stop_boxed_5178_: usize = 0;
    let mut v_res_5179_: u8 = 0;
    let mut v_r_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5177_ = crate::leanh::lean_unbox_usize(v_i_5175_);
    crate::leanh::lean_dec(v_i_5175_);
    v_stop_boxed_5178_ = crate::leanh::lean_unbox_usize(v_stop_5176_);
    crate::leanh::lean_dec(v_stop_5176_);
    v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_5173_, v_as_5174_, v_i_boxed_5177_, v_stop_boxed_5178_);
    crate::leanh::lean_dec_ref(v_as_5174_);
    crate::leanh::lean_dec(v_a_5173_);
    v_r_5180_ = crate::leanh::lean_box((v_res_5179_) as usize);
    return v_r_5180_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(
    mut v_as_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    v___x_5183_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5184_ = lean_array_get_size(v_as_5181_);
    v___x_5185_ = lean_nat_dec_lt(v___x_5183_, v___x_5184_);
    if v___x_5185_ == 0 {
        return v___x_5185_;
    } else {
        if v___x_5185_ == 0 {
            return v___x_5185_;
        } else {
            let mut v___x_5186_: usize = 0;
            let mut v___x_5187_: usize = 0;
            let mut v___x_5188_: u8 = 0;
            v___x_5186_ = 0usize;
            v___x_5187_ = lean_usize_of_nat(v___x_5184_);
            v___x_5188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_5182_, v_as_5181_, v___x_5186_, v___x_5187_);
            return v___x_5188_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(
    mut v_as_5189_: *mut crate::leanh::LeanObject,
    mut v_a_5190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5191_: u8 = 0;
    let mut v_r_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5191_ =
        l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_5189_, v_a_5190_);
    crate::leanh::lean_dec(v_a_5190_);
    crate::leanh::lean_dec_ref(v_as_5189_);
    v_r_5192_ = crate::leanh::lean_box((v_res_5191_) as usize);
    return v_r_5192_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(
    mut v_upperBound_5194_: *mut crate::leanh::LeanObject,
    mut v___x_5195_: *mut crate::leanh::LeanObject,
    mut v_typeNames_5196_: *mut crate::leanh::LeanObject,
    mut v_className_5197_: *mut crate::leanh::LeanObject,
    mut v_ctx_5198_: *mut crate::leanh::LeanObject,
    mut v_useAnonCtor_5199_: u8,
    mut v_a_5200_: *mut crate::leanh::LeanObject,
    mut v_b_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v_a_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instName_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_a_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5303_: u8 = 0;
    let mut v_a_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5307_: u8 = 0;
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5234_ = lean_nat_dec_lt(v_a_5200_, v_upperBound_5194_);
                if v___x_5234_ == 0 {
                    crate::leanh::lean_dec(v_a_5200_);
                    crate::leanh::lean_dec_ref(v_ctx_5198_);
                    crate::leanh::lean_dec(v_className_5197_);
                    v___x_5235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5235_, 0, v_b_5201_);
                    return v___x_5235_;
                } else {
                    v___x_5236_ = l_Lean_instInhabitedInductiveVal_default;
                    v___x_5237_ = lean_array_get_borrowed(v___x_5236_, v___x_5195_, v_a_5200_);
                    v_toConstantVal_5238_ = crate::leanh::lean_ctor_get(v___x_5237_, 0);
                    v_name_5239_ = crate::leanh::lean_ctor_get(v_toConstantVal_5238_, 0);
                    v___x_5240_ =
                        l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(
                            v_typeNames_5196_,
                            v_name_5239_,
                        );
                    if v___x_5240_ == 0 {
                        v_a_5210_ = v_b_5201_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_5237_);
                        v___x_5241_ = l_Lean_Elab_Deriving_mkInductArgNames(
                            v___x_5237_,
                            v___y_5202_,
                            v___y_5203_,
                            v___y_5204_,
                            v___y_5205_,
                            v___y_5206_,
                            v___y_5207_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5241_) == 0 {
                            v_a_5242_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                            crate::leanh::lean_inc_n(v_a_5242_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_5241_, 1);
                            v___x_5243_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                                v_a_5242_,
                                v___y_5202_,
                                v___y_5203_,
                                v___y_5204_,
                                v___y_5205_,
                                v___y_5206_,
                                v___y_5207_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5243_) == 0 {
                                v_a_5244_ = crate::leanh::lean_ctor_get(v___x_5243_, 0);
                                crate::leanh::lean_inc(v_a_5244_);
                                crate::leanh::lean_dec_ref_known(v___x_5243_, 1);
                                crate::leanh::lean_inc(v_a_5242_);
                                crate::leanh::lean_inc(v___x_5237_);
                                crate::leanh::lean_inc(v_className_5197_);
                                v___x_5245_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                                    v_className_5197_,
                                    v___x_5237_,
                                    v_a_5242_,
                                    v___y_5202_,
                                    v___y_5203_,
                                    v___y_5204_,
                                    v___y_5205_,
                                    v___y_5206_,
                                    v___y_5207_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5245_) == 0 {
                                    v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                                    crate::leanh::lean_inc(v_a_5246_);
                                    crate::leanh::lean_dec_ref_known(v___x_5245_, 1);
                                    crate::leanh::lean_inc(v___x_5237_);
                                    v___x_5247_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                        v___x_5237_,
                                        v_a_5242_,
                                        v___y_5206_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5247_) == 0 {
                                        v_a_5248_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                                        crate::leanh::lean_inc(v_a_5248_);
                                        crate::leanh::lean_dec_ref_known(v___x_5247_, 1);
                                        v_instName_5249_ =
                                            crate::leanh::lean_ctor_get(v_ctx_5198_, 0);
                                        v_auxFunNames_5250_ =
                                            crate::leanh::lean_ctor_get(v_ctx_5198_, 2);
                                        v_ref_5251_ = crate::leanh::lean_ctor_get(v___y_5206_, 5);
                                        v___f_5252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0;
                                        v___x_5253_ = crate::leanh::lean_box(0);
                                        v___x_5254_ = lean_array_get_borrowed(
                                            v___x_5253_,
                                            v_auxFunNames_5250_,
                                            v_a_5200_,
                                        );
                                        v___x_5255_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0;
                                        v___x_5256_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1;
                                        v___x_5257_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2;
                                        v___x_5258_ = l_Array_append___redArg(v_a_5244_, v_a_5246_);
                                        crate::leanh::lean_dec(v_a_5246_);
                                        v___x_5259_ = 0;
                                        v___x_5260_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_5251_, v___x_5259_);
                                        v___x_5261_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                        crate::leanh::lean_inc(v_className_5197_);
                                        v___x_5262_ = l_Lean_mkCIdent(v_className_5197_);
                                        v___x_5263_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                        crate::leanh::lean_inc(v___x_5260_);
                                        v___x_5264_ = l_Lean_Syntax_node1(
                                            v___x_5260_,
                                            v___x_5263_,
                                            v_a_5248_,
                                        );
                                        v___x_5265_ = l_Lean_Syntax_node2(
                                            v___x_5260_,
                                            v___x_5261_,
                                            v___x_5262_,
                                            v___x_5264_,
                                        );
                                        crate::leanh::lean_inc(v___x_5254_);
                                        v___x_5266_ = lean_mk_syntax_ident(v___x_5254_);
                                        if v_useAnonCtor_5199_ == 0 {
                                            v___x_5267_ = crate::leanh::lean_box(0);
                                            crate::leanh::lean_inc(v_instName_5249_);
                                            v___x_5268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5252_, v___x_5255_, v___x_5256_, v___x_5263_, v___x_5257_, v_instName_5249_, v___x_5258_, v___x_5265_, v_b_5201_, v___x_5267_, v___x_5266_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                            crate::leanh::lean_dec_ref(v___x_5258_);
                                            v___y_5215_ = v___x_5268_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_5269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                            if crate::leanh::lean_obj_tag(v___x_5269_) == 0 {
                                                v_a_5270_ =
                                                    crate::leanh::lean_ctor_get(v___x_5269_, 0);
                                                crate::leanh::lean_inc_n(v_a_5270_, 4);
                                                crate::leanh::lean_dec_ref_known(v___x_5269_, 1);
                                                v___x_5271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5;
                                                v___x_5272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2;
                                                v___x_5273_ =
                                                    crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_5273_,
                                                    0,
                                                    v_a_5270_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_5273_,
                                                    1,
                                                    v___x_5272_,
                                                );
                                                v___x_5274_ = l_Lean_Syntax_node1(
                                                    v_a_5270_,
                                                    v___x_5263_,
                                                    v___x_5266_,
                                                );
                                                v___x_5275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3;
                                                v___x_5276_ =
                                                    crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_5276_,
                                                    0,
                                                    v_a_5270_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_5276_,
                                                    1,
                                                    v___x_5275_,
                                                );
                                                v___x_5277_ = l_Lean_Syntax_node3(
                                                    v_a_5270_,
                                                    v___x_5271_,
                                                    v___x_5273_,
                                                    v___x_5274_,
                                                    v___x_5276_,
                                                );
                                                v___x_5278_ = crate::leanh::lean_box(0);
                                                crate::leanh::lean_inc(v_instName_5249_);
                                                v___x_5279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5252_, v___x_5255_, v___x_5256_, v___x_5263_, v___x_5257_, v_instName_5249_, v___x_5258_, v___x_5265_, v_b_5201_, v___x_5278_, v___x_5277_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                                crate::leanh::lean_dec_ref(v___x_5258_);
                                                v___y_5215_ = v___x_5279_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_5266_);
                                                crate::leanh::lean_dec(v___x_5265_);
                                                crate::leanh::lean_dec_ref(v___x_5258_);
                                                crate::leanh::lean_dec_ref(v_b_5201_);
                                                crate::leanh::lean_dec(v_a_5200_);
                                                crate::leanh::lean_dec_ref(v_ctx_5198_);
                                                crate::leanh::lean_dec(v_className_5197_);
                                                v_a_5280_ =
                                                    crate::leanh::lean_ctor_get(v___x_5269_, 0);
                                                v_isSharedCheck_5287_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5269_))
                                                        as u8;
                                                if v_isSharedCheck_5287_ == 0 {
                                                    v___x_5282_ = v___x_5269_;
                                                    v_isShared_5283_ = v_isSharedCheck_5287_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5280_);
                                                    crate::leanh::lean_dec(v___x_5269_);
                                                    v___x_5282_ = crate::leanh::lean_box(0);
                                                    v_isShared_5283_ = v_isSharedCheck_5287_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5246_);
                                        crate::leanh::lean_dec(v_a_5244_);
                                        crate::leanh::lean_dec_ref(v_b_5201_);
                                        crate::leanh::lean_dec(v_a_5200_);
                                        crate::leanh::lean_dec_ref(v_ctx_5198_);
                                        crate::leanh::lean_dec(v_className_5197_);
                                        v_a_5288_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                                        v_isSharedCheck_5295_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5247_)) as u8;
                                        if v_isSharedCheck_5295_ == 0 {
                                            v___x_5290_ = v___x_5247_;
                                            v_isShared_5291_ = v_isSharedCheck_5295_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5288_);
                                            crate::leanh::lean_dec(v___x_5247_);
                                            v___x_5290_ = crate::leanh::lean_box(0);
                                            v_isShared_5291_ = v_isSharedCheck_5295_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5244_);
                                    crate::leanh::lean_dec(v_a_5242_);
                                    crate::leanh::lean_dec_ref(v_b_5201_);
                                    crate::leanh::lean_dec(v_a_5200_);
                                    crate::leanh::lean_dec_ref(v_ctx_5198_);
                                    crate::leanh::lean_dec(v_className_5197_);
                                    v_a_5296_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                                    v_isSharedCheck_5303_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5245_)) as u8;
                                    if v_isSharedCheck_5303_ == 0 {
                                        v___x_5298_ = v___x_5245_;
                                        v_isShared_5299_ = v_isSharedCheck_5303_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5296_);
                                        crate::leanh::lean_dec(v___x_5245_);
                                        v___x_5298_ = crate::leanh::lean_box(0);
                                        v_isShared_5299_ = v_isSharedCheck_5303_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5242_);
                                crate::leanh::lean_dec_ref(v_b_5201_);
                                crate::leanh::lean_dec(v_a_5200_);
                                crate::leanh::lean_dec_ref(v_ctx_5198_);
                                crate::leanh::lean_dec(v_className_5197_);
                                return v___x_5243_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_5201_);
                            crate::leanh::lean_dec(v_a_5200_);
                            crate::leanh::lean_dec_ref(v_ctx_5198_);
                            crate::leanh::lean_dec(v_className_5197_);
                            v_a_5304_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                            v_isSharedCheck_5311_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5241_)) as u8;
                            if v_isSharedCheck_5311_ == 0 {
                                v___x_5306_ = v___x_5241_;
                                v_isShared_5307_ = v_isSharedCheck_5311_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5304_);
                                crate::leanh::lean_dec(v___x_5241_);
                                v___x_5306_ = crate::leanh::lean_box(0);
                                v_isShared_5307_ = v_isSharedCheck_5311_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5211_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5212_ = lean_nat_add(v_a_5200_, v___x_5211_);
                crate::leanh::lean_dec(v_a_5200_);
                v_a_5200_ = v___x_5212_;
                v_b_5201_ = v_a_5210_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5215_) == 0 {
                    v_a_5216_ = crate::leanh::lean_ctor_get(v___y_5215_, 0);
                    v_isSharedCheck_5225_ = (!crate::leanh::lean_is_exclusive(v___y_5215_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5218_ = v___y_5215_;
                        v_isShared_5219_ = v_isSharedCheck_5225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5216_);
                        crate::leanh::lean_dec(v___y_5215_);
                        v___x_5218_ = crate::leanh::lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5225_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5200_);
                    crate::leanh::lean_dec_ref(v_ctx_5198_);
                    crate::leanh::lean_dec(v_className_5197_);
                    v_a_5226_ = crate::leanh::lean_ctor_get(v___y_5215_, 0);
                    v_isSharedCheck_5233_ = (!crate::leanh::lean_is_exclusive(v___y_5215_)) as u8;
                    if v_isSharedCheck_5233_ == 0 {
                        v___x_5228_ = v___y_5215_;
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5226_);
                        crate::leanh::lean_dec(v___y_5215_);
                        v___x_5228_ = crate::leanh::lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_5216_) == 0 {
                    crate::leanh::lean_dec(v_a_5200_);
                    crate::leanh::lean_dec_ref(v_ctx_5198_);
                    crate::leanh::lean_dec(v_className_5197_);
                    v_a_5220_ = crate::leanh::lean_ctor_get(v_a_5216_, 0);
                    crate::leanh::lean_inc(v_a_5220_);
                    crate::leanh::lean_dec_ref_known(v_a_5216_, 1);
                    if v_isShared_5219_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5218_, 0, v_a_5220_);
                        v___x_5222_ = v___x_5218_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5220_);
                        v___x_5222_ = v_reuseFailAlloc_5223_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5218_);
                    v_a_5224_ = crate::leanh::lean_ctor_get(v_a_5216_, 0);
                    crate::leanh::lean_inc(v_a_5224_);
                    crate::leanh::lean_dec_ref_known(v_a_5216_, 1);
                    v_a_5210_ = v_a_5224_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_5222_;
            }
            5 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5231_;
            }
            7 => {
                if v_isShared_5283_ == 0 {
                    v___x_5285_ = v___x_5282_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
                    v___x_5285_ = v_reuseFailAlloc_5286_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5285_;
            }
            9 => {
                if v_isShared_5291_ == 0 {
                    v___x_5293_ = v___x_5290_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
                    v___x_5293_ = v_reuseFailAlloc_5294_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5293_;
            }
            11 => {
                if v_isShared_5299_ == 0 {
                    v___x_5301_ = v___x_5298_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
                    v___x_5301_ = v_reuseFailAlloc_5302_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5301_;
            }
            13 => {
                if v_isShared_5307_ == 0 {
                    v___x_5309_ = v___x_5306_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
                    v___x_5309_ = v_reuseFailAlloc_5310_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(
    mut v_upperBound_5312_: *mut crate::leanh::LeanObject,
    mut v___x_5313_: *mut crate::leanh::LeanObject,
    mut v_typeNames_5314_: *mut crate::leanh::LeanObject,
    mut v_className_5315_: *mut crate::leanh::LeanObject,
    mut v_ctx_5316_: *mut crate::leanh::LeanObject,
    mut v_useAnonCtor_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_b_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
    mut v___y_5325_: *mut crate::leanh::LeanObject,
    mut v___y_5326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAnonCtor_boxed_5327_: u8 = 0;
    let mut v_res_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5327_ = (crate::leanh::lean_unbox(v_useAnonCtor_5317_) as u8);
    v_res_5328_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(
            v_upperBound_5312_,
            v___x_5313_,
            v_typeNames_5314_,
            v_className_5315_,
            v_ctx_5316_,
            v_useAnonCtor_boxed_5327_,
            v_a_5318_,
            v_b_5319_,
            v___y_5320_,
            v___y_5321_,
            v___y_5322_,
            v___y_5323_,
            v___y_5324_,
            v___y_5325_,
        );
    crate::leanh::lean_dec(v___y_5325_);
    crate::leanh::lean_dec_ref(v___y_5324_);
    crate::leanh::lean_dec(v___y_5323_);
    crate::leanh::lean_dec_ref(v___y_5322_);
    crate::leanh::lean_dec(v___y_5321_);
    crate::leanh::lean_dec_ref(v___y_5320_);
    crate::leanh::lean_dec_ref(v_typeNames_5314_);
    crate::leanh::lean_dec_ref(v___x_5313_);
    crate::leanh::lean_dec(v_upperBound_5312_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstanceCmds(
    mut v_ctx_5329_: *mut crate::leanh::LeanObject,
    mut v_className_5330_: *mut crate::leanh::LeanObject,
    mut v_typeNames_5331_: *mut crate::leanh::LeanObject,
    mut v_useAnonCtor_5332_: u8,
    mut v_a_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_a_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_typeInfos_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_typeInfos_5340_ = crate::leanh::lean_ctor_get(v_ctx_5329_, 1);
    crate::leanh::lean_inc_ref(v_typeInfos_5340_);
    v___x_5341_ = lean_array_get_size(v_typeInfos_5340_);
    v___x_5342_ = crate::leanh::lean_unsigned_to_nat(0);
    v_instances_5343_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
    v___x_5344_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(
            v___x_5341_,
            v_typeInfos_5340_,
            v_typeNames_5331_,
            v_className_5330_,
            v_ctx_5329_,
            v_useAnonCtor_5332_,
            v___x_5342_,
            v_instances_5343_,
            v_a_5333_,
            v_a_5334_,
            v_a_5335_,
            v_a_5336_,
            v_a_5337_,
            v_a_5338_,
        );
    crate::leanh::lean_dec_ref(v_typeInfos_5340_);
    return v___x_5344_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstanceCmds___boxed(
    mut v_ctx_5345_: *mut crate::leanh::LeanObject,
    mut v_className_5346_: *mut crate::leanh::LeanObject,
    mut v_typeNames_5347_: *mut crate::leanh::LeanObject,
    mut v_useAnonCtor_5348_: *mut crate::leanh::LeanObject,
    mut v_a_5349_: *mut crate::leanh::LeanObject,
    mut v_a_5350_: *mut crate::leanh::LeanObject,
    mut v_a_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
    mut v_a_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAnonCtor_boxed_5356_: u8 = 0;
    let mut v_res_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5356_ = (crate::leanh::lean_unbox(v_useAnonCtor_5348_) as u8);
    v_res_5357_ = l_Lean_Elab_Deriving_mkInstanceCmds(
        v_ctx_5345_,
        v_className_5346_,
        v_typeNames_5347_,
        v_useAnonCtor_boxed_5356_,
        v_a_5349_,
        v_a_5350_,
        v_a_5351_,
        v_a_5352_,
        v_a_5353_,
        v_a_5354_,
    );
    crate::leanh::lean_dec(v_a_5354_);
    crate::leanh::lean_dec_ref(v_a_5353_);
    crate::leanh::lean_dec(v_a_5352_);
    crate::leanh::lean_dec_ref(v_a_5351_);
    crate::leanh::lean_dec(v_a_5350_);
    crate::leanh::lean_dec_ref(v_a_5349_);
    crate::leanh::lean_dec_ref(v_typeNames_5347_);
    return v_res_5357_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(
    mut v_upperBound_5358_: *mut crate::leanh::LeanObject,
    mut v___x_5359_: *mut crate::leanh::LeanObject,
    mut v_typeNames_5360_: *mut crate::leanh::LeanObject,
    mut v_className_5361_: *mut crate::leanh::LeanObject,
    mut v_ctx_5362_: *mut crate::leanh::LeanObject,
    mut v_useAnonCtor_5363_: u8,
    mut v_inst_5364_: *mut crate::leanh::LeanObject,
    mut v_R_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_b_5367_: *mut crate::leanh::LeanObject,
    mut v_c_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(
            v_upperBound_5358_,
            v___x_5359_,
            v_typeNames_5360_,
            v_className_5361_,
            v_ctx_5362_,
            v_useAnonCtor_5363_,
            v_a_5366_,
            v_b_5367_,
            v___y_5369_,
            v___y_5370_,
            v___y_5371_,
            v___y_5372_,
            v___y_5373_,
            v___y_5374_,
        );
    return v___x_5376_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_5377_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5378_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_typeNames_5379_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_className_5380_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ctx_5381_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_useAnonCtor_5382_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_5383_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_R_5384_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_5385_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_b_5386_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_c_5387_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5388_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5389_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5390_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5391_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5392_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5393_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5394_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_useAnonCtor_boxed_5395_: u8 = 0;
    let mut v_res_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5395_ = (crate::leanh::lean_unbox(v_useAnonCtor_5382_) as u8);
    v_res_5396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(
        v_upperBound_5377_,
        v___x_5378_,
        v_typeNames_5379_,
        v_className_5380_,
        v_ctx_5381_,
        v_useAnonCtor_boxed_5395_,
        v_inst_5383_,
        v_R_5384_,
        v_a_5385_,
        v_b_5386_,
        v_c_5387_,
        v___y_5388_,
        v___y_5389_,
        v___y_5390_,
        v___y_5391_,
        v___y_5392_,
        v___y_5393_,
    );
    crate::leanh::lean_dec(v___y_5393_);
    crate::leanh::lean_dec_ref(v___y_5392_);
    crate::leanh::lean_dec(v___y_5391_);
    crate::leanh::lean_dec_ref(v___y_5390_);
    crate::leanh::lean_dec(v___y_5389_);
    crate::leanh::lean_dec_ref(v___y_5388_);
    crate::leanh::lean_dec_ref(v_typeNames_5379_);
    crate::leanh::lean_dec_ref(v___x_5378_);
    crate::leanh::lean_dec(v_upperBound_5377_);
    return v_res_5396_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___redArg(
    mut v_varName_5403_: *mut crate::leanh::LeanObject,
    mut v_a_5404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5406_ = crate::leanh::lean_ctor_get(v_a_5404_, 5);
    v___x_5407_ = 0;
    v___x_5408_ = l_Lean_SourceInfo_fromRef(v_ref_5406_, v___x_5407_);
    v___x_5409_ = l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1;
    v___x_5410_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
    v___x_5411_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once),
        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
    );
    crate::leanh::lean_inc(v___x_5408_);
    v___x_5412_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5408_);
    crate::leanh::lean_ctor_set(v___x_5412_, 1, v___x_5410_);
    crate::leanh::lean_ctor_set(v___x_5412_, 2, v___x_5411_);
    v___x_5413_ = lean_mk_syntax_ident(v_varName_5403_);
    v___x_5414_ = l_Lean_Syntax_node2(v___x_5408_, v___x_5409_, v___x_5412_, v___x_5413_);
    v___x_5415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5415_, 0, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(
    mut v_varName_5416_: *mut crate::leanh::LeanObject,
    mut v_a_5417_: *mut crate::leanh::LeanObject,
    mut v_a_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5419_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_5416_, v_a_5417_);
    crate::leanh::lean_dec_ref(v_a_5417_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr(
    mut v_varName_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
    mut v_a_5422_: *mut crate::leanh::LeanObject,
    mut v_a_5423_: *mut crate::leanh::LeanObject,
    mut v_a_5424_: *mut crate::leanh::LeanObject,
    mut v_a_5425_: *mut crate::leanh::LeanObject,
    mut v_a_5426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5428_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_5420_, v_a_5425_);
    return v___x_5428_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___boxed(
    mut v_varName_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: *mut crate::leanh::LeanObject,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
    mut v_a_5433_: *mut crate::leanh::LeanObject,
    mut v_a_5434_: *mut crate::leanh::LeanObject,
    mut v_a_5435_: *mut crate::leanh::LeanObject,
    mut v_a_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5437_ = l_Lean_Elab_Deriving_mkDiscr(
        v_varName_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
        v_a_5433_,
        v_a_5434_,
        v_a_5435_,
    );
    crate::leanh::lean_dec(v_a_5435_);
    crate::leanh::lean_dec_ref(v_a_5434_);
    crate::leanh::lean_dec(v_a_5433_);
    crate::leanh::lean_dec_ref(v_a_5432_);
    crate::leanh::lean_dec(v_a_5431_);
    crate::leanh::lean_dec_ref(v_a_5430_);
    return v_res_5437_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(
    mut v_upperBound_5441_: *mut crate::leanh::LeanObject,
    mut v_a_5442_: *mut crate::leanh::LeanObject,
    mut v_b_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5447_ = lean_nat_dec_lt(v_a_5442_, v_upperBound_5441_);
                if v___x_5447_ == 0 {
                    crate::leanh::lean_dec(v_a_5442_);
                    v___x_5448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5448_, 0, v_b_5443_);
                    return v___x_5448_;
                } else {
                    v___x_5449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1;
                    v___x_5450_ =
                        l_Lean_Core_mkFreshUserName(v___x_5449_, v___y_5444_, v___y_5445_);
                    if crate::leanh::lean_obj_tag(v___x_5450_) == 0 {
                        v_a_5451_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                        crate::leanh::lean_inc(v_a_5451_);
                        crate::leanh::lean_dec_ref_known(v___x_5450_, 1);
                        v___x_5452_ = lean_array_push(v_b_5443_, v_a_5451_);
                        v___x_5453_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5454_ = lean_nat_add(v_a_5442_, v___x_5453_);
                        crate::leanh::lean_dec(v_a_5442_);
                        v_a_5442_ = v___x_5454_;
                        v_b_5443_ = v___x_5452_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5443_);
                        crate::leanh::lean_dec(v_a_5442_);
                        v_a_5456_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                        v_isSharedCheck_5463_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5450_)) as u8;
                        if v_isSharedCheck_5463_ == 0 {
                            v___x_5458_ = v___x_5450_;
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5456_);
                            crate::leanh::lean_dec(v___x_5450_);
                            v___x_5458_ = crate::leanh::lean_box(0);
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5459_ == 0 {
                    v___x_5461_ = v___x_5458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
                    v___x_5461_ = v_reuseFailAlloc_5462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(
    mut v_upperBound_5464_: *mut crate::leanh::LeanObject,
    mut v_a_5465_: *mut crate::leanh::LeanObject,
    mut v_b_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5470_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(
            v_upperBound_5464_,
            v_a_5465_,
            v_b_5466_,
            v___y_5467_,
            v___y_5468_,
        );
    crate::leanh::lean_dec(v___y_5468_);
    crate::leanh::lean_dec_ref(v___y_5467_);
    crate::leanh::lean_dec(v_upperBound_5464_);
    return v_res_5470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(
    mut v_a_5479_: *mut crate::leanh::LeanObject,
    mut v_sz_5480_: usize,
    mut v_i_5481_: usize,
    mut v_bs_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: u8 = 0;
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: usize = 0;
    let mut v___x_5508_: usize = 0;
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_usize_dec_lt(v_i_5481_, v_sz_5480_);
                if v___x_5485_ == 0 {
                    crate::leanh::lean_dec(v_a_5479_);
                    v___x_5486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5486_, 0, v_bs_5482_);
                    return v___x_5486_;
                } else {
                    v_ref_5487_ = crate::leanh::lean_ctor_get(v___y_5483_, 5);
                    v_v_5488_ = lean_array_uget(v_bs_5482_, v_i_5481_);
                    v___x_5489_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5490_ = lean_array_uset(v_bs_5482_, v_i_5481_, v___x_5489_);
                    v___x_5491_ = 0;
                    v___x_5492_ = l_Lean_SourceInfo_fromRef(v_ref_5487_, v___x_5491_);
                    v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1;
                    v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2;
                    crate::leanh::lean_inc_n(v___x_5492_, 6);
                    v___x_5495_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5495_, 0, v___x_5492_);
                    crate::leanh::lean_ctor_set(v___x_5495_, 1, v___x_5494_);
                    v___x_5496_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_5497_ = lean_mk_syntax_ident(v_v_5488_);
                    v___x_5498_ = l_Lean_Syntax_node1(v___x_5492_, v___x_5496_, v___x_5497_);
                    v___x_5499_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                    v___x_5500_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5500_, 0, v___x_5492_);
                    crate::leanh::lean_ctor_set(v___x_5500_, 1, v___x_5499_);
                    crate::leanh::lean_inc(v_a_5479_);
                    v___x_5501_ =
                        l_Lean_Syntax_node2(v___x_5492_, v___x_5496_, v___x_5500_, v_a_5479_);
                    v___x_5502_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_5503_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5503_, 0, v___x_5492_);
                    crate::leanh::lean_ctor_set(v___x_5503_, 1, v___x_5496_);
                    crate::leanh::lean_ctor_set(v___x_5503_, 2, v___x_5502_);
                    v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3;
                    v___x_5505_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5505_, 0, v___x_5492_);
                    crate::leanh::lean_ctor_set(v___x_5505_, 1, v___x_5504_);
                    v___x_5506_ = l_Lean_Syntax_node5(
                        v___x_5492_,
                        v___x_5493_,
                        v___x_5495_,
                        v___x_5498_,
                        v___x_5501_,
                        v___x_5503_,
                        v___x_5505_,
                    );
                    v___x_5507_ = 1usize;
                    v___x_5508_ = lean_usize_add(v_i_5481_, v___x_5507_);
                    v___x_5509_ = lean_array_uset(v_bs_x27_5490_, v_i_5481_, v___x_5506_);
                    v_i_5481_ = v___x_5508_;
                    v_bs_5482_ = v___x_5509_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(
    mut v_a_5511_: *mut crate::leanh::LeanObject,
    mut v_sz_5512_: *mut crate::leanh::LeanObject,
    mut v_i_5513_: *mut crate::leanh::LeanObject,
    mut v_bs_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5517_: usize = 0;
    let mut v_i_boxed_5518_: usize = 0;
    let mut v_res_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5517_ = crate::leanh::lean_unbox_usize(v_sz_5512_);
    crate::leanh::lean_dec(v_sz_5512_);
    v_i_boxed_5518_ = crate::leanh::lean_unbox_usize(v_i_5513_);
    crate::leanh::lean_dec(v_i_5513_);
    v_res_5519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5511_, v_sz_boxed_5517_, v_i_boxed_5518_, v_bs_5514_, v___y_5515_);
    crate::leanh::lean_dec_ref(v___y_5515_);
    return v_res_5519_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkHeader(
    mut v_className_5520_: *mut crate::leanh::LeanObject,
    mut v_arity_5521_: *mut crate::leanh::LeanObject,
    mut v_indVal_5522_: *mut crate::leanh::LeanObject,
    mut v_a_5523_: *mut crate::leanh::LeanObject,
    mut v_a_5524_: *mut crate::leanh::LeanObject,
    mut v_a_5525_: *mut crate::leanh::LeanObject,
    mut v_a_5526_: *mut crate::leanh::LeanObject,
    mut v_a_5527_: *mut crate::leanh::LeanObject,
    mut v_a_5528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5542_: usize = 0;
    let mut v___x_5543_: usize = 0;
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5548_: u8 = 0;
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_a_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut v_a_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_a_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v_a_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_indVal_5522_);
                v___x_5530_ = l_Lean_Elab_Deriving_mkInductArgNames(
                    v_indVal_5522_,
                    v_a_5523_,
                    v_a_5524_,
                    v_a_5525_,
                    v_a_5526_,
                    v_a_5527_,
                    v_a_5528_,
                );
                if crate::leanh::lean_obj_tag(v___x_5530_) == 0 {
                    v_a_5531_ = crate::leanh::lean_ctor_get(v___x_5530_, 0);
                    crate::leanh::lean_inc_n(v_a_5531_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5530_, 1);
                    v___x_5532_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                        v_a_5531_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5532_) == 0 {
                        v_a_5533_ = crate::leanh::lean_ctor_get(v___x_5532_, 0);
                        crate::leanh::lean_inc(v_a_5533_);
                        crate::leanh::lean_dec_ref_known(v___x_5532_, 1);
                        crate::leanh::lean_inc(v_a_5531_);
                        crate::leanh::lean_inc_ref(v_indVal_5522_);
                        v___x_5534_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                            v_indVal_5522_,
                            v_a_5531_,
                            v_a_5527_,
                        );
                        v_a_5535_ = crate::leanh::lean_ctor_get(v___x_5534_, 0);
                        crate::leanh::lean_inc(v_a_5535_);
                        crate::leanh::lean_dec_ref(v___x_5534_);
                        v___x_5536_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5537_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
                        v___x_5538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_5521_, v___x_5536_, v___x_5537_, v_a_5527_, v_a_5528_);
                        if crate::leanh::lean_obj_tag(v___x_5538_) == 0 {
                            v_a_5539_ = crate::leanh::lean_ctor_get(v___x_5538_, 0);
                            crate::leanh::lean_inc(v_a_5539_);
                            crate::leanh::lean_dec_ref_known(v___x_5538_, 1);
                            crate::leanh::lean_inc(v_a_5531_);
                            v___x_5540_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                                v_className_5520_,
                                v_indVal_5522_,
                                v_a_5531_,
                                v_a_5523_,
                                v_a_5524_,
                                v_a_5525_,
                                v_a_5526_,
                                v_a_5527_,
                                v_a_5528_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5540_) == 0 {
                                v_a_5541_ = crate::leanh::lean_ctor_get(v___x_5540_, 0);
                                crate::leanh::lean_inc(v_a_5541_);
                                crate::leanh::lean_dec_ref_known(v___x_5540_, 1);
                                v_sz_5542_ = lean_array_size(v_a_5539_);
                                v___x_5543_ = 0usize;
                                crate::leanh::lean_inc(v_a_5539_);
                                crate::leanh::lean_inc(v_a_5535_);
                                v___x_5544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5535_, v_sz_5542_, v___x_5543_, v_a_5539_, v_a_5527_);
                                if crate::leanh::lean_obj_tag(v___x_5544_) == 0 {
                                    v_a_5545_ = crate::leanh::lean_ctor_get(v___x_5544_, 0);
                                    v_isSharedCheck_5555_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5544_)) as u8;
                                    if v_isSharedCheck_5555_ == 0 {
                                        v___x_5547_ = v___x_5544_;
                                        v_isShared_5548_ = v_isSharedCheck_5555_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5545_);
                                        crate::leanh::lean_dec(v___x_5544_);
                                        v___x_5547_ = crate::leanh::lean_box(0);
                                        v_isShared_5548_ = v_isSharedCheck_5555_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5541_);
                                    crate::leanh::lean_dec(v_a_5539_);
                                    crate::leanh::lean_dec(v_a_5535_);
                                    crate::leanh::lean_dec(v_a_5533_);
                                    crate::leanh::lean_dec(v_a_5531_);
                                    v_a_5556_ = crate::leanh::lean_ctor_get(v___x_5544_, 0);
                                    v_isSharedCheck_5563_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5544_)) as u8;
                                    if v_isSharedCheck_5563_ == 0 {
                                        v___x_5558_ = v___x_5544_;
                                        v_isShared_5559_ = v_isSharedCheck_5563_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5556_);
                                        crate::leanh::lean_dec(v___x_5544_);
                                        v___x_5558_ = crate::leanh::lean_box(0);
                                        v_isShared_5559_ = v_isSharedCheck_5563_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5539_);
                                crate::leanh::lean_dec(v_a_5535_);
                                crate::leanh::lean_dec(v_a_5533_);
                                crate::leanh::lean_dec(v_a_5531_);
                                v_a_5564_ = crate::leanh::lean_ctor_get(v___x_5540_, 0);
                                v_isSharedCheck_5571_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5540_)) as u8;
                                if v_isSharedCheck_5571_ == 0 {
                                    v___x_5566_ = v___x_5540_;
                                    v_isShared_5567_ = v_isSharedCheck_5571_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5564_);
                                    crate::leanh::lean_dec(v___x_5540_);
                                    v___x_5566_ = crate::leanh::lean_box(0);
                                    v_isShared_5567_ = v_isSharedCheck_5571_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5535_);
                            crate::leanh::lean_dec(v_a_5533_);
                            crate::leanh::lean_dec(v_a_5531_);
                            crate::leanh::lean_dec_ref(v_indVal_5522_);
                            crate::leanh::lean_dec(v_className_5520_);
                            v_a_5572_ = crate::leanh::lean_ctor_get(v___x_5538_, 0);
                            v_isSharedCheck_5579_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5538_)) as u8;
                            if v_isSharedCheck_5579_ == 0 {
                                v___x_5574_ = v___x_5538_;
                                v_isShared_5575_ = v_isSharedCheck_5579_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5572_);
                                crate::leanh::lean_dec(v___x_5538_);
                                v___x_5574_ = crate::leanh::lean_box(0);
                                v_isShared_5575_ = v_isSharedCheck_5579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5531_);
                        crate::leanh::lean_dec_ref(v_indVal_5522_);
                        crate::leanh::lean_dec(v_className_5520_);
                        v_a_5580_ = crate::leanh::lean_ctor_get(v___x_5532_, 0);
                        v_isSharedCheck_5587_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5532_)) as u8;
                        if v_isSharedCheck_5587_ == 0 {
                            v___x_5582_ = v___x_5532_;
                            v_isShared_5583_ = v_isSharedCheck_5587_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5580_);
                            crate::leanh::lean_dec(v___x_5532_);
                            v___x_5582_ = crate::leanh::lean_box(0);
                            v_isShared_5583_ = v_isSharedCheck_5587_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_indVal_5522_);
                    crate::leanh::lean_dec(v_className_5520_);
                    v_a_5588_ = crate::leanh::lean_ctor_get(v___x_5530_, 0);
                    v_isSharedCheck_5595_ = (!crate::leanh::lean_is_exclusive(v___x_5530_)) as u8;
                    if v_isSharedCheck_5595_ == 0 {
                        v___x_5590_ = v___x_5530_;
                        v_isShared_5591_ = v_isSharedCheck_5595_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5588_);
                        crate::leanh::lean_dec(v___x_5530_);
                        v___x_5590_ = crate::leanh::lean_box(0);
                        v_isShared_5591_ = v_isSharedCheck_5595_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5549_ = l_Array_append___redArg(v_a_5533_, v_a_5541_);
                crate::leanh::lean_dec(v_a_5541_);
                v___x_5550_ = l_Array_append___redArg(v___x_5549_, v_a_5545_);
                crate::leanh::lean_dec(v_a_5545_);
                v___x_5551_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5551_, 0, v___x_5550_);
                crate::leanh::lean_ctor_set(v___x_5551_, 1, v_a_5531_);
                crate::leanh::lean_ctor_set(v___x_5551_, 2, v_a_5539_);
                crate::leanh::lean_ctor_set(v___x_5551_, 3, v_a_5535_);
                if v_isShared_5548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5547_, 0, v___x_5551_);
                    v___x_5553_ = v___x_5547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5551_);
                    v___x_5553_ = v_reuseFailAlloc_5554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5553_;
            }
            3 => {
                if v_isShared_5559_ == 0 {
                    v___x_5561_ = v___x_5558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
                    v___x_5561_ = v_reuseFailAlloc_5562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5561_;
            }
            5 => {
                if v_isShared_5567_ == 0 {
                    v___x_5569_ = v___x_5566_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
                    v___x_5569_ = v_reuseFailAlloc_5570_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5569_;
            }
            7 => {
                if v_isShared_5575_ == 0 {
                    v___x_5577_ = v___x_5574_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
                    v___x_5577_ = v_reuseFailAlloc_5578_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5577_;
            }
            9 => {
                if v_isShared_5583_ == 0 {
                    v___x_5585_ = v___x_5582_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
                    v___x_5585_ = v_reuseFailAlloc_5586_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5585_;
            }
            11 => {
                if v_isShared_5591_ == 0 {
                    v___x_5593_ = v___x_5590_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
                    v___x_5593_ = v_reuseFailAlloc_5594_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkHeader___boxed(
    mut v_className_5596_: *mut crate::leanh::LeanObject,
    mut v_arity_5597_: *mut crate::leanh::LeanObject,
    mut v_indVal_5598_: *mut crate::leanh::LeanObject,
    mut v_a_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
    mut v_a_5601_: *mut crate::leanh::LeanObject,
    mut v_a_5602_: *mut crate::leanh::LeanObject,
    mut v_a_5603_: *mut crate::leanh::LeanObject,
    mut v_a_5604_: *mut crate::leanh::LeanObject,
    mut v_a_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5606_ = l_Lean_Elab_Deriving_mkHeader(
        v_className_5596_,
        v_arity_5597_,
        v_indVal_5598_,
        v_a_5599_,
        v_a_5600_,
        v_a_5601_,
        v_a_5602_,
        v_a_5603_,
        v_a_5604_,
    );
    crate::leanh::lean_dec(v_a_5604_);
    crate::leanh::lean_dec_ref(v_a_5603_);
    crate::leanh::lean_dec(v_a_5602_);
    crate::leanh::lean_dec_ref(v_a_5601_);
    crate::leanh::lean_dec(v_a_5600_);
    crate::leanh::lean_dec_ref(v_a_5599_);
    crate::leanh::lean_dec(v_arity_5597_);
    return v_res_5606_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(
    mut v_a_5607_: *mut crate::leanh::LeanObject,
    mut v_sz_5608_: usize,
    mut v_i_5609_: usize,
    mut v_bs_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5607_, v_sz_5608_, v_i_5609_, v_bs_5610_, v___y_5615_);
    return v___x_5618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(
    mut v_a_5619_: *mut crate::leanh::LeanObject,
    mut v_sz_5620_: *mut crate::leanh::LeanObject,
    mut v_i_5621_: *mut crate::leanh::LeanObject,
    mut v_bs_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5630_: usize = 0;
    let mut v_i_boxed_5631_: usize = 0;
    let mut v_res_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5630_ = crate::leanh::lean_unbox_usize(v_sz_5620_);
    crate::leanh::lean_dec(v_sz_5620_);
    v_i_boxed_5631_ = crate::leanh::lean_unbox_usize(v_i_5621_);
    crate::leanh::lean_dec(v_i_5621_);
    v_res_5632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_5619_, v_sz_boxed_5630_, v_i_boxed_5631_, v_bs_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
    crate::leanh::lean_dec(v___y_5628_);
    crate::leanh::lean_dec_ref(v___y_5627_);
    crate::leanh::lean_dec(v___y_5626_);
    crate::leanh::lean_dec_ref(v___y_5625_);
    crate::leanh::lean_dec(v___y_5624_);
    crate::leanh::lean_dec_ref(v___y_5623_);
    return v_res_5632_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(
    mut v_upperBound_5633_: *mut crate::leanh::LeanObject,
    mut v_inst_5634_: *mut crate::leanh::LeanObject,
    mut v_R_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
    mut v_b_5637_: *mut crate::leanh::LeanObject,
    mut v_c_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5646_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(
            v_upperBound_5633_,
            v_a_5636_,
            v_b_5637_,
            v___y_5643_,
            v___y_5644_,
        );
    return v___x_5646_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(
    mut v_upperBound_5647_: *mut crate::leanh::LeanObject,
    mut v_inst_5648_: *mut crate::leanh::LeanObject,
    mut v_R_5649_: *mut crate::leanh::LeanObject,
    mut v_a_5650_: *mut crate::leanh::LeanObject,
    mut v_b_5651_: *mut crate::leanh::LeanObject,
    mut v_c_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(
        v_upperBound_5647_,
        v_inst_5648_,
        v_R_5649_,
        v_a_5650_,
        v_b_5651_,
        v_c_5652_,
        v___y_5653_,
        v___y_5654_,
        v___y_5655_,
        v___y_5656_,
        v___y_5657_,
        v___y_5658_,
    );
    crate::leanh::lean_dec(v___y_5658_);
    crate::leanh::lean_dec_ref(v___y_5657_);
    crate::leanh::lean_dec(v___y_5656_);
    crate::leanh::lean_dec_ref(v___y_5655_);
    crate::leanh::lean_dec(v___y_5654_);
    crate::leanh::lean_dec_ref(v___y_5653_);
    crate::leanh::lean_dec(v_upperBound_5647_);
    return v_res_5660_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
    mut v_a_5661_: *mut crate::leanh::LeanObject,
    mut v_b_5662_: *mut crate::leanh::LeanObject,
    mut v___y_5663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5670_: u8 = 0;
    let mut v___x_5671_: u8 = 0;
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5686_: u8 = 0;
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5690_: u8 = 0;
    let mut v_isSharedCheck_5691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5665_ = crate::leanh::lean_ctor_get(v_a_5661_, 0);
                v_start_5666_ = crate::leanh::lean_ctor_get(v_a_5661_, 1);
                v_stop_5667_ = crate::leanh::lean_ctor_get(v_a_5661_, 2);
                v_isSharedCheck_5691_ = (!crate::leanh::lean_is_exclusive(v_a_5661_)) as u8;
                if v_isSharedCheck_5691_ == 0 {
                    v___x_5669_ = v_a_5661_;
                    v_isShared_5670_ = v_isSharedCheck_5691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_5667_);
                    crate::leanh::lean_inc(v_start_5666_);
                    crate::leanh::lean_inc(v_array_5665_);
                    crate::leanh::lean_dec(v_a_5661_);
                    v___x_5669_ = crate::leanh::lean_box(0);
                    v_isShared_5670_ = v_isSharedCheck_5691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5671_ = lean_nat_dec_lt(v_start_5666_, v_stop_5667_);
                if v___x_5671_ == 0 {
                    crate::leanh::lean_del_object(v___x_5669_);
                    crate::leanh::lean_dec(v_stop_5667_);
                    crate::leanh::lean_dec(v_start_5666_);
                    crate::leanh::lean_dec_ref(v_array_5665_);
                    v___x_5672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5672_, 0, v_b_5662_);
                    return v___x_5672_;
                } else {
                    v___x_5673_ = lean_array_fget_borrowed(v_array_5665_, v_start_5666_);
                    crate::leanh::lean_inc(v___x_5673_);
                    v___x_5674_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_5673_, v___y_5663_);
                    if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
                        v_a_5675_ = crate::leanh::lean_ctor_get(v___x_5674_, 0);
                        crate::leanh::lean_inc(v_a_5675_);
                        crate::leanh::lean_dec_ref_known(v___x_5674_, 1);
                        v___x_5676_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5677_ = lean_nat_add(v_start_5666_, v___x_5676_);
                        crate::leanh::lean_dec(v_start_5666_);
                        if v_isShared_5670_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5669_, 1, v___x_5677_);
                            v___x_5679_ = v___x_5669_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5682_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_array_5665_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___x_5677_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 2, v_stop_5667_);
                            v___x_5679_ = v_reuseFailAlloc_5682_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5669_);
                        crate::leanh::lean_dec(v_stop_5667_);
                        crate::leanh::lean_dec(v_start_5666_);
                        crate::leanh::lean_dec_ref(v_array_5665_);
                        crate::leanh::lean_dec_ref(v_b_5662_);
                        v_a_5683_ = crate::leanh::lean_ctor_get(v___x_5674_, 0);
                        v_isSharedCheck_5690_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5674_)) as u8;
                        if v_isSharedCheck_5690_ == 0 {
                            v___x_5685_ = v___x_5674_;
                            v_isShared_5686_ = v_isSharedCheck_5690_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5683_);
                            crate::leanh::lean_dec(v___x_5674_);
                            v___x_5685_ = crate::leanh::lean_box(0);
                            v_isShared_5686_ = v_isSharedCheck_5690_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_5680_ = lean_array_push(v_b_5662_, v_a_5675_);
                v_a_5661_ = v___x_5679_;
                v_b_5662_ = v___x_5680_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5686_ == 0 {
                    v___x_5688_ = v___x_5685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
                    v___x_5688_ = v_reuseFailAlloc_5689_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_b_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5696_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
            v_a_5692_,
            v_b_5693_,
            v___y_5694_,
        );
    crate::leanh::lean_dec_ref(v___y_5694_);
    return v_res_5696_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(
    mut v_sz_5697_: usize,
    mut v_i_5698_: usize,
    mut v_bs_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: usize = 0;
    let mut v___x_5710_: usize = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5716_: u8 = 0;
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5702_ = lean_usize_dec_lt(v_i_5698_, v_sz_5697_);
                if v___x_5702_ == 0 {
                    v___x_5703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5703_, 0, v_bs_5699_);
                    return v___x_5703_;
                } else {
                    v_v_5704_ = lean_array_uget_borrowed(v_bs_5699_, v_i_5698_);
                    crate::leanh::lean_inc(v_v_5704_);
                    v___x_5705_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_5704_, v___y_5700_);
                    if crate::leanh::lean_obj_tag(v___x_5705_) == 0 {
                        v_a_5706_ = crate::leanh::lean_ctor_get(v___x_5705_, 0);
                        crate::leanh::lean_inc(v_a_5706_);
                        crate::leanh::lean_dec_ref_known(v___x_5705_, 1);
                        v___x_5707_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5708_ = lean_array_uset(v_bs_5699_, v_i_5698_, v___x_5707_);
                        v___x_5709_ = 1usize;
                        v___x_5710_ = lean_usize_add(v_i_5698_, v___x_5709_);
                        v___x_5711_ = lean_array_uset(v_bs_x27_5708_, v_i_5698_, v_a_5706_);
                        v_i_5698_ = v___x_5710_;
                        v_bs_5699_ = v___x_5711_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5699_);
                        v_a_5713_ = crate::leanh::lean_ctor_get(v___x_5705_, 0);
                        v_isSharedCheck_5720_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5705_)) as u8;
                        if v_isSharedCheck_5720_ == 0 {
                            v___x_5715_ = v___x_5705_;
                            v_isShared_5716_ = v_isSharedCheck_5720_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5713_);
                            crate::leanh::lean_dec(v___x_5705_);
                            v___x_5715_ = crate::leanh::lean_box(0);
                            v_isShared_5716_ = v_isSharedCheck_5720_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5716_ == 0 {
                    v___x_5718_ = v___x_5715_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5719_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_a_5713_);
                    v___x_5718_ = v_reuseFailAlloc_5719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(
    mut v_sz_5721_: *mut crate::leanh::LeanObject,
    mut v_i_5722_: *mut crate::leanh::LeanObject,
    mut v_bs_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5726_: usize = 0;
    let mut v_i_boxed_5727_: usize = 0;
    let mut v_res_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5726_ = crate::leanh::lean_unbox_usize(v_sz_5721_);
    crate::leanh::lean_dec(v_sz_5721_);
    v_i_boxed_5727_ = crate::leanh::lean_unbox_usize(v_i_5722_);
    crate::leanh::lean_dec(v_i_5722_);
    v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_5726_, v_i_boxed_5727_, v_bs_5723_, v___y_5724_);
    crate::leanh::lean_dec_ref(v___y_5724_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscrs(
    mut v_header_5729_: *mut crate::leanh::LeanObject,
    mut v_indVal_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
    mut v_a_5733_: *mut crate::leanh::LeanObject,
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_argNames_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetNames_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5749_: usize = 0;
    let mut v___x_5750_: usize = 0;
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5755_: u8 = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_argNames_5738_ = crate::leanh::lean_ctor_get(v_header_5729_, 1);
                crate::leanh::lean_inc_ref(v_argNames_5738_);
                v_targetNames_5739_ = crate::leanh::lean_ctor_get(v_header_5729_, 2);
                crate::leanh::lean_inc_ref(v_targetNames_5739_);
                crate::leanh::lean_dec_ref(v_header_5729_);
                v_numParams_5740_ = crate::leanh::lean_ctor_get(v_indVal_5730_, 1);
                crate::leanh::lean_inc(v_numParams_5740_);
                crate::leanh::lean_dec_ref(v_indVal_5730_);
                v___x_5741_ = crate::leanh::lean_unsigned_to_nat(0);
                v_discrs_5742_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
                v___x_5761_ = lean_array_get_size(v_argNames_5738_);
                v___x_5762_ = lean_nat_dec_le(v_numParams_5740_, v___x_5741_);
                if v___x_5762_ == 0 {
                    v_lower_5744_ = v_numParams_5740_;
                    v_upper_5745_ = v___x_5761_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_numParams_5740_);
                    v_lower_5744_ = v___x_5741_;
                    v_upper_5745_ = v___x_5761_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5746_ =
                    l_Array_toSubarray___redArg(v_argNames_5738_, v_lower_5744_, v_upper_5745_);
                v___x_5747_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v___x_5746_, v_discrs_5742_, v_a_5735_);
                if crate::leanh::lean_obj_tag(v___x_5747_) == 0 {
                    v_a_5748_ = crate::leanh::lean_ctor_get(v___x_5747_, 0);
                    crate::leanh::lean_inc(v_a_5748_);
                    crate::leanh::lean_dec_ref_known(v___x_5747_, 1);
                    v_sz_5749_ = lean_array_size(v_targetNames_5739_);
                    v___x_5750_ = 0usize;
                    v___x_5751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_5749_, v___x_5750_, v_targetNames_5739_, v_a_5735_);
                    if crate::leanh::lean_obj_tag(v___x_5751_) == 0 {
                        v_a_5752_ = crate::leanh::lean_ctor_get(v___x_5751_, 0);
                        v_isSharedCheck_5760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5751_)) as u8;
                        if v_isSharedCheck_5760_ == 0 {
                            v___x_5754_ = v___x_5751_;
                            v_isShared_5755_ = v_isSharedCheck_5760_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5752_);
                            crate::leanh::lean_dec(v___x_5751_);
                            v___x_5754_ = crate::leanh::lean_box(0);
                            v_isShared_5755_ = v_isSharedCheck_5760_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5748_);
                        return v___x_5751_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_targetNames_5739_);
                    return v___x_5747_;
                }
            }
            2 => {
                v___x_5756_ = l_Array_append___redArg(v_a_5748_, v_a_5752_);
                crate::leanh::lean_dec(v_a_5752_);
                if v_isShared_5755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5754_, 0, v___x_5756_);
                    v___x_5758_ = v___x_5754_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscrs___boxed(
    mut v_header_5763_: *mut crate::leanh::LeanObject,
    mut v_indVal_5764_: *mut crate::leanh::LeanObject,
    mut v_a_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_a_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
    mut v_a_5769_: *mut crate::leanh::LeanObject,
    mut v_a_5770_: *mut crate::leanh::LeanObject,
    mut v_a_5771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l_Lean_Elab_Deriving_mkDiscrs(
        v_header_5763_,
        v_indVal_5764_,
        v_a_5765_,
        v_a_5766_,
        v_a_5767_,
        v_a_5768_,
        v_a_5769_,
        v_a_5770_,
    );
    crate::leanh::lean_dec(v_a_5770_);
    crate::leanh::lean_dec_ref(v_a_5769_);
    crate::leanh::lean_dec(v_a_5768_);
    crate::leanh::lean_dec_ref(v_a_5767_);
    crate::leanh::lean_dec(v_a_5766_);
    crate::leanh::lean_dec_ref(v_a_5765_);
    return v_res_5772_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(
    mut v_inst_5773_: *mut crate::leanh::LeanObject,
    mut v_R_5774_: *mut crate::leanh::LeanObject,
    mut v_a_5775_: *mut crate::leanh::LeanObject,
    mut v_b_5776_: *mut crate::leanh::LeanObject,
    mut v_c_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5785_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
            v_a_5775_,
            v_b_5776_,
            v___y_5782_,
        );
    return v___x_5785_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(
    mut v_inst_5786_: *mut crate::leanh::LeanObject,
    mut v_R_5787_: *mut crate::leanh::LeanObject,
    mut v_a_5788_: *mut crate::leanh::LeanObject,
    mut v_b_5789_: *mut crate::leanh::LeanObject,
    mut v_c_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(
        v_inst_5786_,
        v_R_5787_,
        v_a_5788_,
        v_b_5789_,
        v_c_5790_,
        v___y_5791_,
        v___y_5792_,
        v___y_5793_,
        v___y_5794_,
        v___y_5795_,
        v___y_5796_,
    );
    crate::leanh::lean_dec(v___y_5796_);
    crate::leanh::lean_dec_ref(v___y_5795_);
    crate::leanh::lean_dec(v___y_5794_);
    crate::leanh::lean_dec_ref(v___y_5793_);
    crate::leanh::lean_dec(v___y_5792_);
    crate::leanh::lean_dec_ref(v___y_5791_);
    return v_res_5798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(
    mut v_sz_5799_: usize,
    mut v_i_5800_: usize,
    mut v_bs_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
    mut v___y_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_5799_, v_i_5800_, v_bs_5801_, v___y_5806_);
    return v___x_5809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(
    mut v_sz_5810_: *mut crate::leanh::LeanObject,
    mut v_i_5811_: *mut crate::leanh::LeanObject,
    mut v_bs_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
    mut v___y_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5820_: usize = 0;
    let mut v_i_boxed_5821_: usize = 0;
    let mut v_res_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5820_ = crate::leanh::lean_unbox_usize(v_sz_5810_);
    crate::leanh::lean_dec(v_sz_5810_);
    v_i_boxed_5821_ = crate::leanh::lean_unbox_usize(v_i_5811_);
    crate::leanh::lean_dec(v_i_5811_);
    v_res_5822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_5820_, v_i_boxed_5821_, v_bs_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
    crate::leanh::lean_dec(v___y_5818_);
    crate::leanh::lean_dec_ref(v___y_5817_);
    crate::leanh::lean_dec(v___y_5816_);
    crate::leanh::lean_dec_ref(v___y_5815_);
    crate::leanh::lean_dec(v___y_5814_);
    crate::leanh::lean_dec_ref(v___y_5813_);
    return v_res_5822_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Elab_Deriving_implicitBinderF = _init_l_Lean_Elab_Deriving_implicitBinderF();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Deriving_implicitBinderF);
    l_Lean_Elab_Deriving_instBinderF = _init_l_Lean_Elab_Deriving_instBinderF();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Deriving_instBinderF);
    l_Lean_Elab_Deriving_explicitBinderF = _init_l_Lean_Elab_Deriving_explicitBinderF();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Deriving_explicitBinderF);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Deriving_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_Util(builtin);
}
