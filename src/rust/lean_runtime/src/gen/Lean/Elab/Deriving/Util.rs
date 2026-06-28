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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_7, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Lean_Elab_Deriving_implicitBinderF___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_implicitBinderF___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_implicitBinderF: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_instBinderF: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Deriving_explicitBinderF___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_explicitBinderF___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Deriving_explicitBinderF: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Deriving_mkInductArgNames___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value: LeanStringObject<4> =
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
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value)
                as *mut LeanObject,
            12966880221525079621 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value: LeanStringObject<9> =
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
        m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value)
                as *mut LeanObject,
            13290931718435096973 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value: LeanStringObject<2> =
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
        m_data: [64, 0],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value) as *mut LeanObject,6962862263136859431 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value) as *mut LeanObject,16363371701764479942 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value) as *mut LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value) as *mut LeanObject,7499624980761693169 as *mut LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value) as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value) as *mut LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value) as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value) as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value) as *mut LeanObject;
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value) as *mut LeanObject,3878072352281346923 as *mut LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value) as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 115, 101, 0]};
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value) as *mut LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value) as *mut LeanObject,9363914857124557226 as *mut LeanObject] };
static mut l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8: *mut LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value:
    LeanStringObject<43> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value:
    LeanStringObject<45> = LeanStringObject {
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
        96, 32, 97, 115, 32, 105, 116, 32, 104, 97, 115, 32, 111, 110, 101, 32, 111, 114, 32, 109,
        111, 114, 101, 32, 112, 114, 105, 118, 97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkInstName___closed__0_value: LeanStringObject<5> =
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
        m_data: [105, 110, 115, 116, 0],
    };
static mut l_Lean_Elab_Deriving_mkInstName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInstName___closed__0_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__0_value: LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__1_value: LeanStringObject<9> =
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
        m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__0_value) as *mut LeanObject,
        12843180897352504333 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Deriving_mkContext___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__1_value) as *mut LeanObject,
        3113176348997436611 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkContext___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__3_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Deriving_mkContext___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkContext___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__3_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Deriving_mkContext___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_mkContext___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkContext___closed__6_value: LeanStringObject<11> =
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
        m_data: [105, 110, 115, 116, 78, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_mkContext___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Deriving_mkContext___closed__8_value: LeanStringObject<15> =
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
            32, 97, 117, 120, 70, 117, 110, 78, 97, 109, 101, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Deriving_mkContext___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkContext___closed__8_value) as *mut LeanObject;
static mut l_Lean_Elab_Deriving_mkContext___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Deriving_mkContext___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 99, 97, 108, 105, 110, 115, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value) as *mut LeanObject,850437327472445489 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value) as *mut LeanObject,8036185514257755965 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value) as *mut LeanObject,17116161260408496210 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value) as *mut LeanObject,13708106407786339395 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value) as *mut LeanObject,146480343229376155 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value) as *mut LeanObject,17404204824591055365 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value: LeanStringObject<11> =
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
        m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0],
    };
static mut l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value)
                as *mut LeanObject,
            9383794970646754147 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value) as *mut LeanObject,17201320286889277233 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0() -> *mut LeanObject {
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    v___x_2912_ = 0;
    v___x_2913_ = l_Lean_Parser_Term_implicitBinder(v___x_2912_);
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_implicitBinderF() -> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_implicitBinderF___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_implicitBinderF___closed__0_once),
        _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0,
    );
    return v___x_2914_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_instBinderF() -> *mut LeanObject {
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Parser_Term_instBinder;
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0() -> *mut LeanObject {
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    v___x_2916_ = 0;
    v___x_2917_ = l_Lean_Parser_Term_explicitBinder(v___x_2916_);
    return v___x_2917_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_explicitBinderF() -> *mut LeanObject {
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    v___x_2918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_explicitBinderF___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_explicitBinderF___closed__0_once),
        _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0,
    );
    return v___x_2918_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(
    mut v_k_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v_b_2922_: *mut LeanObject,
    mut v_c_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2927_);
    lean_inc_ref(v___y_2926_);
    lean_inc(v___y_2925_);
    lean_inc_ref(v___y_2924_);
    lean_inc(v___y_2921_);
    lean_inc_ref(v___y_2920_);
    v___x_2929_ = lean_apply_9(
        v_k_2919_,
        v_b_2922_,
        v_c_2923_,
        v___y_2920_,
        v___y_2921_,
        v___y_2924_,
        v___y_2925_,
        v___y_2926_,
        v___y_2927_,
        lean_box(0),
    );
    return v___x_2929_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed(
    mut v_k_2930_: *mut LeanObject,
    mut v___y_2931_: *mut LeanObject,
    mut v___y_2932_: *mut LeanObject,
    mut v_b_2933_: *mut LeanObject,
    mut v_c_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(v_k_2930_, v___y_2931_, v___y_2932_, v_b_2933_, v_c_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
    lean_dec(v___y_2938_);
    lean_dec_ref(v___y_2937_);
    lean_dec(v___y_2936_);
    lean_dec_ref(v___y_2935_);
    lean_dec(v___y_2932_);
    lean_dec_ref(v___y_2931_);
    return v_res_2940_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(
    mut v_type_2941_: *mut LeanObject,
    mut v_k_2942_: *mut LeanObject,
    mut v_cleanupAnnotations_2943_: u8,
    mut v_whnfType_2944_: u8,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v___y_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2946_);
                lean_inc_ref(v___y_2945_);
                v___f_2952_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_2952_, 0, v_k_2942_);
                lean_closure_set(v___f_2952_, 1, v___y_2945_);
                lean_closure_set(v___f_2952_, 2, v___y_2946_);
                v___x_2953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_2941_,
                    v___f_2952_,
                    v_cleanupAnnotations_2943_,
                    v_whnfType_2944_,
                    v___y_2947_,
                    v___y_2948_,
                    v___y_2949_,
                    v___y_2950_,
                );
                if lean_obj_tag(v___x_2953_) == 0 {
                    return v___x_2953_;
                } else {
                    v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
                    v_isSharedCheck_2961_ = (!lean_is_exclusive(v___x_2953_)) as u8;
                    if v_isSharedCheck_2961_ == 0 {
                        v___x_2956_ = v___x_2953_;
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2954_);
                        lean_dec(v___x_2953_);
                        v___x_2956_ = lean_box(0);
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
                    v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
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
    mut v_type_2962_: *mut LeanObject,
    mut v_k_2963_: *mut LeanObject,
    mut v_cleanupAnnotations_2964_: *mut LeanObject,
    mut v_whnfType_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
    mut v___y_2967_: *mut LeanObject,
    mut v___y_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2973_: u8 = 0;
    let mut v_whnfType_boxed_2974_: u8 = 0;
    let mut v_res_2975_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2973_ = (lean_unbox(v_cleanupAnnotations_2964_) as u8);
    v_whnfType_boxed_2974_ = (lean_unbox(v_whnfType_2965_) as u8);
    v_res_2975_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_2962_, v_k_2963_, v_cleanupAnnotations_boxed_2973_, v_whnfType_boxed_2974_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
    lean_dec(v___y_2971_);
    lean_dec_ref(v___y_2970_);
    lean_dec(v___y_2969_);
    lean_dec_ref(v___y_2968_);
    lean_dec(v___y_2967_);
    lean_dec_ref(v___y_2966_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(
    mut v_00_u03b1_2976_: *mut LeanObject,
    mut v_type_2977_: *mut LeanObject,
    mut v_k_2978_: *mut LeanObject,
    mut v_cleanupAnnotations_2979_: u8,
    mut v_whnfType_2980_: u8,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_2977_, v_k_2978_, v_cleanupAnnotations_2979_, v_whnfType_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___boxed(
    mut v_00_u03b1_2989_: *mut LeanObject,
    mut v_type_2990_: *mut LeanObject,
    mut v_k_2991_: *mut LeanObject,
    mut v_cleanupAnnotations_2992_: *mut LeanObject,
    mut v_whnfType_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
    mut v___y_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3001_: u8 = 0;
    let mut v_whnfType_boxed_3002_: u8 = 0;
    let mut v_res_3003_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3001_ = (lean_unbox(v_cleanupAnnotations_2992_) as u8);
    v_whnfType_boxed_3002_ = (lean_unbox(v_whnfType_2993_) as u8);
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
    lean_dec(v___y_2999_);
    lean_dec_ref(v___y_2998_);
    lean_dec(v___y_2997_);
    lean_dec_ref(v___y_2996_);
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    return v_res_3003_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(
    mut v_as_3004_: *mut LeanObject,
    mut v_sz_3005_: usize,
    mut v_i_3006_: usize,
    mut v_b_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    let mut v_a_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v_a_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3012_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
                if v___x_3012_ == 0 {
                    v___x_3013_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3013_, 0, v_b_3007_);
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
                    if lean_obj_tag(v___x_3016_) == 0 {
                        v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
                        lean_inc(v_a_3017_);
                        lean_dec_ref_known(v___x_3016_, 1);
                        v___x_3018_ = l_Lean_LocalDecl_userName(v_a_3017_);
                        lean_dec(v_a_3017_);
                        v___x_3019_ = lean_erase_macro_scopes(v___x_3018_);
                        v___x_3020_ =
                            l_Lean_Core_mkFreshUserName(v___x_3019_, v___y_3009_, v___y_3010_);
                        if lean_obj_tag(v___x_3020_) == 0 {
                            v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
                            lean_inc(v_a_3021_);
                            lean_dec_ref_known(v___x_3020_, 1);
                            v___x_3022_ = lean_array_push(v_b_3007_, v_a_3021_);
                            v___x_3023_ = 1usize;
                            v___x_3024_ = lean_usize_add(v_i_3006_, v___x_3023_);
                            v_i_3006_ = v___x_3024_;
                            v_b_3007_ = v___x_3022_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_b_3007_);
                            v_a_3026_ = lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3033_ = (!lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3033_ == 0 {
                                v___x_3028_ = v___x_3020_;
                                v_isShared_3029_ = v_isSharedCheck_3033_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3026_);
                                lean_dec(v___x_3020_);
                                v___x_3028_ = lean_box(0);
                                v_isShared_3029_ = v_isSharedCheck_3033_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_3007_);
                        v_a_3034_ = lean_ctor_get(v___x_3016_, 0);
                        v_isSharedCheck_3041_ = (!lean_is_exclusive(v___x_3016_)) as u8;
                        if v_isSharedCheck_3041_ == 0 {
                            v___x_3036_ = v___x_3016_;
                            v_isShared_3037_ = v_isSharedCheck_3041_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3034_);
                            lean_dec(v___x_3016_);
                            v___x_3036_ = lean_box(0);
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
                    v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
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
                    v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
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
    mut v_as_3042_: *mut LeanObject,
    mut v_sz_3043_: *mut LeanObject,
    mut v_i_3044_: *mut LeanObject,
    mut v_b_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3050_: usize = 0;
    let mut v_i_boxed_3051_: usize = 0;
    let mut v_res_3052_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3050_ = lean_unbox_usize(v_sz_3043_);
    lean_dec(v_sz_3043_);
    v_i_boxed_3051_ = lean_unbox_usize(v_i_3044_);
    lean_dec(v_i_3044_);
    v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_3042_, v_sz_boxed_3050_, v_i_boxed_3051_, v_b_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
    lean_dec(v___y_3048_);
    lean_dec_ref(v___y_3047_);
    lean_dec_ref(v___y_3046_);
    lean_dec_ref(v_as_3042_);
    return v_res_3052_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___lam__0(
    mut v_xs_3055_: *mut LeanObject,
    mut v_x_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_argNames_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    v_argNames_3064_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
    v_sz_3065_ = lean_array_size(v_xs_3055_);
    v___x_3066_ = 0usize;
    v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_xs_3055_, v_sz_3065_, v___x_3066_, v_argNames_3064_, v___y_3059_, v___y_3061_, v___y_3062_);
    return v___x_3067_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed(
    mut v_xs_3068_: *mut LeanObject,
    mut v_x_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3077_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3075_);
    lean_dec_ref(v___y_3074_);
    lean_dec(v___y_3073_);
    lean_dec_ref(v___y_3072_);
    lean_dec(v___y_3071_);
    lean_dec_ref(v___y_3070_);
    lean_dec_ref(v_x_3069_);
    lean_dec_ref(v_xs_3068_);
    return v_res_3077_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames(
    mut v_indVal_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toConstantVal_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    v_toConstantVal_3087_ = lean_ctor_get(v_indVal_3079_, 0);
    lean_inc_ref(v_toConstantVal_3087_);
    lean_dec_ref(v_indVal_3079_);
    v_type_3088_ = lean_ctor_get(v_toConstantVal_3087_, 2);
    lean_inc_ref(v_type_3088_);
    lean_dec_ref(v_toConstantVal_3087_);
    v___f_3089_ = l_Lean_Elab_Deriving_mkInductArgNames___closed__0;
    v___x_3090_ = 0;
    v___x_3091_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_3088_, v___f_3089_, v___x_3090_, v___x_3090_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
    return v___x_3091_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductArgNames___boxed(
    mut v_indVal_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3100_: *mut LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Lean_Elab_Deriving_mkInductArgNames(
        v_indVal_3092_,
        v_a_3093_,
        v_a_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
    );
    lean_dec(v_a_3098_);
    lean_dec_ref(v_a_3097_);
    lean_dec(v_a_3096_);
    lean_dec_ref(v_a_3095_);
    lean_dec(v_a_3094_);
    lean_dec_ref(v_a_3093_);
    return v_res_3100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(
    mut v_as_3101_: *mut LeanObject,
    mut v_sz_3102_: usize,
    mut v_i_3103_: usize,
    mut v_b_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_3101_, v_sz_3102_, v_i_3103_, v_b_3104_, v___y_3107_, v___y_3109_, v___y_3110_);
    return v___x_3112_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___boxed(
    mut v_as_3113_: *mut LeanObject,
    mut v_sz_3114_: *mut LeanObject,
    mut v_i_3115_: *mut LeanObject,
    mut v_b_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3124_: usize = 0;
    let mut v_i_boxed_3125_: usize = 0;
    let mut v_res_3126_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3124_ = lean_unbox_usize(v_sz_3114_);
    lean_dec(v_sz_3114_);
    v_i_boxed_3125_ = lean_unbox_usize(v_i_3115_);
    lean_dec(v_i_3115_);
    v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(v_as_3113_, v_sz_boxed_3124_, v_i_boxed_3125_, v_b_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
    lean_dec(v___y_3122_);
    lean_dec_ref(v___y_3121_);
    lean_dec(v___y_3120_);
    lean_dec_ref(v___y_3119_);
    lean_dec(v___y_3118_);
    lean_dec_ref(v___y_3117_);
    lean_dec_ref(v_as_3113_);
    return v_res_3126_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(
    mut v_sz_3127_: usize,
    mut v_i_3128_: usize,
    mut v_bs_3129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3130_: u8 = 0;
    let mut v_v_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: usize = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3130_ = lean_usize_dec_lt(v_i_3128_, v_sz_3127_);
                if v___x_3130_ == 0 {
                    return v_bs_3129_;
                } else {
                    v_v_3131_ = lean_array_uget(v_bs_3129_, v_i_3128_);
                    v___x_3132_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3138_: *mut LeanObject,
    mut v_i_3139_: *mut LeanObject,
    mut v_bs_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3141_: usize = 0;
    let mut v_i_boxed_3142_: usize = 0;
    let mut v_res_3143_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3141_ = lean_unbox_usize(v_sz_3138_);
    lean_dec(v_sz_3138_);
    v_i_boxed_3142_ = lean_unbox_usize(v_i_3139_);
    lean_dec(v_i_3139_);
    v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_boxed_3141_, v_i_boxed_3142_, v_bs_3140_);
    return v_res_3143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(
    mut v_sz_3144_: usize,
    mut v_i_3145_: usize,
    mut v_bs_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3147_: u8 = 0;
    let mut v_v_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: usize = 0;
    let mut v___x_3153_: usize = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3147_ = lean_usize_dec_lt(v_i_3145_, v_sz_3144_);
                if v___x_3147_ == 0 {
                    return v_bs_3146_;
                } else {
                    v_v_3148_ = lean_array_uget(v_bs_3146_, v_i_3145_);
                    v___x_3149_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3156_: *mut LeanObject,
    mut v_i_3157_: *mut LeanObject,
    mut v_bs_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3159_: usize = 0;
    let mut v_i_boxed_3160_: usize = 0;
    let mut v_res_3161_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3159_ = lean_unbox_usize(v_sz_3156_);
    lean_dec(v_sz_3156_);
    v_i_boxed_3160_ = lean_unbox_usize(v_i_3157_);
    lean_dec(v_i_3157_);
    v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_boxed_3159_, v_i_boxed_3160_, v_bs_3158_);
    return v_res_3161_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Array_mkArray0(lean_box(0));
    return v___x_3181_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___redArg(
    mut v_indVal_3182_: *mut LeanObject,
    mut v_argNames_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toConstantVal_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v_ref_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3192_: usize = 0;
    let mut v_f_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: usize = 0;
    let mut v_args_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3205_: usize = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_unused_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_3186_ = lean_ctor_get(v_indVal_3182_, 0);
                lean_inc_ref(v_toConstantVal_3186_);
                lean_dec_ref(v_indVal_3182_);
                v_name_3187_ = lean_ctor_get(v_toConstantVal_3186_, 0);
                v_isSharedCheck_3213_ = (!lean_is_exclusive(v_toConstantVal_3186_)) as u8;
                if v_isSharedCheck_3213_ == 0 {
                    v_unused_3214_ = lean_ctor_get(v_toConstantVal_3186_, 2);
                    lean_dec(v_unused_3214_);
                    v_unused_3215_ = lean_ctor_get(v_toConstantVal_3186_, 1);
                    lean_dec(v_unused_3215_);
                    v___x_3189_ = v_toConstantVal_3186_;
                    v_isShared_3190_ = v_isSharedCheck_3213_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_3187_);
                    lean_dec(v_toConstantVal_3186_);
                    v___x_3189_ = lean_box(0);
                    v_isShared_3190_ = v_isSharedCheck_3213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_3191_ = lean_ctor_get(v_a_3184_, 5);
                v_sz_3192_ = lean_array_size(v_argNames_3183_);
                v_f_3193_ = l_Lean_mkCIdent(v_name_3187_);
                v___x_3194_ = 0usize;
                v_args_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_3192_, v___x_3194_, v_argNames_3183_);
                v___x_3196_ = 0;
                v___x_3197_ = l_Lean_SourceInfo_fromRef(v_ref_3191_, v___x_3196_);
                v___x_3198_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                v___x_3199_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6;
                v___x_3200_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7;
                lean_inc_n(v___x_3197_, 3);
                v___x_3201_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3201_, 0, v___x_3197_);
                lean_ctor_set(v___x_3201_, 1, v___x_3200_);
                v___x_3202_ = l_Lean_Syntax_node2(v___x_3197_, v___x_3199_, v___x_3201_, v_f_3193_);
                v___x_3203_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                v___x_3204_ = lean_obj_once(
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
                lean_dec_ref(v___x_3206_);
                if v_isShared_3190_ == 0 {
                    lean_ctor_set_tag(v___x_3189_, 1);
                    lean_ctor_set(v___x_3189_, 2, v___x_3207_);
                    lean_ctor_set(v___x_3189_, 1, v___x_3203_);
                    lean_ctor_set(v___x_3189_, 0, v___x_3197_);
                    v___x_3209_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3197_);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3203_);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 2, v___x_3207_);
                    v___x_3209_ = v_reuseFailAlloc_3212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3210_ =
                    l_Lean_Syntax_node2(v___x_3197_, v___x_3198_, v___x_3202_, v___x_3209_);
                v___x_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                return v___x_3211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___redArg___boxed(
    mut v_indVal_3216_: *mut LeanObject,
    mut v_argNames_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3220_: *mut LeanObject = core::ptr::null_mut();
    v_res_3220_ =
        l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_3216_, v_argNames_3217_, v_a_3218_);
    lean_dec_ref(v_a_3218_);
    return v_res_3220_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp(
    mut v_indVal_3221_: *mut LeanObject,
    mut v_argNames_3222_: *mut LeanObject,
    mut v_a_3223_: *mut LeanObject,
    mut v_a_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    v___x_3230_ =
        l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_3221_, v_argNames_3222_, v_a_3227_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInductiveApp___boxed(
    mut v_indVal_3231_: *mut LeanObject,
    mut v_argNames_3232_: *mut LeanObject,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3240_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3238_);
    lean_dec_ref(v_a_3237_);
    lean_dec(v_a_3236_);
    lean_dec_ref(v_a_3235_);
    lean_dec(v_a_3234_);
    lean_dec_ref(v_a_3233_);
    return v_res_3240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(
    mut v_sz_3249_: usize,
    mut v_i_3250_: usize,
    mut v_bs_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: usize = 0;
    let mut v___x_3274_: usize = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3254_ = lean_usize_dec_lt(v_i_3250_, v_sz_3249_);
                if v___x_3254_ == 0 {
                    v___x_3255_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3255_, 0, v_bs_3251_);
                    return v___x_3255_;
                } else {
                    v_ref_3256_ = lean_ctor_get(v___y_3252_, 5);
                    v_v_3257_ = lean_array_uget(v_bs_3251_, v_i_3250_);
                    v___x_3258_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3259_ = lean_array_uset(v_bs_3251_, v_i_3250_, v___x_3258_);
                    v___x_3260_ = 0;
                    v___x_3261_ = l_Lean_SourceInfo_fromRef(v_ref_3256_, v___x_3260_);
                    v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1;
                    v___x_3263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2;
                    lean_inc_n(v___x_3261_, 4);
                    v___x_3264_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3264_, 0, v___x_3261_);
                    lean_ctor_set(v___x_3264_, 1, v___x_3263_);
                    v___x_3265_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_3266_ = lean_mk_syntax_ident(v_v_3257_);
                    v___x_3267_ = l_Lean_Syntax_node1(v___x_3261_, v___x_3265_, v___x_3266_);
                    v___x_3268_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_3269_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3269_, 0, v___x_3261_);
                    lean_ctor_set(v___x_3269_, 1, v___x_3265_);
                    lean_ctor_set(v___x_3269_, 2, v___x_3268_);
                    v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3;
                    v___x_3271_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3271_, 0, v___x_3261_);
                    lean_ctor_set(v___x_3271_, 1, v___x_3270_);
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
    mut v_sz_3277_: *mut LeanObject,
    mut v_i_3278_: *mut LeanObject,
    mut v_bs_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3282_: usize = 0;
    let mut v_i_boxed_3283_: usize = 0;
    let mut v_res_3284_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3277_);
    lean_dec(v_sz_3277_);
    v_i_boxed_3283_ = lean_unbox_usize(v_i_3278_);
    lean_dec(v_i_3278_);
    v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_boxed_3282_, v_i_boxed_3283_, v_bs_3279_, v___y_3280_);
    lean_dec_ref(v___y_3280_);
    return v_res_3284_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkImplicitBinders(
    mut v_argNames_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
    mut v_a_3289_: *mut LeanObject,
    mut v_a_3290_: *mut LeanObject,
    mut v_a_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3293_: usize = 0;
    let mut v___x_3294_: usize = 0;
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3293_ = lean_array_size(v_argNames_3285_);
    v___x_3294_ = 0usize;
    v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_3293_, v___x_3294_, v_argNames_3285_, v_a_3290_);
    return v___x_3295_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkImplicitBinders___boxed(
    mut v_argNames_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3304_: *mut LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_Lean_Elab_Deriving_mkImplicitBinders(
        v_argNames_3296_,
        v_a_3297_,
        v_a_3298_,
        v_a_3299_,
        v_a_3300_,
        v_a_3301_,
        v_a_3302_,
    );
    lean_dec(v_a_3302_);
    lean_dec_ref(v_a_3301_);
    lean_dec(v_a_3300_);
    lean_dec_ref(v_a_3299_);
    lean_dec(v_a_3298_);
    lean_dec_ref(v_a_3297_);
    return v_res_3304_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(
    mut v_sz_3305_: usize,
    mut v_i_3306_: usize,
    mut v_bs_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_3305_, v_i_3306_, v_bs_3307_, v___y_3312_);
    return v___x_3315_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___boxed(
    mut v_sz_3316_: *mut LeanObject,
    mut v_i_3317_: *mut LeanObject,
    mut v_bs_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3326_: usize = 0;
    let mut v_i_boxed_3327_: usize = 0;
    let mut v_res_3328_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3326_ = lean_unbox_usize(v_sz_3316_);
    lean_dec(v_sz_3316_);
    v_i_boxed_3327_ = lean_unbox_usize(v_i_3317_);
    lean_dec(v_i_3317_);
    v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(v_sz_boxed_3326_, v_i_boxed_3327_, v_bs_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
    lean_dec(v___y_3324_);
    lean_dec_ref(v___y_3323_);
    lean_dec(v___y_3322_);
    lean_dec_ref(v___y_3321_);
    lean_dec(v___y_3320_);
    lean_dec_ref(v___y_3319_);
    return v_res_3328_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(
    mut v_type_3329_: *mut LeanObject,
    mut v_maxFVars_x3f_3330_: *mut LeanObject,
    mut v_k_3331_: *mut LeanObject,
    mut v_cleanupAnnotations_3332_: u8,
    mut v_whnfType_3333_: u8,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3346_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3335_);
                lean_inc_ref(v___y_3334_);
                v___f_3341_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_3341_, 0, v_k_3331_);
                lean_closure_set(v___f_3341_, 1, v___y_3334_);
                lean_closure_set(v___f_3341_, 2, v___y_3335_);
                v___x_3342_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3342_) == 0 {
                    return v___x_3342_;
                } else {
                    v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
                    v_isSharedCheck_3350_ = (!lean_is_exclusive(v___x_3342_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3345_ = v___x_3342_;
                        v_isShared_3346_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3343_);
                        lean_dec(v___x_3342_);
                        v___x_3345_ = lean_box(0);
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
                    v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
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
    mut v_type_3351_: *mut LeanObject,
    mut v_maxFVars_x3f_3352_: *mut LeanObject,
    mut v_k_3353_: *mut LeanObject,
    mut v_cleanupAnnotations_3354_: *mut LeanObject,
    mut v_whnfType_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3363_: u8 = 0;
    let mut v_whnfType_boxed_3364_: u8 = 0;
    let mut v_res_3365_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3363_ = (lean_unbox(v_cleanupAnnotations_3354_) as u8);
    v_whnfType_boxed_3364_ = (lean_unbox(v_whnfType_3355_) as u8);
    v_res_3365_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3351_, v_maxFVars_x3f_3352_, v_k_3353_, v_cleanupAnnotations_boxed_3363_, v_whnfType_boxed_3364_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    lean_dec(v___y_3361_);
    lean_dec_ref(v___y_3360_);
    lean_dec(v___y_3359_);
    lean_dec_ref(v___y_3358_);
    lean_dec(v___y_3357_);
    lean_dec_ref(v___y_3356_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(
    mut v_00_u03b1_3366_: *mut LeanObject,
    mut v_type_3367_: *mut LeanObject,
    mut v_maxFVars_x3f_3368_: *mut LeanObject,
    mut v_k_3369_: *mut LeanObject,
    mut v_cleanupAnnotations_3370_: u8,
    mut v_whnfType_3371_: u8,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3367_, v_maxFVars_x3f_3368_, v_k_3369_, v_cleanupAnnotations_3370_, v_whnfType_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___boxed(
    mut v_00_u03b1_3380_: *mut LeanObject,
    mut v_type_3381_: *mut LeanObject,
    mut v_maxFVars_x3f_3382_: *mut LeanObject,
    mut v_k_3383_: *mut LeanObject,
    mut v_cleanupAnnotations_3384_: *mut LeanObject,
    mut v_whnfType_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_3393_: u8 = 0;
    let mut v_whnfType_boxed_3394_: u8 = 0;
    let mut v_res_3395_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3393_ = (lean_unbox(v_cleanupAnnotations_3384_) as u8);
    v_whnfType_boxed_3394_ = (lean_unbox(v_whnfType_3385_) as u8);
    v_res_3395_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(v_00_u03b1_3380_, v_type_3381_, v_maxFVars_x3f_3382_, v_k_3383_, v_cleanupAnnotations_boxed_3393_, v_whnfType_boxed_3394_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    lean_dec(v___y_3391_);
    lean_dec_ref(v___y_3390_);
    lean_dec(v___y_3389_);
    lean_dec_ref(v___y_3388_);
    lean_dec(v___y_3387_);
    lean_dec_ref(v___y_3386_);
    return v_res_3395_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(
    mut v_upperBound_3404_: *mut LeanObject,
    mut v_xs_3405_: *mut LeanObject,
    mut v_className_3406_: *mut LeanObject,
    mut v_argNames_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
    mut v_b_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: u8 = 0;
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v_ref_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3428_ = lean_nat_dec_lt(v_a_3408_, v_upperBound_3404_);
                if v___x_3428_ == 0 {
                    lean_dec(v_a_3408_);
                    lean_dec(v_className_3406_);
                    v___x_3429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3429_, 0, v_b_3409_);
                    return v___x_3429_;
                } else {
                    v___x_3430_ = lean_array_fget_borrowed(v_xs_3405_, v_a_3408_);
                    v___x_3431_ = lean_unsigned_to_nat(1);
                    v___x_3432_ = lean_mk_empty_array_with_capacity(v___x_3431_);
                    lean_inc(v___x_3430_);
                    v___x_3433_ = lean_array_push(v___x_3432_, v___x_3430_);
                    lean_inc(v_className_3406_);
                    v___x_3434_ = l_Lean_Meta_mkAppM(
                        v_className_3406_,
                        v___x_3433_,
                        v___y_3410_,
                        v___y_3411_,
                        v___y_3412_,
                        v___y_3413_,
                    );
                    if lean_obj_tag(v___x_3434_) == 0 {
                        v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
                        lean_inc(v_a_3435_);
                        lean_dec_ref_known(v___x_3434_, 1);
                        v___x_3436_ = l_Lean_Meta_isTypeCorrect(
                            v_a_3435_,
                            v___y_3410_,
                            v___y_3411_,
                            v___y_3412_,
                            v___y_3413_,
                        );
                        if lean_obj_tag(v___x_3436_) == 0 {
                            v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
                            lean_inc(v_a_3437_);
                            lean_dec_ref_known(v___x_3436_, 1);
                            v___x_3438_ = (lean_unbox(v_a_3437_) as u8);
                            lean_dec(v_a_3437_);
                            if v___x_3438_ == 0 {
                                v_snd_3416_ = v_b_3409_;
                                state = 1;
                                continue;
                            } else {
                                v_ref_3439_ = lean_ctor_get(v___y_3412_, 5);
                                v___x_3440_ = lean_box(0);
                                v___x_3441_ = lean_array_get_borrowed(
                                    v___x_3440_,
                                    v_argNames_3407_,
                                    v_a_3408_,
                                );
                                v___x_3442_ = 0;
                                v___x_3443_ = l_Lean_SourceInfo_fromRef(v_ref_3439_, v___x_3442_);
                                v___x_3444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1;
                                v___x_3445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2;
                                lean_inc_n(v___x_3443_, 5);
                                v___x_3446_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_3446_, 0, v___x_3443_);
                                lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                                v___x_3447_ =
                                    l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                v___x_3448_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once), _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
                                v___x_3449_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_3449_, 0, v___x_3443_);
                                lean_ctor_set(v___x_3449_, 1, v___x_3447_);
                                lean_ctor_set(v___x_3449_, 2, v___x_3448_);
                                v___x_3450_ =
                                    l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                lean_inc(v_className_3406_);
                                v___x_3451_ = l_Lean_mkCIdent(v_className_3406_);
                                lean_inc(v___x_3441_);
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
                                v___x_3456_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_3456_, 0, v___x_3443_);
                                lean_ctor_set(v___x_3456_, 1, v___x_3455_);
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
                            v_a_3459_ = lean_ctor_get(v___x_3436_, 0);
                            lean_inc(v_a_3459_);
                            lean_dec_ref_known(v___x_3436_, 1);
                            v_a_3425_ = v_a_3459_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3460_ = lean_ctor_get(v___x_3434_, 0);
                        lean_inc(v_a_3460_);
                        lean_dec_ref_known(v___x_3434_, 1);
                        v_a_3425_ = v_a_3460_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3417_ = lean_unsigned_to_nat(1);
                v___x_3418_ = lean_nat_add(v_a_3408_, v___x_3417_);
                lean_dec(v_a_3408_);
                v_a_3408_ = v___x_3418_;
                v_b_3409_ = v_snd_3416_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3422_ == 0 {
                    lean_dec_ref(v___y_3421_);
                    v_snd_3416_ = v_b_3409_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_b_3409_);
                    lean_dec(v_a_3408_);
                    lean_dec(v_className_3406_);
                    v___x_3423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3423_, 0, v___y_3421_);
                    return v___x_3423_;
                }
            }
            3 => {
                v___x_3426_ = l_Lean_Exception_isInterrupt(v_a_3425_);
                if v___x_3426_ == 0 {
                    lean_inc_ref(v_a_3425_);
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
    mut v_upperBound_3461_: *mut LeanObject,
    mut v_xs_3462_: *mut LeanObject,
    mut v_className_3463_: *mut LeanObject,
    mut v_argNames_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
    mut v_b_3466_: *mut LeanObject,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3472_: *mut LeanObject = core::ptr::null_mut();
    v_res_3472_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_3461_, v_xs_3462_, v_className_3463_, v_argNames_3464_, v_a_3465_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
    lean_dec(v___y_3470_);
    lean_dec_ref(v___y_3469_);
    lean_dec(v___y_3468_);
    lean_dec_ref(v___y_3467_);
    lean_dec_ref(v_argNames_3464_);
    lean_dec_ref(v_xs_3462_);
    lean_dec(v_upperBound_3461_);
    return v_res_3472_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(
    mut v_className_3475_: *mut LeanObject,
    mut v_argNames_3476_: *mut LeanObject,
    mut v_xs_3477_: *mut LeanObject,
    mut v_x_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binders_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_array_get_size(v_xs_3477_);
    v___x_3487_ = lean_unsigned_to_nat(0);
    v_binders_3488_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
    v___x_3489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v___x_3486_, v_xs_3477_, v_className_3475_, v_argNames_3476_, v___x_3487_, v_binders_3488_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    return v___x_3489_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(
    mut v_className_3490_: *mut LeanObject,
    mut v_argNames_3491_: *mut LeanObject,
    mut v_xs_3492_: *mut LeanObject,
    mut v_x_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3501_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3499_);
    lean_dec_ref(v___y_3498_);
    lean_dec(v___y_3497_);
    lean_dec_ref(v___y_3496_);
    lean_dec(v___y_3495_);
    lean_dec_ref(v___y_3494_);
    lean_dec_ref(v_x_3493_);
    lean_dec_ref(v_xs_3492_);
    lean_dec_ref(v_argNames_3491_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders(
    mut v_className_3502_: *mut LeanObject,
    mut v_indVal_3503_: *mut LeanObject,
    mut v_argNames_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
    mut v_a_3507_: *mut LeanObject,
    mut v_a_3508_: *mut LeanObject,
    mut v_a_3509_: *mut LeanObject,
    mut v_a_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toConstantVal_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v_toConstantVal_3512_ = lean_ctor_get(v_indVal_3503_, 0);
    lean_inc_ref(v_toConstantVal_3512_);
    v_numParams_3513_ = lean_ctor_get(v_indVal_3503_, 1);
    lean_inc(v_numParams_3513_);
    lean_dec_ref(v_indVal_3503_);
    v_type_3514_ = lean_ctor_get(v_toConstantVal_3512_, 2);
    lean_inc_ref(v_type_3514_);
    lean_dec_ref(v_toConstantVal_3512_);
    v___f_3515_ = lean_alloc_closure(
        l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___f_3515_, 0, v_className_3502_);
    lean_closure_set(v___f_3515_, 1, v_argNames_3504_);
    v___x_3516_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3516_, 0, v_numParams_3513_);
    v___x_3517_ = 0;
    v___x_3518_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_3514_, v___x_3516_, v___f_3515_, v___x_3517_, v___x_3517_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(
    mut v_className_3519_: *mut LeanObject,
    mut v_indVal_3520_: *mut LeanObject,
    mut v_argNames_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3529_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3527_);
    lean_dec_ref(v_a_3526_);
    lean_dec(v_a_3525_);
    lean_dec_ref(v_a_3524_);
    lean_dec(v_a_3523_);
    lean_dec_ref(v_a_3522_);
    return v_res_3529_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(
    mut v_upperBound_3530_: *mut LeanObject,
    mut v_xs_3531_: *mut LeanObject,
    mut v_className_3532_: *mut LeanObject,
    mut v_argNames_3533_: *mut LeanObject,
    mut v_inst_3534_: *mut LeanObject,
    mut v_R_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_b_3537_: *mut LeanObject,
    mut v_c_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
    mut v___y_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_3530_, v_xs_3531_, v_className_3532_, v_argNames_3533_, v_a_3536_, v_b_3537_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
    return v___x_3546_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(
    mut v_upperBound_3547_: *mut LeanObject,
    mut v_xs_3548_: *mut LeanObject,
    mut v_className_3549_: *mut LeanObject,
    mut v_argNames_3550_: *mut LeanObject,
    mut v_inst_3551_: *mut LeanObject,
    mut v_R_3552_: *mut LeanObject,
    mut v_a_3553_: *mut LeanObject,
    mut v_b_3554_: *mut LeanObject,
    mut v_c_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3563_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3561_);
    lean_dec_ref(v___y_3560_);
    lean_dec(v___y_3559_);
    lean_dec_ref(v___y_3558_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec_ref(v_argNames_3550_);
    lean_dec_ref(v_xs_3548_);
    lean_dec(v_upperBound_3547_);
    return v_res_3563_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
    mut v___x_3586_: u8,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___y_3596_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: u8 = 0;
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: u8 = 0;
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3587_) == 0 {
                    v___x_3589_ = l_List_reverse___redArg(v_a_3588_);
                    return v___x_3589_;
                } else {
                    v_head_3590_ = lean_ctor_get(v_a_3587_, 0);
                    v_tail_3591_ = lean_ctor_get(v_a_3587_, 1);
                    v_isSharedCheck_3620_ = (!lean_is_exclusive(v_a_3587_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3593_ = v_a_3587_;
                        v_isShared_3594_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3591_);
                        lean_inc(v_head_3590_);
                        lean_dec(v_a_3587_);
                        v___x_3593_ = lean_box(0);
                        v_isShared_3594_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3602_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1;
                lean_inc(v_head_3590_);
                v___x_3603_ = l_Lean_Syntax_isOfKind(v_head_3590_, v___x_3602_);
                if v___x_3603_ == 0 {
                    v___y_3596_ = v___x_3586_;
                    state = 2;
                    continue;
                } else {
                    v___x_3604_ = lean_unsigned_to_nat(0);
                    v___x_3605_ = l_Lean_Syntax_getArg(v_head_3590_, v___x_3604_);
                    v___x_3606_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3;
                    lean_inc(v___x_3605_);
                    v___x_3607_ = l_Lean_Syntax_isOfKind(v___x_3605_, v___x_3606_);
                    if v___x_3607_ == 0 {
                        lean_dec(v___x_3605_);
                        v___y_3596_ = v___x_3586_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3608_ = l_Lean_Syntax_getArg(v___x_3605_, v___x_3604_);
                        lean_dec(v___x_3605_);
                        v___x_3609_ = l_Lean_Syntax_matchesNull(v___x_3608_, v___x_3604_);
                        if v___x_3609_ == 0 {
                            v___y_3596_ = v___x_3607_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3610_ = lean_unsigned_to_nat(1);
                            v___x_3611_ = l_Lean_Syntax_getArg(v_head_3590_, v___x_3610_);
                            v___x_3612_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6;
                            lean_inc(v___x_3611_);
                            v___x_3613_ = l_Lean_Syntax_isOfKind(v___x_3611_, v___x_3612_);
                            if v___x_3613_ == 0 {
                                lean_dec(v___x_3611_);
                                v___y_3596_ = v___x_3609_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3614_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3604_);
                                v___x_3615_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8;
                                v___x_3616_ = l_Lean_Syntax_matchesIdent(v___x_3614_, v___x_3615_);
                                lean_dec(v___x_3614_);
                                if v___x_3616_ == 0 {
                                    lean_dec(v___x_3611_);
                                    v___y_3596_ = v___x_3613_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3617_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3610_);
                                    lean_dec(v___x_3611_);
                                    v___x_3618_ =
                                        l_Lean_Syntax_matchesNull(v___x_3617_, v___x_3604_);
                                    if v___x_3618_ == 0 {
                                        v___y_3596_ = v___x_3616_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_3593_);
                                        lean_dec(v_head_3590_);
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
                    lean_del_object(v___x_3593_);
                    lean_dec(v_head_3590_);
                    v_a_3587_ = v_tail_3591_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_3594_ == 0 {
                        lean_ctor_set(v___x_3593_, 1, v_a_3588_);
                        v___x_3599_ = v___x_3593_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_head_3590_);
                        lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_a_3588_);
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
    mut v___x_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5393__boxed_3624_: u8 = 0;
    let mut v_res_3625_: *mut LeanObject = core::ptr::null_mut();
    v___x_5393__boxed_3624_ = (lean_unbox(v___x_3621_) as u8);
    v_res_3625_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
        v___x_5393__boxed_3624_,
        v_a_3622_,
        v_a_3623_,
    );
    return v_res_3625_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(
    mut v___x_3626_: u8,
    mut v_sc_3627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_header_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelNames_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varDecls_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varUIds_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includedVars_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_3637_: u8 = 0;
    let mut v_isPublic_3638_: u8 = 0;
    let mut v_isMeta_3639_: u8 = 0;
    let mut v_attrs_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_3628_ = lean_ctor_get(v_sc_3627_, 0);
                v_opts_3629_ = lean_ctor_get(v_sc_3627_, 1);
                v_currNamespace_3630_ = lean_ctor_get(v_sc_3627_, 2);
                v_openDecls_3631_ = lean_ctor_get(v_sc_3627_, 3);
                v_levelNames_3632_ = lean_ctor_get(v_sc_3627_, 4);
                v_varDecls_3633_ = lean_ctor_get(v_sc_3627_, 5);
                v_varUIds_3634_ = lean_ctor_get(v_sc_3627_, 6);
                v_includedVars_3635_ = lean_ctor_get(v_sc_3627_, 7);
                v_omittedVars_3636_ = lean_ctor_get(v_sc_3627_, 8);
                v_isNoncomputable_3637_ = lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isPublic_3638_ = lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_3639_ = lean_ctor_get_uint8(
                    v_sc_3627_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_3640_ = lean_ctor_get(v_sc_3627_, 9);
                v_isSharedCheck_3649_ = (!lean_is_exclusive(v_sc_3627_)) as u8;
                if v_isSharedCheck_3649_ == 0 {
                    v___x_3642_ = v_sc_3627_;
                    v_isShared_3643_ = v_isSharedCheck_3649_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_attrs_3640_);
                    lean_inc(v_omittedVars_3636_);
                    lean_inc(v_includedVars_3635_);
                    lean_inc(v_varUIds_3634_);
                    lean_inc(v_varDecls_3633_);
                    lean_inc(v_levelNames_3632_);
                    lean_inc(v_openDecls_3631_);
                    lean_inc(v_currNamespace_3630_);
                    lean_inc(v_opts_3629_);
                    lean_inc(v_header_3628_);
                    lean_dec(v_sc_3627_);
                    v___x_3642_ = lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3644_ = lean_box(0);
                v___x_3645_ =
                    l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(
                        v___x_3626_,
                        v_attrs_3640_,
                        v___x_3644_,
                    );
                if v_isShared_3643_ == 0 {
                    lean_ctor_set(v___x_3642_, 9, v___x_3645_);
                    v___x_3647_ = v___x_3642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 10, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_header_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_opts_3629_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_currNamespace_3630_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_openDecls_3631_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_levelNames_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 5, v_varDecls_3633_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 6, v_varUIds_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 7, v_includedVars_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 8, v_omittedVars_3636_);
                    lean_ctor_set(v_reuseFailAlloc_3648_, 9, v___x_3645_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_isNoncomputable_3637_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 1) as u32,
                        v_isPublic_3638_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3648_,
                        (core::mem::size_of::<*mut LeanObject>() * 10 + 2) as u32,
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
    mut v___x_3650_: *mut LeanObject,
    mut v_sc_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5488__boxed_3652_: u8 = 0;
    let mut v_res_3653_: *mut LeanObject = core::ptr::null_mut();
    v___x_5488__boxed_3652_ = (lean_unbox(v___x_3650_) as u8);
    v_res_3653_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(
        v___x_5488__boxed_3652_,
        v_sc_3651_,
    );
    return v_res_3653_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0()
-> *mut LeanObject {
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    v___x_3654_ = lean_box(1);
    v___x_3655_ = l_Lean_MessageData_ofFormat(v___x_3654_);
    return v___x_3655_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3()
-> *mut LeanObject {
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2;
    v___x_3660_ = l_Lean_MessageData_ofFormat(v___x_3659_);
    return v___x_3660_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(
    mut v_x_3661_: *mut LeanObject,
    mut v_x_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v_before_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3662_) == 0 {
                    return v_x_3661_;
                } else {
                    v_head_3663_ = lean_ctor_get(v_x_3662_, 0);
                    v_tail_3664_ = lean_ctor_get(v_x_3662_, 1);
                    v_isSharedCheck_3686_ = (!lean_is_exclusive(v_x_3662_)) as u8;
                    if v_isSharedCheck_3686_ == 0 {
                        v___x_3666_ = v_x_3662_;
                        v_isShared_3667_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3664_);
                        lean_inc(v_head_3663_);
                        lean_dec(v_x_3662_);
                        v___x_3666_ = lean_box(0);
                        v_isShared_3667_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3668_ = lean_ctor_get(v_head_3663_, 0);
                v_isSharedCheck_3684_ = (!lean_is_exclusive(v_head_3663_)) as u8;
                if v_isSharedCheck_3684_ == 0 {
                    v_unused_3685_ = lean_ctor_get(v_head_3663_, 1);
                    lean_dec(v_unused_3685_);
                    v___x_3670_ = v_head_3663_;
                    v_isShared_3671_ = v_isSharedCheck_3684_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3668_);
                    lean_dec(v_head_3663_);
                    v___x_3670_ = lean_box(0);
                    v_isShared_3671_ = v_isSharedCheck_3684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3672_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3671_ == 0 {
                    lean_ctor_set_tag(v___x_3670_, 7);
                    lean_ctor_set(v___x_3670_, 1, v___x_3672_);
                    lean_ctor_set(v___x_3670_, 0, v_x_3661_);
                    v___x_3674_ = v___x_3670_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_x_3661_);
                    lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___x_3672_);
                    v___x_3674_ = v_reuseFailAlloc_3683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3675_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3);
                if v_isShared_3667_ == 0 {
                    lean_ctor_set_tag(v___x_3666_, 7);
                    lean_ctor_set(v___x_3666_, 1, v___x_3675_);
                    lean_ctor_set(v___x_3666_, 0, v___x_3674_);
                    v___x_3677_ = v___x_3666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3674_);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3675_);
                    v___x_3677_ = v_reuseFailAlloc_3682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3678_ = l_Lean_MessageData_ofSyntax(v_before_3668_);
                v___x_3679_ = l_Lean_indentD(v___x_3678_);
                v___x_3680_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3680_, 0, v___x_3677_);
                lean_ctor_set(v___x_3680_, 1, v___x_3679_);
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
    mut v_opts_3687_: *mut LeanObject,
    mut v_opt_3688_: *mut LeanObject,
) -> u8 {
    let mut v_name_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v_name_3689_ = lean_ctor_get(v_opt_3688_, 0);
    v_defValue_3690_ = lean_ctor_get(v_opt_3688_, 1);
    v_map_3691_ = lean_ctor_get(v_opts_3687_, 0);
    v___x_3692_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3691_,
            v_name_3689_,
        );
    if lean_obj_tag(v___x_3692_) == 0 {
        let mut v___x_3693_: u8 = 0;
        v___x_3693_ = (lean_unbox(v_defValue_3690_) as u8);
        return v___x_3693_;
    } else {
        let mut v_val_3694_: *mut LeanObject = core::ptr::null_mut();
        v_val_3694_ = lean_ctor_get(v___x_3692_, 0);
        lean_inc(v_val_3694_);
        lean_dec_ref_known(v___x_3692_, 1);
        if lean_obj_tag(v_val_3694_) == 1 {
            let mut v_v_3695_: u8 = 0;
            v_v_3695_ = lean_ctor_get_uint8(v_val_3694_, 0 as u32);
            lean_dec_ref_known(v_val_3694_, 0);
            return v_v_3695_;
        } else {
            let mut v___x_3696_: u8 = 0;
            lean_dec(v_val_3694_);
            v___x_3696_ = (lean_unbox(v_defValue_3690_) as u8);
            return v___x_3696_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(
    mut v_opts_3697_: *mut LeanObject,
    mut v_opt_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3699_: u8 = 0;
    let mut v_r_3700_: *mut LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_3697_, v_opt_3698_);
    lean_dec_ref(v_opt_3698_);
    lean_dec_ref(v_opts_3697_);
    v_r_3700_ = lean_box((v_res_3699_) as usize);
    return v_r_3700_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3704_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1;
    v___x_3705_ = l_Lean_MessageData_ofFormat(v___x_3704_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(
    mut v_msgData_3706_: *mut LeanObject,
    mut v_macroStack_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_unused_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3710_ = lean_st_ref_get(v___y_3708_);
                v_scopes_3711_ = lean_ctor_get(v___x_3710_, 2);
                lean_inc(v_scopes_3711_);
                lean_dec(v___x_3710_);
                v___x_3712_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3713_ = l_List_head_x21___redArg(v___x_3712_, v_scopes_3711_);
                lean_dec(v_scopes_3711_);
                v_opts_3714_ = lean_ctor_get(v___x_3713_, 1);
                lean_inc_ref(v_opts_3714_);
                lean_dec(v___x_3713_);
                v___x_3715_ = l_Lean_Elab_pp_macroStack;
                v___x_3716_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_3714_, v___x_3715_);
                lean_dec_ref(v_opts_3714_);
                if v___x_3716_ == 0 {
                    lean_dec(v_macroStack_3707_);
                    v___x_3717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3717_, 0, v_msgData_3706_);
                    return v___x_3717_;
                } else {
                    if lean_obj_tag(v_macroStack_3707_) == 0 {
                        v___x_3718_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3718_, 0, v_msgData_3706_);
                        return v___x_3718_;
                    } else {
                        v_head_3719_ = lean_ctor_get(v_macroStack_3707_, 0);
                        lean_inc(v_head_3719_);
                        v_after_3720_ = lean_ctor_get(v_head_3719_, 1);
                        v_isSharedCheck_3735_ = (!lean_is_exclusive(v_head_3719_)) as u8;
                        if v_isSharedCheck_3735_ == 0 {
                            v_unused_3736_ = lean_ctor_get(v_head_3719_, 0);
                            lean_dec(v_unused_3736_);
                            v___x_3722_ = v_head_3719_;
                            v_isShared_3723_ = v_isSharedCheck_3735_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3720_);
                            lean_dec(v_head_3719_);
                            v___x_3722_ = lean_box(0);
                            v_isShared_3723_ = v_isSharedCheck_3735_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3724_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3723_ == 0 {
                    lean_ctor_set_tag(v___x_3722_, 7);
                    lean_ctor_set(v___x_3722_, 1, v___x_3724_);
                    lean_ctor_set(v___x_3722_, 0, v_msgData_3706_);
                    v___x_3726_ = v___x_3722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_msgData_3706_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3724_);
                    v___x_3726_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3727_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
                v___x_3728_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3728_, 0, v___x_3726_);
                lean_ctor_set(v___x_3728_, 1, v___x_3727_);
                v___x_3729_ = l_Lean_MessageData_ofSyntax(v_after_3720_);
                v___x_3730_ = l_Lean_indentD(v___x_3729_);
                v_msgData_3731_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3731_, 0, v___x_3728_);
                lean_ctor_set(v_msgData_3731_, 1, v___x_3730_);
                v___x_3732_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_3731_, v_macroStack_3707_);
                v___x_3733_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3733_, 0, v___x_3732_);
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(
    mut v_msgData_3737_: *mut LeanObject,
    mut v_macroStack_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_3737_, v_macroStack_3738_, v___y_3739_);
    lean_dec(v___y_3739_);
    return v_res_3741_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    v___x_3742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___x_3743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0);
    v___x_3744_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3744_, 0, v___x_3743_);
    return v___x_3744_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
    v___x_3746_ = lean_unsigned_to_nat(0);
    v___x_3747_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3747_, 0, v___x_3746_);
    lean_ctor_set(v___x_3747_, 1, v___x_3746_);
    lean_ctor_set(v___x_3747_, 2, v___x_3746_);
    lean_ctor_set(v___x_3747_, 3, v___x_3746_);
    lean_ctor_set(v___x_3747_, 4, v___x_3745_);
    lean_ctor_set(v___x_3747_, 5, v___x_3745_);
    lean_ctor_set(v___x_3747_, 6, v___x_3745_);
    lean_ctor_set(v___x_3747_, 7, v___x_3745_);
    lean_ctor_set(v___x_3747_, 8, v___x_3745_);
    lean_ctor_set(v___x_3747_, 9, v___x_3745_);
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    v___x_3748_ = lean_unsigned_to_nat(32);
    v___x_3749_ = lean_mk_empty_array_with_capacity(v___x_3748_);
    v___x_3750_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3750_, 0, v___x_3749_);
    return v___x_3750_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3751_: usize = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    v___x_3751_ = 5usize;
    v___x_3752_ = lean_unsigned_to_nat(0);
    v___x_3753_ = lean_unsigned_to_nat(32);
    v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
    v___x_3755_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3);
    v___x_3756_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3756_, 0, v___x_3755_);
    lean_ctor_set(v___x_3756_, 1, v___x_3754_);
    lean_ctor_set(v___x_3756_, 2, v___x_3752_);
    lean_ctor_set(v___x_3756_, 3, v___x_3752_);
    lean_ctor_set_usize(v___x_3756_, 4, v___x_3751_);
    return v___x_3756_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = lean_box(1);
    v___x_3758_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4);
    v___x_3759_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
    v___x_3760_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3760_, 0, v___x_3759_);
    lean_ctor_set(v___x_3760_, 1, v___x_3758_);
    lean_ctor_set(v___x_3760_, 2, v___x_3757_);
    return v___x_3760_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(
    mut v_msgData_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    v___x_3764_ = lean_st_ref_get(v___y_3762_);
    v_env_3765_ = lean_ctor_get(v___x_3764_, 0);
    lean_inc_ref(v_env_3765_);
    lean_dec(v___x_3764_);
    v___x_3766_ = lean_st_ref_get(v___y_3762_);
    v_scopes_3767_ = lean_ctor_get(v___x_3766_, 2);
    lean_inc(v_scopes_3767_);
    lean_dec(v___x_3766_);
    v___x_3768_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3769_ = l_List_head_x21___redArg(v___x_3768_, v_scopes_3767_);
    lean_dec(v_scopes_3767_);
    v_opts_3770_ = lean_ctor_get(v___x_3769_, 1);
    lean_inc_ref(v_opts_3770_);
    lean_dec(v___x_3769_);
    v___x_3771_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
    v___x_3772_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
    v___x_3773_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3773_, 0, v_env_3765_);
    lean_ctor_set(v___x_3773_, 1, v___x_3771_);
    lean_ctor_set(v___x_3773_, 2, v___x_3772_);
    lean_ctor_set(v___x_3773_, 3, v_opts_3770_);
    v___x_3774_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3774_, 0, v___x_3773_);
    lean_ctor_set(v___x_3774_, 1, v_msgData_3761_);
    v___x_3775_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3775_, 0, v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(
    mut v_msgData_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3779_: *mut LeanObject = core::ptr::null_mut();
    v_res_3779_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_3776_, v___y_3777_);
    lean_dec(v___y_3777_);
    return v_res_3779_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
    mut v_msg_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
    mut v___y_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_a_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3784_ = l_Lean_Elab_Command_getRef___redArg(v___y_3781_);
                if lean_obj_tag(v___x_3784_) == 0 {
                    v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
                    lean_inc(v_a_3785_);
                    lean_dec_ref_known(v___x_3784_, 1);
                    v_macroStack_3786_ = lean_ctor_get(v___y_3781_, 4);
                    v___x_3787_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msg_3780_, v___y_3782_);
                    v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
                    lean_inc(v_a_3788_);
                    lean_dec_ref(v___x_3787_);
                    v___x_3789_ = l_Lean_Elab_getBetterRef(v_a_3785_, v_macroStack_3786_);
                    lean_dec(v_a_3785_);
                    lean_inc(v_macroStack_3786_);
                    v___x_3790_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_a_3788_, v_macroStack_3786_, v___y_3782_);
                    v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
                    v_isSharedCheck_3799_ = (!lean_is_exclusive(v___x_3790_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3793_ = v___x_3790_;
                        v_isShared_3794_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3791_);
                        lean_dec(v___x_3790_);
                        v___x_3793_ = lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_3780_);
                    v_a_3800_ = lean_ctor_get(v___x_3784_, 0);
                    v_isSharedCheck_3807_ = (!lean_is_exclusive(v___x_3784_)) as u8;
                    if v_isSharedCheck_3807_ == 0 {
                        v___x_3802_ = v___x_3784_;
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3800_);
                        lean_dec(v___x_3784_);
                        v___x_3802_ = lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3807_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3795_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3795_, 0, v___x_3789_);
                lean_ctor_set(v___x_3795_, 1, v_a_3791_);
                if v_isShared_3794_ == 0 {
                    lean_ctor_set_tag(v___x_3793_, 1);
                    lean_ctor_set(v___x_3793_, 0, v___x_3795_);
                    v___x_3797_ = v___x_3793_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
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
                    v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
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
    mut v_msg_3808_: *mut LeanObject,
    mut v___y_3809_: *mut LeanObject,
    mut v___y_3810_: *mut LeanObject,
    mut v___y_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3812_: *mut LeanObject = core::ptr::null_mut();
    v_res_3812_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
            v_msg_3808_,
            v___y_3809_,
            v___y_3810_,
        );
    lean_dec(v___y_3810_);
    lean_dec_ref(v___y_3809_);
    return v_res_3812_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v___x_3814_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0;
    v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2;
    v___x_3818_ = l_Lean_stringToMessageData(v___x_3817_);
    return v___x_3818_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(
    mut v_constName_3819_: *mut LeanObject,
    mut v___y_3820_: *mut LeanObject,
    mut v___y_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3823_ = lean_st_ref_get(v___y_3821_);
                v_env_3824_ = lean_ctor_get(v___x_3823_, 0);
                lean_inc_ref(v_env_3824_);
                lean_dec(v___x_3823_);
                lean_inc(v_constName_3819_);
                v___x_3825_ = l_Lean_isInductiveCore_x3f(v_env_3824_, v_constName_3819_);
                if lean_obj_tag(v___x_3825_) == 0 {
                    v___x_3826_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
                    v___x_3827_ = 0;
                    v___x_3828_ = l_Lean_MessageData_ofConstName(v_constName_3819_, v___x_3827_);
                    v___x_3829_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3829_, 0, v___x_3826_);
                    lean_ctor_set(v___x_3829_, 1, v___x_3828_);
                    v___x_3830_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
                    v___x_3831_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3831_, 0, v___x_3829_);
                    lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                    v___x_3832_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_3831_, v___y_3820_, v___y_3821_);
                    return v___x_3832_;
                } else {
                    lean_dec(v_constName_3819_);
                    v_val_3833_ = lean_ctor_get(v___x_3825_, 0);
                    v_isSharedCheck_3840_ = (!lean_is_exclusive(v___x_3825_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3825_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3833_);
                        lean_dec(v___x_3825_);
                        v___x_3835_ = lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3836_ == 0 {
                    lean_ctor_set_tag(v___x_3835_, 0);
                    v___x_3838_ = v___x_3835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_val_3833_);
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
    mut v_constName_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3845_: *mut LeanObject = core::ptr::null_mut();
    v_res_3845_ =
        l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(
            v_constName_3841_,
            v___y_3842_,
            v___y_3843_,
        );
    lean_dec(v___y_3843_);
    lean_dec_ref(v___y_3842_);
    return v_res_3845_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(
    mut v_as_x27_3846_: *mut LeanObject,
    mut v_b_3847_: *mut LeanObject,
    mut v___y_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3846_) == 0 {
                    v___x_3851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3851_, 0, v_b_3847_);
                    return v___x_3851_;
                } else {
                    v_head_3852_ = lean_ctor_get(v_as_x27_3846_, 0);
                    v_tail_3853_ = lean_ctor_get(v_as_x27_3846_, 1);
                    lean_inc(v_head_3852_);
                    v___x_3854_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_head_3852_, v___y_3848_, v___y_3849_);
                    if lean_obj_tag(v___x_3854_) == 0 {
                        v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
                        lean_inc(v_a_3855_);
                        lean_dec_ref_known(v___x_3854_, 1);
                        v___x_3856_ = lean_array_push(v_b_3847_, v_a_3855_);
                        v_as_x27_3846_ = v_tail_3853_;
                        v_b_3847_ = v___x_3856_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_3847_);
                        v_a_3858_ = lean_ctor_get(v___x_3854_, 0);
                        v_isSharedCheck_3865_ = (!lean_is_exclusive(v___x_3854_)) as u8;
                        if v_isSharedCheck_3865_ == 0 {
                            v___x_3860_ = v___x_3854_;
                            v_isShared_3861_ = v_isSharedCheck_3865_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3858_);
                            lean_dec(v___x_3854_);
                            v___x_3860_ = lean_box(0);
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
                    v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
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
    mut v_as_x27_3866_: *mut LeanObject,
    mut v_b_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3871_: *mut LeanObject = core::ptr::null_mut();
    v_res_3871_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(
            v_as_x27_3866_,
            v_b_3867_,
            v___y_3868_,
            v___y_3869_,
        );
    lean_dec(v___y_3869_);
    lean_dec_ref(v___y_3868_);
    lean_dec(v_as_x27_3866_);
    return v_res_3871_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(
    mut v___x_3872_: u8,
    mut v_x_3873_: *mut LeanObject,
) -> u8 {
    let mut v___x_3874_: u8 = 0;
    let mut v_head_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3878_: u8 = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3873_) == 0 {
                    v___x_3874_ = 0;
                    return v___x_3874_;
                } else {
                    v_head_3875_ = lean_ctor_get(v_x_3873_, 0);
                    lean_inc_n(v_head_3875_, 2);
                    v_tail_3876_ = lean_ctor_get(v_x_3873_, 1);
                    lean_inc(v_tail_3876_);
                    lean_dec_ref_known(v_x_3873_, 2);
                    v___x_3880_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1;
                    v___x_3881_ = l_Lean_Syntax_isOfKind(v_head_3875_, v___x_3880_);
                    if v___x_3881_ == 0 {
                        lean_dec(v_head_3875_);
                        v___y_3878_ = v___x_3881_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3882_ = lean_unsigned_to_nat(0);
                        v___x_3883_ = l_Lean_Syntax_getArg(v_head_3875_, v___x_3882_);
                        v___x_3884_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3;
                        lean_inc(v___x_3883_);
                        v___x_3885_ = l_Lean_Syntax_isOfKind(v___x_3883_, v___x_3884_);
                        if v___x_3885_ == 0 {
                            lean_dec(v___x_3883_);
                            lean_dec(v_head_3875_);
                            v___y_3878_ = v___x_3885_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3886_ = l_Lean_Syntax_getArg(v___x_3883_, v___x_3882_);
                            lean_dec(v___x_3883_);
                            v___x_3887_ = l_Lean_Syntax_matchesNull(v___x_3886_, v___x_3882_);
                            if v___x_3887_ == 0 {
                                lean_dec(v_head_3875_);
                                v___y_3878_ = v___x_3887_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3888_ = lean_unsigned_to_nat(1);
                                v___x_3889_ = l_Lean_Syntax_getArg(v_head_3875_, v___x_3888_);
                                lean_dec(v_head_3875_);
                                v___x_3890_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6;
                                lean_inc(v___x_3889_);
                                v___x_3891_ = l_Lean_Syntax_isOfKind(v___x_3889_, v___x_3890_);
                                if v___x_3891_ == 0 {
                                    lean_dec(v___x_3889_);
                                    v___y_3878_ = v___x_3891_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3892_ = l_Lean_Syntax_getArg(v___x_3889_, v___x_3882_);
                                    v___x_3893_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8;
                                    v___x_3894_ =
                                        l_Lean_Syntax_matchesIdent(v___x_3892_, v___x_3893_);
                                    lean_dec(v___x_3892_);
                                    if v___x_3894_ == 0 {
                                        lean_dec(v___x_3889_);
                                        v___y_3878_ = v___x_3894_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3895_ =
                                            l_Lean_Syntax_getArg(v___x_3889_, v___x_3888_);
                                        lean_dec(v___x_3889_);
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
                    lean_dec(v_tail_3876_);
                    return v___y_3878_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(
    mut v___x_3897_: *mut LeanObject,
    mut v_x_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5940__boxed_3899_: u8 = 0;
    let mut v_res_3900_: u8 = 0;
    let mut v_r_3901_: *mut LeanObject = core::ptr::null_mut();
    v___x_5940__boxed_3899_ = (lean_unbox(v___x_3897_) as u8);
    v_res_3900_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(
        v___x_5940__boxed_3899_,
        v_x_3898_,
    );
    v_r_3901_ = lean_box((v_res_3900_) as usize);
    return v_r_3901_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(
    mut v_x_3902_: *mut LeanObject,
) -> u8 {
    let mut v___x_3903_: u8 = 0;
    let mut v_head_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3902_) == 0 {
                    v___x_3903_ = 0;
                    return v___x_3903_;
                } else {
                    v_head_3904_ = lean_ctor_get(v_x_3902_, 0);
                    v_tail_3905_ = lean_ctor_get(v_x_3902_, 1);
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
    mut v_x_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3909_: u8 = 0;
    let mut v_r_3910_: *mut LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_3908_);
    lean_dec(v_x_3908_);
    v_r_3910_ = lean_box((v_res_3909_) as usize);
    return v_r_3910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(
    mut v_as_3911_: *mut LeanObject,
    mut v_i_3912_: usize,
    mut v_stop_3913_: usize,
) -> u8 {
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_3916_: *mut LeanObject = core::ptr::null_mut();
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
                    v_ctors_3916_ = lean_ctor_get(v___x_3915_, 4);
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
    mut v_as_3922_: *mut LeanObject,
    mut v_i_3923_: *mut LeanObject,
    mut v_stop_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3925_: usize = 0;
    let mut v_stop_boxed_3926_: usize = 0;
    let mut v_res_3927_: u8 = 0;
    let mut v_r_3928_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3925_ = lean_unbox_usize(v_i_3923_);
    lean_dec(v_i_3923_);
    v_stop_boxed_3926_ = lean_unbox_usize(v_stop_3924_);
    lean_dec(v_stop_3924_);
    v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_3922_, v_i_boxed_3925_, v_stop_boxed_3926_);
    lean_dec_ref(v_as_3922_);
    v_r_3928_ = lean_box((v_res_3927_) as usize);
    return v_r_3928_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1;
    v___x_3933_ = l_Lean_stringToMessageData(v___x_3932_);
    return v___x_3933_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___x_3935_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3;
    v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
    mut v_typeName_3937_: *mut LeanObject,
    mut v_cont_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_a_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_typeName_3937_);
                v___x_3942_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_typeName_3937_, v_a_3939_, v_a_3940_);
                if lean_obj_tag(v___x_3942_) == 0 {
                    v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
                    lean_inc(v_a_3943_);
                    lean_dec_ref_known(v___x_3942_, 1);
                    v_all_3944_ = lean_ctor_get(v_a_3943_, 3);
                    lean_inc(v_all_3944_);
                    lean_dec(v_a_3943_);
                    v___x_3945_ = lean_unsigned_to_nat(0);
                    v___x_3946_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0;
                    v___x_3947_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_all_3944_, v___x_3946_, v_a_3939_, v_a_3940_);
                    lean_dec(v_all_3944_);
                    if lean_obj_tag(v___x_3947_) == 0 {
                        v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
                        lean_inc(v_a_3948_);
                        lean_dec_ref_known(v___x_3947_, 1);
                        v___x_3949_ = lean_array_get_size(v_a_3948_);
                        v___x_3950_ = lean_nat_dec_lt(v___x_3945_, v___x_3949_);
                        if v___x_3950_ == 0 {
                            lean_dec(v_a_3948_);
                            lean_dec(v_typeName_3937_);
                            lean_inc(v_a_3940_);
                            lean_inc_ref(v_a_3939_);
                            v___x_3951_ =
                                lean_apply_3(v_cont_3938_, v_a_3939_, v_a_3940_, lean_box(0));
                            return v___x_3951_;
                        } else {
                            if v___x_3950_ == 0 {
                                lean_dec(v_a_3948_);
                                lean_dec(v_typeName_3937_);
                                lean_inc(v_a_3940_);
                                lean_inc_ref(v_a_3939_);
                                v___x_3952_ =
                                    lean_apply_3(v_cont_3938_, v_a_3939_, v_a_3940_, lean_box(0));
                                return v___x_3952_;
                            } else {
                                v___x_3953_ = 0usize;
                                v___x_3954_ = lean_usize_of_nat(v___x_3949_);
                                v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_a_3948_, v___x_3953_, v___x_3954_);
                                lean_dec(v_a_3948_);
                                if v___x_3955_ == 0 {
                                    lean_dec(v_typeName_3937_);
                                    lean_inc(v_a_3940_);
                                    lean_inc_ref(v_a_3939_);
                                    v___x_3956_ = lean_apply_3(
                                        v_cont_3938_,
                                        v_a_3939_,
                                        v_a_3940_,
                                        lean_box(0),
                                    );
                                    return v___x_3956_;
                                } else {
                                    v___x_3957_ = lean_box((v___x_3955_) as usize);
                                    v___f_3958_ = lean_alloc_closure(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                                    lean_closure_set(v___f_3958_, 0, v___x_3957_);
                                    v___x_3959_ = l_Lean_isPrivateName(v_typeName_3937_);
                                    if v___x_3959_ == 0 {
                                        v___x_3960_ =
                                            l_Lean_Elab_Command_getScope___redArg(v_a_3940_);
                                        if lean_obj_tag(v___x_3960_) == 0 {
                                            v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
                                            lean_inc(v_a_3961_);
                                            lean_dec_ref_known(v___x_3960_, 1);
                                            v_attrs_3962_ = lean_ctor_get(v_a_3961_, 9);
                                            lean_inc(v_attrs_3962_);
                                            lean_dec(v_a_3961_);
                                            v___x_3963_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___x_3955_, v_attrs_3962_);
                                            if v___x_3963_ == 0 {
                                                lean_dec(v_typeName_3937_);
                                                v___x_3964_ =
                                                    l_Lean_Elab_Command_withScope___redArg(
                                                        v___f_3958_,
                                                        v_cont_3938_,
                                                        v_a_3939_,
                                                        v_a_3940_,
                                                    );
                                                return v___x_3964_;
                                            } else {
                                                lean_dec_ref(v___f_3958_);
                                                lean_dec_ref(v_cont_3938_);
                                                v___x_3965_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once), _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2);
                                                v___x_3966_ = l_Lean_MessageData_ofConstName(
                                                    v_typeName_3937_,
                                                    v___x_3959_,
                                                );
                                                v___x_3967_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                lean_ctor_set(v___x_3967_, 0, v___x_3965_);
                                                lean_ctor_set(v___x_3967_, 1, v___x_3966_);
                                                v___x_3968_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once), _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4);
                                                v___x_3969_ = lean_alloc_ctor(7, 2, (0) as u32);
                                                lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                                                lean_ctor_set(v___x_3969_, 1, v___x_3968_);
                                                v___x_3970_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_3969_, v_a_3939_, v_a_3940_);
                                                v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
                                                v_isSharedCheck_3978_ =
                                                    (!lean_is_exclusive(v___x_3970_)) as u8;
                                                if v_isSharedCheck_3978_ == 0 {
                                                    v___x_3973_ = v___x_3970_;
                                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3971_);
                                                    lean_dec(v___x_3970_);
                                                    v___x_3973_ = lean_box(0);
                                                    v_isShared_3974_ = v_isSharedCheck_3978_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___f_3958_);
                                            lean_dec_ref(v_cont_3938_);
                                            lean_dec(v_typeName_3937_);
                                            v_a_3979_ = lean_ctor_get(v___x_3960_, 0);
                                            v_isSharedCheck_3986_ =
                                                (!lean_is_exclusive(v___x_3960_)) as u8;
                                            if v_isSharedCheck_3986_ == 0 {
                                                v___x_3981_ = v___x_3960_;
                                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3979_);
                                                lean_dec(v___x_3960_);
                                                v___x_3981_ = lean_box(0);
                                                v_isShared_3982_ = v_isSharedCheck_3986_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_typeName_3937_);
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
                        lean_dec_ref(v_cont_3938_);
                        lean_dec(v_typeName_3937_);
                        v_a_3988_ = lean_ctor_get(v___x_3947_, 0);
                        v_isSharedCheck_3995_ = (!lean_is_exclusive(v___x_3947_)) as u8;
                        if v_isSharedCheck_3995_ == 0 {
                            v___x_3990_ = v___x_3947_;
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3988_);
                            lean_dec(v___x_3947_);
                            v___x_3990_ = lean_box(0);
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_cont_3938_);
                    lean_dec(v_typeName_3937_);
                    v_a_3996_ = lean_ctor_get(v___x_3942_, 0);
                    v_isSharedCheck_4003_ = (!lean_is_exclusive(v___x_3942_)) as u8;
                    if v_isSharedCheck_4003_ == 0 {
                        v___x_3998_ = v___x_3942_;
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3996_);
                        lean_dec(v___x_3942_);
                        v___x_3998_ = lean_box(0);
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
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
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
                    v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
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
                    v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
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
                    v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
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
    mut v_typeName_4004_: *mut LeanObject,
    mut v_cont_4005_: *mut LeanObject,
    mut v_a_4006_: *mut LeanObject,
    mut v_a_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_typeName_4004_,
        v_cont_4005_,
        v_a_4006_,
        v_a_4007_,
    );
    lean_dec(v_a_4007_);
    lean_dec_ref(v_a_4006_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors(
    mut v_00_u03b1_4010_: *mut LeanObject,
    mut v_typeName_4011_: *mut LeanObject,
    mut v_cont_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    v___x_4016_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_typeName_4011_,
        v_cont_4012_,
        v_a_4013_,
        v_a_4014_,
    );
    return v___x_4016_;
}
pub unsafe fn l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(
    mut v_00_u03b1_4017_: *mut LeanObject,
    mut v_typeName_4018_: *mut LeanObject,
    mut v_cont_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4023_: *mut LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(
        v_00_u03b1_4017_,
        v_typeName_4018_,
        v_cont_4019_,
        v_a_4020_,
        v_a_4021_,
    );
    lean_dec(v_a_4021_);
    lean_dec_ref(v_a_4020_);
    return v_res_4023_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(
    mut v_as_4024_: *mut LeanObject,
    mut v_as_x27_4025_: *mut LeanObject,
    mut v_b_4026_: *mut LeanObject,
    mut v_a_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_4032_: *mut LeanObject,
    mut v_as_x27_4033_: *mut LeanObject,
    mut v_b_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
    mut v___y_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4039_: *mut LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(
        v_as_4032_,
        v_as_x27_4033_,
        v_b_4034_,
        v_a_4035_,
        v___y_4036_,
        v___y_4037_,
    );
    lean_dec(v___y_4037_);
    lean_dec_ref(v___y_4036_);
    lean_dec(v_as_x27_4033_);
    lean_dec(v_as_4032_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(
    mut v_msgData_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___x_4044_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_4040_, v___y_4042_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(
    mut v_msgData_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4049_: *mut LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_4045_, v___y_4046_, v___y_4047_);
    lean_dec(v___y_4047_);
    lean_dec_ref(v___y_4046_);
    return v_res_4049_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(
    mut v_00_u03b1_4050_: *mut LeanObject,
    mut v_msg_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___x_4055_ =
        l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(
            v_msg_4051_,
            v___y_4052_,
            v___y_4053_,
        );
    return v___x_4055_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(
    mut v_00_u03b1_4056_: *mut LeanObject,
    mut v_msg_4057_: *mut LeanObject,
    mut v___y_4058_: *mut LeanObject,
    mut v___y_4059_: *mut LeanObject,
    mut v___y_4060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4061_: *mut LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(
        v_00_u03b1_4056_,
        v_msg_4057_,
        v___y_4058_,
        v___y_4059_,
    );
    lean_dec(v___y_4059_);
    lean_dec_ref(v___y_4058_);
    return v_res_4061_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(
    mut v_msgData_4062_: *mut LeanObject,
    mut v_macroStack_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_4062_, v_macroStack_4063_, v___y_4065_);
    return v___x_4067_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(
    mut v_msgData_4068_: *mut LeanObject,
    mut v_macroStack_4069_: *mut LeanObject,
    mut v___y_4070_: *mut LeanObject,
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4073_: *mut LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_4068_, v_macroStack_4069_, v___y_4070_, v___y_4071_);
    lean_dec(v___y_4071_);
    lean_dec_ref(v___y_4070_);
    return v_res_4073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(
    mut v_sz_4074_: usize,
    mut v_i_4075_: usize,
    mut v_bs_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4077_: u8 = 0;
    let mut v_v_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4077_ = lean_usize_dec_lt(v_i_4075_, v_sz_4074_);
                if v___x_4077_ == 0 {
                    return v_bs_4076_;
                } else {
                    v_v_4078_ = lean_array_uget(v_bs_4076_, v_i_4075_);
                    v___x_4079_ = lean_unsigned_to_nat(0);
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
    mut v_sz_4085_: *mut LeanObject,
    mut v_i_4086_: *mut LeanObject,
    mut v_bs_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4088_: usize = 0;
    let mut v_i_boxed_4089_: usize = 0;
    let mut v_res_4090_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4088_ = lean_unbox_usize(v_sz_4085_);
    lean_dec(v_sz_4085_);
    v_i_boxed_4089_ = lean_unbox_usize(v_i_4086_);
    lean_dec(v_i_4086_);
    v_res_4090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_4088_, v_i_boxed_4089_, v_bs_4087_);
    return v_res_4090_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(
    mut v_msgData_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    v___x_4097_ = lean_st_ref_get(v___y_4095_);
    v_env_4098_ = lean_ctor_get(v___x_4097_, 0);
    lean_inc_ref(v_env_4098_);
    lean_dec(v___x_4097_);
    v___x_4099_ = lean_st_ref_get(v___y_4093_);
    v_mctx_4100_ = lean_ctor_get(v___x_4099_, 0);
    lean_inc_ref(v_mctx_4100_);
    lean_dec(v___x_4099_);
    v_lctx_4101_ = lean_ctor_get(v___y_4092_, 2);
    v_options_4102_ = lean_ctor_get(v___y_4094_, 2);
    lean_inc_ref(v_options_4102_);
    lean_inc_ref(v_lctx_4101_);
    v___x_4103_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4103_, 0, v_env_4098_);
    lean_ctor_set(v___x_4103_, 1, v_mctx_4100_);
    lean_ctor_set(v___x_4103_, 2, v_lctx_4101_);
    lean_ctor_set(v___x_4103_, 3, v_options_4102_);
    v___x_4104_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4104_, 0, v___x_4103_);
    lean_ctor_set(v___x_4104_, 1, v_msgData_4091_);
    v___x_4105_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4105_, 0, v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4112_: *mut LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    lean_dec(v___y_4110_);
    lean_dec_ref(v___y_4109_);
    lean_dec(v___y_4108_);
    lean_dec_ref(v___y_4107_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_4113_: *mut LeanObject,
    mut v_macroStack_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v_unused_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4117_ = lean_ctor_get(v___y_4115_, 2);
                v___x_4118_ = l_Lean_Elab_pp_macroStack;
                v___x_4119_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_options_4117_, v___x_4118_);
                if v___x_4119_ == 0 {
                    lean_dec(v_macroStack_4114_);
                    v___x_4120_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4120_, 0, v_msgData_4113_);
                    return v___x_4120_;
                } else {
                    if lean_obj_tag(v_macroStack_4114_) == 0 {
                        v___x_4121_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4121_, 0, v_msgData_4113_);
                        return v___x_4121_;
                    } else {
                        v_head_4122_ = lean_ctor_get(v_macroStack_4114_, 0);
                        lean_inc(v_head_4122_);
                        v_after_4123_ = lean_ctor_get(v_head_4122_, 1);
                        v_isSharedCheck_4138_ = (!lean_is_exclusive(v_head_4122_)) as u8;
                        if v_isSharedCheck_4138_ == 0 {
                            v_unused_4139_ = lean_ctor_get(v_head_4122_, 0);
                            lean_dec(v_unused_4139_);
                            v___x_4125_ = v_head_4122_;
                            v_isShared_4126_ = v_isSharedCheck_4138_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_4123_);
                            lean_dec(v_head_4122_);
                            v___x_4125_ = lean_box(0);
                            v_isShared_4126_ = v_isSharedCheck_4138_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4127_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_4126_ == 0 {
                    lean_ctor_set_tag(v___x_4125_, 7);
                    lean_ctor_set(v___x_4125_, 1, v___x_4127_);
                    lean_ctor_set(v___x_4125_, 0, v_msgData_4113_);
                    v___x_4129_ = v___x_4125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_msgData_4113_);
                    lean_ctor_set(v_reuseFailAlloc_4137_, 1, v___x_4127_);
                    v___x_4129_ = v_reuseFailAlloc_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4130_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
                v___x_4131_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4131_, 0, v___x_4129_);
                lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                v___x_4132_ = l_Lean_MessageData_ofSyntax(v_after_4123_);
                v___x_4133_ = l_Lean_indentD(v___x_4132_);
                v_msgData_4134_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_4134_, 0, v___x_4131_);
                lean_ctor_set(v_msgData_4134_, 1, v___x_4133_);
                v___x_4135_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_4134_, v_macroStack_4114_);
                v___x_4136_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                return v___x_4136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_4140_: *mut LeanObject,
    mut v_macroStack_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v_res_4144_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_4140_, v_macroStack_4141_, v___y_4142_);
    lean_dec_ref(v___y_4142_);
    return v_res_4144_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(
    mut v_msg_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4153_ = lean_ctor_get(v___y_4150_, 5);
                v___x_4154_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_4145_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
                v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
                lean_inc(v_a_4155_);
                lean_dec_ref(v___x_4154_);
                v_macroStack_4156_ = lean_ctor_get(v___y_4146_, 1);
                v___x_4157_ = l_Lean_Elab_getBetterRef(v_ref_4153_, v_macroStack_4156_);
                lean_inc(v_macroStack_4156_);
                v___x_4158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_4155_, v_macroStack_4156_, v___y_4150_);
                v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
                v_isSharedCheck_4167_ = (!lean_is_exclusive(v___x_4158_)) as u8;
                if v_isSharedCheck_4167_ == 0 {
                    v___x_4161_ = v___x_4158_;
                    v_isShared_4162_ = v_isSharedCheck_4167_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4159_);
                    lean_dec(v___x_4158_);
                    v___x_4161_ = lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4163_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4163_, 0, v___x_4157_);
                lean_ctor_set(v___x_4163_, 1, v_a_4159_);
                if v_isShared_4162_ == 0 {
                    lean_ctor_set_tag(v___x_4161_, 1);
                    lean_ctor_set(v___x_4161_, 0, v___x_4163_);
                    v___x_4165_ = v___x_4161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
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
    mut v_msg_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
    mut v___y_4175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4176_: *mut LeanObject = core::ptr::null_mut();
    v_res_4176_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    lean_dec(v___y_4174_);
    lean_dec_ref(v___y_4173_);
    lean_dec(v___y_4172_);
    lean_dec_ref(v___y_4171_);
    lean_dec(v___y_4170_);
    lean_dec_ref(v___y_4169_);
    return v_res_4176_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
    mut v_constName_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4185_ = lean_st_ref_get(v___y_4183_);
                v_env_4186_ = lean_ctor_get(v___x_4185_, 0);
                lean_inc_ref(v_env_4186_);
                lean_dec(v___x_4185_);
                lean_inc(v_constName_4177_);
                v___x_4187_ = l_Lean_isInductiveCore_x3f(v_env_4186_, v_constName_4177_);
                if lean_obj_tag(v___x_4187_) == 0 {
                    v___x_4188_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
                    v___x_4189_ = 0;
                    v___x_4190_ = l_Lean_MessageData_ofConstName(v_constName_4177_, v___x_4189_);
                    v___x_4191_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4191_, 0, v___x_4188_);
                    lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                    v___x_4192_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
                    v___x_4193_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4193_, 0, v___x_4191_);
                    lean_ctor_set(v___x_4193_, 1, v___x_4192_);
                    v___x_4194_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_4193_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
                    return v___x_4194_;
                } else {
                    lean_dec(v_constName_4177_);
                    v_val_4195_ = lean_ctor_get(v___x_4187_, 0);
                    v_isSharedCheck_4202_ = (!lean_is_exclusive(v___x_4187_)) as u8;
                    if v_isSharedCheck_4202_ == 0 {
                        v___x_4197_ = v___x_4187_;
                        v_isShared_4198_ = v_isSharedCheck_4202_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4195_);
                        lean_dec(v___x_4187_);
                        v___x_4197_ = lean_box(0);
                        v_isShared_4198_ = v_isSharedCheck_4202_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4198_ == 0 {
                    lean_ctor_set_tag(v___x_4197_, 0);
                    v___x_4200_ = v___x_4197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4195_);
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
    mut v_constName_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
    mut v___y_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4211_: *mut LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(
        v_constName_4203_,
        v___y_4204_,
        v___y_4205_,
        v___y_4206_,
        v___y_4207_,
        v___y_4208_,
        v___y_4209_,
    );
    lean_dec(v___y_4209_);
    lean_dec_ref(v___y_4208_);
    lean_dec(v___y_4207_);
    lean_dec_ref(v___y_4206_);
    lean_dec(v___y_4205_);
    lean_dec_ref(v___y_4204_);
    return v_res_4211_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstName(
    mut v_className_4213_: *mut LeanObject,
    mut v_indName_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4239_: usize = 0;
    let mut v___x_4240_: usize = 0;
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4250_: u8 = 0;
    let mut v_a_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4222_) == 0 {
                    v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
                    lean_inc_n(v_a_4223_, 2);
                    lean_dec_ref_known(v___x_4222_, 1);
                    v___x_4224_ = l_Lean_Elab_Deriving_mkInductArgNames(
                        v_a_4223_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_,
                    );
                    if lean_obj_tag(v___x_4224_) == 0 {
                        v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
                        lean_inc_n(v_a_4225_, 2);
                        lean_dec_ref_known(v___x_4224_, 1);
                        v___x_4226_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                            v_a_4225_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_,
                            v_a_4220_,
                        );
                        if lean_obj_tag(v___x_4226_) == 0 {
                            v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
                            lean_inc(v_a_4227_);
                            lean_dec_ref_known(v___x_4226_, 1);
                            v___x_4228_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                v_a_4223_, v_a_4225_, v_a_4219_,
                            );
                            v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
                            lean_inc(v_a_4229_);
                            lean_dec_ref(v___x_4228_);
                            v_ref_4230_ = lean_ctor_get(v_a_4219_, 5);
                            v___x_4231_ = 0;
                            v___x_4232_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4231_);
                            v___x_4233_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                            v___x_4234_ = l_Lean_mkCIdent(v_className_4213_);
                            v___x_4235_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                            lean_inc(v___x_4232_);
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
                            lean_dec(v_a_4225_);
                            lean_dec(v_a_4223_);
                            lean_dec(v_className_4213_);
                            v_a_4243_ = lean_ctor_get(v___x_4226_, 0);
                            v_isSharedCheck_4250_ = (!lean_is_exclusive(v___x_4226_)) as u8;
                            if v_isSharedCheck_4250_ == 0 {
                                v___x_4245_ = v___x_4226_;
                                v_isShared_4246_ = v_isSharedCheck_4250_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4243_);
                                lean_dec(v___x_4226_);
                                v___x_4245_ = lean_box(0);
                                v_isShared_4246_ = v_isSharedCheck_4250_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4223_);
                        lean_dec(v_className_4213_);
                        v_a_4251_ = lean_ctor_get(v___x_4224_, 0);
                        v_isSharedCheck_4258_ = (!lean_is_exclusive(v___x_4224_)) as u8;
                        if v_isSharedCheck_4258_ == 0 {
                            v___x_4253_ = v___x_4224_;
                            v_isShared_4254_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4251_);
                            lean_dec(v___x_4224_);
                            v___x_4253_ = lean_box(0);
                            v_isShared_4254_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_className_4213_);
                    v_a_4259_ = lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4266_ = (!lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4222_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4259_);
                        lean_dec(v___x_4222_);
                        v___x_4261_ = lean_box(0);
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
                    v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
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
                    v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
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
                    v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
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
    mut v_className_4267_: *mut LeanObject,
    mut v_indName_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
    mut v_a_4274_: *mut LeanObject,
    mut v_a_4275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4276_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4274_);
    lean_dec_ref(v_a_4273_);
    lean_dec(v_a_4272_);
    lean_dec_ref(v_a_4271_);
    lean_dec(v_a_4270_);
    lean_dec_ref(v_a_4269_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(
    mut v_00_u03b1_4277_: *mut LeanObject,
    mut v_msg_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
    mut v___y_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
    return v___x_4286_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(
    mut v_00_u03b1_4287_: *mut LeanObject,
    mut v_msg_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4296_: *mut LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_4287_, v_msg_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
    lean_dec(v___y_4294_);
    lean_dec_ref(v___y_4293_);
    lean_dec(v___y_4292_);
    lean_dec_ref(v___y_4291_);
    lean_dec(v___y_4290_);
    lean_dec_ref(v___y_4289_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(
    mut v_msgData_4297_: *mut LeanObject,
    mut v_macroStack_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    v___x_4306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_4297_, v_macroStack_4298_, v___y_4303_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_4307_: *mut LeanObject,
    mut v_macroStack_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
    mut v___y_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4316_: *mut LeanObject = core::ptr::null_mut();
    v_res_4316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_4307_, v_macroStack_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
    lean_dec(v___y_4314_);
    lean_dec_ref(v___y_4313_);
    lean_dec(v___y_4312_);
    lean_dec_ref(v___y_4311_);
    lean_dec(v___y_4310_);
    lean_dec_ref(v___y_4309_);
    return v_res_4316_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(
    mut v_as_x27_4317_: *mut LeanObject,
    mut v_b_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4317_) == 0 {
                    v___x_4326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4326_, 0, v_b_4318_);
                    return v___x_4326_;
                } else {
                    v_head_4327_ = lean_ctor_get(v_as_x27_4317_, 0);
                    v_tail_4328_ = lean_ctor_get(v_as_x27_4317_, 1);
                    lean_inc(v_head_4327_);
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
                    if lean_obj_tag(v___x_4329_) == 0 {
                        v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
                        lean_inc(v_a_4330_);
                        lean_dec_ref_known(v___x_4329_, 1);
                        v___x_4331_ = lean_array_push(v_b_4318_, v_a_4330_);
                        v_as_x27_4317_ = v_tail_4328_;
                        v_b_4318_ = v___x_4331_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_4318_);
                        v_a_4333_ = lean_ctor_get(v___x_4329_, 0);
                        v_isSharedCheck_4340_ = (!lean_is_exclusive(v___x_4329_)) as u8;
                        if v_isSharedCheck_4340_ == 0 {
                            v___x_4335_ = v___x_4329_;
                            v_isShared_4336_ = v_isSharedCheck_4340_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4333_);
                            lean_dec(v___x_4329_);
                            v___x_4335_ = lean_box(0);
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
                    v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
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
    mut v_as_x27_4341_: *mut LeanObject,
    mut v_b_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4350_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4348_);
    lean_dec_ref(v___y_4347_);
    lean_dec(v___y_4346_);
    lean_dec_ref(v___y_4345_);
    lean_dec(v___y_4344_);
    lean_dec_ref(v___y_4343_);
    lean_dec(v_as_x27_4341_);
    return v_res_4350_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(
    mut v_a_4351_: *mut LeanObject,
    mut v_a_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4351_) == 0 {
                    v___x_4353_ = l_List_reverse___redArg(v_a_4352_);
                    return v___x_4353_;
                } else {
                    v_head_4354_ = lean_ctor_get(v_a_4351_, 0);
                    v_tail_4355_ = lean_ctor_get(v_a_4351_, 1);
                    v_isSharedCheck_4364_ = (!lean_is_exclusive(v_a_4351_)) as u8;
                    if v_isSharedCheck_4364_ == 0 {
                        v___x_4357_ = v_a_4351_;
                        v_isShared_4358_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4355_);
                        lean_inc(v_head_4354_);
                        lean_dec(v_a_4351_);
                        v___x_4357_ = lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4364_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4359_ = l_Lean_MessageData_ofName(v_head_4354_);
                if v_isShared_4358_ == 0 {
                    lean_ctor_set(v___x_4357_, 1, v_a_4352_);
                    lean_ctor_set(v___x_4357_, 0, v___x_4359_);
                    v___x_4361_ = v___x_4357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4359_);
                    lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_a_4352_);
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
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: f64 = 0.0;
    v___x_4365_ = lean_unsigned_to_nat(0);
    v___x_4366_ = lean_float_of_nat(v___x_4365_);
    return v___x_4366_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
    mut v_cls_4370_: *mut LeanObject,
    mut v_msg_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4395_: u8 = 0;
    let mut v_tid_4396_: u64 = 0;
    let mut v_traces_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: f64 = 0.0;
    let mut v___x_4403_: u8 = 0;
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4377_ = lean_ctor_get(v___y_4374_, 5);
                v___x_4378_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
                v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
                v_isSharedCheck_4423_ = (!lean_is_exclusive(v___x_4378_)) as u8;
                if v_isSharedCheck_4423_ == 0 {
                    v___x_4381_ = v___x_4378_;
                    v_isShared_4382_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4379_);
                    lean_dec(v___x_4378_);
                    v___x_4381_ = lean_box(0);
                    v_isShared_4382_ = v_isSharedCheck_4423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4383_ = lean_st_ref_take(v___y_4375_);
                v_traceState_4384_ = lean_ctor_get(v___x_4383_, 4);
                v_env_4385_ = lean_ctor_get(v___x_4383_, 0);
                v_nextMacroScope_4386_ = lean_ctor_get(v___x_4383_, 1);
                v_ngen_4387_ = lean_ctor_get(v___x_4383_, 2);
                v_auxDeclNGen_4388_ = lean_ctor_get(v___x_4383_, 3);
                v_cache_4389_ = lean_ctor_get(v___x_4383_, 5);
                v_messages_4390_ = lean_ctor_get(v___x_4383_, 6);
                v_infoState_4391_ = lean_ctor_get(v___x_4383_, 7);
                v_snapshotTasks_4392_ = lean_ctor_get(v___x_4383_, 8);
                v_isSharedCheck_4422_ = (!lean_is_exclusive(v___x_4383_)) as u8;
                if v_isSharedCheck_4422_ == 0 {
                    v___x_4394_ = v___x_4383_;
                    v_isShared_4395_ = v_isSharedCheck_4422_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4392_);
                    lean_inc(v_infoState_4391_);
                    lean_inc(v_messages_4390_);
                    lean_inc(v_cache_4389_);
                    lean_inc(v_traceState_4384_);
                    lean_inc(v_auxDeclNGen_4388_);
                    lean_inc(v_ngen_4387_);
                    lean_inc(v_nextMacroScope_4386_);
                    lean_inc(v_env_4385_);
                    lean_dec(v___x_4383_);
                    v___x_4394_ = lean_box(0);
                    v_isShared_4395_ = v_isSharedCheck_4422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4396_ = lean_ctor_get_uint64(
                    v_traceState_4384_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4397_ = lean_ctor_get(v_traceState_4384_, 0);
                v_isSharedCheck_4421_ = (!lean_is_exclusive(v_traceState_4384_)) as u8;
                if v_isSharedCheck_4421_ == 0 {
                    v___x_4399_ = v_traceState_4384_;
                    v_isShared_4400_ = v_isSharedCheck_4421_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4397_);
                    lean_dec(v_traceState_4384_);
                    v___x_4399_ = lean_box(0);
                    v_isShared_4400_ = v_isSharedCheck_4421_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4401_ = lean_box(0);
                v___x_4402_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
                v___x_4403_ = 0;
                v___x_4404_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1;
                v___x_4405_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4405_, 0, v_cls_4370_);
                lean_ctor_set(v___x_4405_, 1, v___x_4401_);
                lean_ctor_set(v___x_4405_, 2, v___x_4404_);
                lean_ctor_set_float(
                    v___x_4405_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4402_,
                );
                lean_ctor_set_float(
                    v___x_4405_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4402_,
                );
                lean_ctor_set_uint8(
                    v___x_4405_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4403_,
                );
                v___x_4406_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2;
                v___x_4407_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4407_, 0, v___x_4405_);
                lean_ctor_set(v___x_4407_, 1, v_a_4379_);
                lean_ctor_set(v___x_4407_, 2, v___x_4406_);
                lean_inc(v_ref_4377_);
                v___x_4408_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4408_, 0, v_ref_4377_);
                lean_ctor_set(v___x_4408_, 1, v___x_4407_);
                v___x_4409_ = l_Lean_PersistentArray_push___redArg(v_traces_4397_, v___x_4408_);
                if v_isShared_4400_ == 0 {
                    lean_ctor_set(v___x_4399_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4399_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4409_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4420_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4396_,
                    );
                    v___x_4411_ = v_reuseFailAlloc_4420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4395_ == 0 {
                    lean_ctor_set(v___x_4394_, 4, v___x_4411_);
                    v___x_4413_ = v___x_4394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_env_4385_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_nextMacroScope_4386_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_ngen_4387_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_auxDeclNGen_4388_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 4, v___x_4411_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 5, v_cache_4389_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 6, v_messages_4390_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 7, v_infoState_4391_);
                    lean_ctor_set(v_reuseFailAlloc_4419_, 8, v_snapshotTasks_4392_);
                    v___x_4413_ = v_reuseFailAlloc_4419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4414_ = lean_st_ref_set(v___y_4375_, v___x_4413_);
                v___x_4415_ = lean_box(0);
                if v_isShared_4382_ == 0 {
                    lean_ctor_set(v___x_4381_, 0, v___x_4415_);
                    v___x_4417_ = v___x_4381_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
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
    mut v_cls_4424_: *mut LeanObject,
    mut v_msg_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4431_: *mut LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
        v_cls_4424_,
        v_msg_4425_,
        v___y_4426_,
        v___y_4427_,
        v___y_4428_,
        v___y_4429_,
    );
    lean_dec(v___y_4429_);
    lean_dec_ref(v___y_4428_);
    lean_dec(v___y_4427_);
    lean_dec_ref(v___y_4426_);
    return v_res_4431_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(
    mut v_fnPrefix_4433_: *mut LeanObject,
    mut v_a_4434_: *mut LeanObject,
    mut v_range_4435_: *mut LeanObject,
    mut v_b_4436_: *mut LeanObject,
    mut v_i_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_4439_ = lean_ctor_get(v_range_4435_, 1);
                v_step_4440_ = lean_ctor_get(v_range_4435_, 2);
                v___x_4441_ = lean_nat_dec_lt(v_i_4437_, v_stop_4439_);
                if v___x_4441_ == 0 {
                    lean_dec(v_i_4437_);
                    lean_dec(v_a_4434_);
                    lean_dec_ref(v_fnPrefix_4433_);
                    v___x_4442_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4442_, 0, v_b_4436_);
                    return v___x_4442_;
                } else {
                    v___x_4443_ = lean_unsigned_to_nat(1);
                    v___x_4444_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0;
                    lean_inc_ref(v_fnPrefix_4433_);
                    v___x_4445_ = lean_string_append(v_fnPrefix_4433_, v___x_4444_);
                    v___x_4446_ = lean_nat_add(v_i_4437_, v___x_4443_);
                    v___x_4447_ = l_Nat_reprFast(v___x_4446_);
                    v___x_4448_ = lean_string_append(v___x_4445_, v___x_4447_);
                    lean_dec_ref(v___x_4447_);
                    v___x_4449_ = lean_box(0);
                    v___x_4450_ = l_Lean_Name_str___override(v___x_4449_, v___x_4448_);
                    lean_inc(v_a_4434_);
                    v___x_4451_ = l_Lean_Name_append(v_a_4434_, v___x_4450_);
                    v___x_4452_ = lean_array_push(v_b_4436_, v___x_4451_);
                    v___x_4453_ = lean_nat_add(v_i_4437_, v_step_4440_);
                    lean_dec(v_i_4437_);
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
    mut v_fnPrefix_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_range_4457_: *mut LeanObject,
    mut v_b_4458_: *mut LeanObject,
    mut v_i_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4461_: *mut LeanObject = core::ptr::null_mut();
    v_res_4461_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4455_, v_a_4456_, v_range_4457_, v_b_4458_, v_i_4459_);
    lean_dec_ref(v_range_4457_);
    return v_res_4461_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__5() -> *mut LeanObject {
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    v___x_4470_ = l_Lean_Elab_Deriving_mkContext___closed__2;
    v___x_4471_ = l_Lean_Elab_Deriving_mkContext___closed__4;
    v___x_4472_ = l_Lean_Name_append(v___x_4471_, v___x_4470_);
    return v___x_4472_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__7() -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_Elab_Deriving_mkContext___closed__6;
    v___x_4475_ = l_Lean_stringToMessageData(v___x_4474_);
    return v___x_4475_;
}
pub unsafe fn _init_l_Lean_Elab_Deriving_mkContext___closed__9() -> *mut LeanObject {
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Lean_Elab_Deriving_mkContext___closed__8;
    v___x_4478_ = l_Lean_stringToMessageData(v___x_4477_);
    return v___x_4478_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkContext(
    mut v_className_4479_: *mut LeanObject,
    mut v_fnPrefix_4480_: *mut LeanObject,
    mut v_typeName_4481_: *mut LeanObject,
    mut v_supportsRec_4482_: u8,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
    mut v_a_4487_: *mut LeanObject,
    mut v_a_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRec_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___y_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4505_: u8 = 0;
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4512_: u8 = 0;
    let mut v___y_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    let mut v_auxFunNames_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4528_: u8 = 0;
    let mut v_inheritedTraceOptions_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut v_a_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut v_a_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_typeName_4481_);
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
                if lean_obj_tag(v___x_4490_) == 0 {
                    v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
                    lean_inc(v_a_4491_);
                    lean_dec_ref_known(v___x_4490_, 1);
                    v_all_4492_ = lean_ctor_get(v_a_4491_, 3);
                    v_isRec_4493_ = lean_ctor_get_uint8(
                        v_a_4491_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    );
                    v___x_4494_ = lean_unsigned_to_nat(0);
                    v___x_4495_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0;
                    v___x_4496_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_4492_, v___x_4495_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
                    if lean_obj_tag(v___x_4496_) == 0 {
                        v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
                        lean_inc(v_a_4497_);
                        lean_dec_ref_known(v___x_4496_, 1);
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
                        if lean_obj_tag(v___x_4498_) == 0 {
                            v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
                            v_isSharedCheck_4562_ = (!lean_is_exclusive(v___x_4498_)) as u8;
                            if v_isSharedCheck_4562_ == 0 {
                                v___x_4501_ = v___x_4498_;
                                v_isShared_4502_ = v_isSharedCheck_4562_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4499_);
                                lean_dec(v___x_4498_);
                                v___x_4501_ = lean_box(0);
                                v_isShared_4502_ = v_isSharedCheck_4562_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4497_);
                            lean_dec(v_a_4491_);
                            lean_dec_ref(v_fnPrefix_4480_);
                            v_a_4563_ = lean_ctor_get(v___x_4498_, 0);
                            v_isSharedCheck_4570_ = (!lean_is_exclusive(v___x_4498_)) as u8;
                            if v_isSharedCheck_4570_ == 0 {
                                v___x_4565_ = v___x_4498_;
                                v_isShared_4566_ = v_isSharedCheck_4570_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4563_);
                                lean_dec(v___x_4498_);
                                v___x_4565_ = lean_box(0);
                                v_isShared_4566_ = v_isSharedCheck_4570_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4491_);
                        lean_dec(v_typeName_4481_);
                        lean_dec_ref(v_fnPrefix_4480_);
                        lean_dec(v_className_4479_);
                        v_a_4571_ = lean_ctor_get(v___x_4496_, 0);
                        v_isSharedCheck_4578_ = (!lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4578_ == 0 {
                            v___x_4573_ = v___x_4496_;
                            v_isShared_4574_ = v_isSharedCheck_4578_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4571_);
                            lean_dec(v___x_4496_);
                            v___x_4573_ = lean_box(0);
                            v_isShared_4574_ = v_isSharedCheck_4578_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_typeName_4481_);
                    lean_dec_ref(v_fnPrefix_4480_);
                    lean_dec(v_className_4479_);
                    v_a_4579_ = lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4586_ = (!lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4586_ == 0 {
                        v___x_4581_ = v___x_4490_;
                        v_isShared_4582_ = v_isSharedCheck_4586_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4579_);
                        lean_dec(v___x_4490_);
                        v___x_4581_ = lean_box(0);
                        v_isShared_4582_ = v_isSharedCheck_4586_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4552_ = l_List_lengthTR___redArg(v_all_4492_);
                v___x_4553_ = lean_unsigned_to_nat(1);
                v___x_4554_ = lean_nat_dec_eq(v___x_4552_, v___x_4553_);
                if v___x_4554_ == 0 {
                    v___x_4555_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_4555_, 0, v___x_4494_);
                    lean_ctor_set(v___x_4555_, 1, v___x_4552_);
                    lean_ctor_set(v___x_4555_, 2, v___x_4553_);
                    lean_inc(v_a_4499_);
                    v___x_4556_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4480_, v_a_4499_, v___x_4555_, v___x_4495_, v___x_4494_);
                    lean_dec_ref_known(v___x_4555_, 3);
                    v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
                    lean_inc(v_a_4557_);
                    lean_dec_ref(v___x_4556_);
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
                    lean_dec(v___x_4552_);
                    v___x_4558_ = lean_box(0);
                    v___x_4559_ = l_Lean_Name_str___override(v___x_4558_, v_fnPrefix_4480_);
                    lean_inc(v_a_4499_);
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
                v___x_4506_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_4506_, 0, v_a_4499_);
                lean_ctor_set(v___x_4506_, 1, v_a_4497_);
                lean_ctor_set(v___x_4506_, 2, v___y_4504_);
                lean_ctor_set_uint8(
                    v___x_4506_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_4505_,
                );
                if v_isShared_4502_ == 0 {
                    lean_ctor_set(v___x_4501_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
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
                lean_dec(v_a_4491_);
                if v___x_4515_ == 0 {
                    v___x_4516_ = lean_unsigned_to_nat(1);
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
                v_options_4527_ = lean_ctor_get(v___y_4525_, 2);
                v_hasTrace_4528_ = lean_ctor_get_uint8(
                    v_options_4527_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4528_ == 0 {
                    v___y_4514_ = v_auxFunNames_4520_;
                    state = 5;
                    continue;
                } else {
                    v_inheritedTraceOptions_4529_ = lean_ctor_get(v___y_4525_, 13);
                    v___x_4530_ = l_Lean_Elab_Deriving_mkContext___closed__2;
                    v___x_4531_ = lean_obj_once(
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
                        v___x_4533_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Deriving_mkContext___closed__7_once
                            ),
                            _init_l_Lean_Elab_Deriving_mkContext___closed__7,
                        );
                        lean_inc(v_a_4499_);
                        v___x_4534_ = l_Lean_MessageData_ofName(v_a_4499_);
                        v___x_4535_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4535_, 0, v___x_4533_);
                        lean_ctor_set(v___x_4535_, 1, v___x_4534_);
                        v___x_4536_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkContext___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Deriving_mkContext___closed__9_once
                            ),
                            _init_l_Lean_Elab_Deriving_mkContext___closed__9,
                        );
                        v___x_4537_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4537_, 0, v___x_4535_);
                        lean_ctor_set(v___x_4537_, 1, v___x_4536_);
                        lean_inc_ref(v_auxFunNames_4520_);
                        v___x_4538_ = lean_array_to_list(v_auxFunNames_4520_);
                        v___x_4539_ = lean_box(0);
                        v___x_4540_ =
                            l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(
                                v___x_4538_,
                                v___x_4539_,
                            );
                        v___x_4541_ = l_Lean_MessageData_ofList(v___x_4540_);
                        v___x_4542_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4542_, 0, v___x_4537_);
                        lean_ctor_set(v___x_4542_, 1, v___x_4541_);
                        v___x_4543_ =
                            l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(
                                v___x_4530_,
                                v___x_4542_,
                                v___y_4523_,
                                v___y_4524_,
                                v___y_4525_,
                                v___y_4526_,
                            );
                        if lean_obj_tag(v___x_4543_) == 0 {
                            lean_dec_ref_known(v___x_4543_, 1);
                            v___y_4514_ = v_auxFunNames_4520_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec_ref(v_auxFunNames_4520_);
                            lean_del_object(v___x_4501_);
                            lean_dec(v_a_4499_);
                            lean_dec(v_a_4497_);
                            lean_dec(v_a_4491_);
                            v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
                            v_isSharedCheck_4551_ = (!lean_is_exclusive(v___x_4543_)) as u8;
                            if v_isSharedCheck_4551_ == 0 {
                                v___x_4546_ = v___x_4543_;
                                v_isShared_4547_ = v_isSharedCheck_4551_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4544_);
                                lean_dec(v___x_4543_);
                                v___x_4546_ = lean_box(0);
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
                    v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
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
                    v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
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
                    v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
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
                    v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
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
    mut v_className_4587_: *mut LeanObject,
    mut v_fnPrefix_4588_: *mut LeanObject,
    mut v_typeName_4589_: *mut LeanObject,
    mut v_supportsRec_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
    mut v_a_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
    mut v_a_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_supportsRec_boxed_4598_: u8 = 0;
    let mut v_res_4599_: *mut LeanObject = core::ptr::null_mut();
    v_supportsRec_boxed_4598_ = (lean_unbox(v_supportsRec_4590_) as u8);
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
    lean_dec(v_a_4596_);
    lean_dec_ref(v_a_4595_);
    lean_dec(v_a_4594_);
    lean_dec_ref(v_a_4593_);
    lean_dec(v_a_4592_);
    lean_dec_ref(v_a_4591_);
    return v_res_4599_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(
    mut v_as_4600_: *mut LeanObject,
    mut v_as_x27_4601_: *mut LeanObject,
    mut v_b_4602_: *mut LeanObject,
    mut v_a_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_4612_: *mut LeanObject,
    mut v_as_x27_4613_: *mut LeanObject,
    mut v_b_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4623_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4621_);
    lean_dec_ref(v___y_4620_);
    lean_dec(v___y_4619_);
    lean_dec_ref(v___y_4618_);
    lean_dec(v___y_4617_);
    lean_dec_ref(v___y_4616_);
    lean_dec(v_as_x27_4613_);
    lean_dec(v_as_4612_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(
    mut v_cls_4624_: *mut LeanObject,
    mut v_msg_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_cls_4634_: *mut LeanObject,
    mut v_msg_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4643_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4641_);
    lean_dec_ref(v___y_4640_);
    lean_dec(v___y_4639_);
    lean_dec_ref(v___y_4638_);
    lean_dec(v___y_4637_);
    lean_dec_ref(v___y_4636_);
    return v_res_4643_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(
    mut v_fnPrefix_4644_: *mut LeanObject,
    mut v_a_4645_: *mut LeanObject,
    mut v_range_4646_: *mut LeanObject,
    mut v_b_4647_: *mut LeanObject,
    mut v_i_4648_: *mut LeanObject,
    mut v_hs_4649_: *mut LeanObject,
    mut v_hl_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    v___x_4658_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_4644_, v_a_4645_, v_range_4646_, v_b_4647_, v_i_4648_);
    return v___x_4658_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(
    mut v_fnPrefix_4659_: *mut LeanObject,
    mut v_a_4660_: *mut LeanObject,
    mut v_range_4661_: *mut LeanObject,
    mut v_b_4662_: *mut LeanObject,
    mut v_i_4663_: *mut LeanObject,
    mut v_hs_4664_: *mut LeanObject,
    mut v_hl_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
    mut v___y_4668_: *mut LeanObject,
    mut v___y_4669_: *mut LeanObject,
    mut v___y_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4673_: *mut LeanObject = core::ptr::null_mut();
    v_res_4673_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_4659_, v_a_4660_, v_range_4661_, v_b_4662_, v_i_4663_, v_hs_4664_, v_hl_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
    lean_dec(v___y_4671_);
    lean_dec_ref(v___y_4670_);
    lean_dec(v___y_4669_);
    lean_dec_ref(v___y_4668_);
    lean_dec(v___y_4667_);
    lean_dec_ref(v___y_4666_);
    lean_dec_ref(v_range_4661_);
    return v_res_4673_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(
    mut v_a_4674_: *mut LeanObject,
    mut v_b_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4676_ = lean_ctor_get(v_a_4674_, 0);
                v_start_4677_ = lean_ctor_get(v_a_4674_, 1);
                v_stop_4678_ = lean_ctor_get(v_a_4674_, 2);
                v_isSharedCheck_4691_ = (!lean_is_exclusive(v_a_4674_)) as u8;
                if v_isSharedCheck_4691_ == 0 {
                    v___x_4680_ = v_a_4674_;
                    v_isShared_4681_ = v_isSharedCheck_4691_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_4678_);
                    lean_inc(v_start_4677_);
                    lean_inc(v_array_4676_);
                    lean_dec(v_a_4674_);
                    v___x_4680_ = lean_box(0);
                    v_isShared_4681_ = v_isSharedCheck_4691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4682_ = lean_nat_dec_lt(v_start_4677_, v_stop_4678_);
                if v___x_4682_ == 0 {
                    lean_del_object(v___x_4680_);
                    lean_dec(v_stop_4678_);
                    lean_dec(v_start_4677_);
                    lean_dec_ref(v_array_4676_);
                    return v_b_4675_;
                } else {
                    v___x_4683_ = lean_unsigned_to_nat(1);
                    v___x_4684_ = lean_nat_add(v_start_4677_, v___x_4683_);
                    lean_inc_ref(v_array_4676_);
                    if v_isShared_4681_ == 0 {
                        lean_ctor_set(v___x_4680_, 1, v___x_4684_);
                        v___x_4686_ = v___x_4680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_array_4676_);
                        lean_ctor_set(v_reuseFailAlloc_4690_, 1, v___x_4684_);
                        lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_stop_4678_);
                        v___x_4686_ = v_reuseFailAlloc_4690_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4687_ = lean_array_fget(v_array_4676_, v_start_4677_);
                lean_dec(v_start_4677_);
                lean_dec_ref(v_array_4676_);
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
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4699_ = lean_ctor_get(v___y_4696_, 5);
    v___x_4700_ = 0;
    v___x_4701_ = l_Lean_SourceInfo_fromRef(v_ref_4699_, v___x_4700_);
    v___x_4702_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4702_, 0, v___x_4701_);
    return v___x_4702_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4710_: *mut LeanObject = core::ptr::null_mut();
    v_res_4710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
    lean_dec(v___y_4708_);
    lean_dec_ref(v___y_4707_);
    lean_dec(v___y_4706_);
    lean_dec_ref(v___y_4705_);
    lean_dec(v___y_4704_);
    lean_dec_ref(v___y_4703_);
    return v_res_4710_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(
    mut v_upperBound_4748_: *mut LeanObject,
    mut v___x_4749_: *mut LeanObject,
    mut v_ctx_4750_: *mut LeanObject,
    mut v_argNames_4751_: *mut LeanObject,
    mut v_className_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
    mut v_b_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4762_: u8 = 0;
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: u8 = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4840_: u8 = 0;
    let mut v_a_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_a_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4864_: u8 = 0;
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u8 = 0;
    let mut v_a_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4871_: u8 = 0;
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4762_ = lean_nat_dec_lt(v_a_4753_, v_upperBound_4748_);
                if v___x_4762_ == 0 {
                    lean_dec(v_a_4753_);
                    lean_dec(v_className_4752_);
                    lean_dec_ref(v_argNames_4751_);
                    v___x_4763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4763_, 0, v_b_4754_);
                    return v___x_4763_;
                } else {
                    v___x_4764_ = lean_array_fget_borrowed(v___x_4749_, v_a_4753_);
                    lean_inc(v___x_4764_);
                    v___x_4765_ = l_Lean_Elab_Deriving_mkInductArgNames(
                        v___x_4764_,
                        v___y_4755_,
                        v___y_4756_,
                        v___y_4757_,
                        v___y_4758_,
                        v___y_4759_,
                        v___y_4760_,
                    );
                    if lean_obj_tag(v___x_4765_) == 0 {
                        v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
                        lean_inc(v_a_4766_);
                        lean_dec_ref_known(v___x_4765_, 1);
                        v_auxFunNames_4767_ = lean_ctor_get(v_ctx_4750_, 2);
                        v_numParams_4768_ = lean_ctor_get(v___x_4764_, 1);
                        v___x_4769_ = lean_box(0);
                        v___x_4770_ =
                            lean_array_get_borrowed(v___x_4769_, v_auxFunNames_4767_, v_a_4753_);
                        v___x_4865_ = lean_unsigned_to_nat(0);
                        v___x_4866_ = lean_array_get_size(v_a_4766_);
                        v___x_4867_ = lean_nat_dec_le(v_numParams_4768_, v___x_4865_);
                        if v___x_4867_ == 0 {
                            lean_inc(v_numParams_4768_);
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
                        lean_dec_ref(v_b_4754_);
                        lean_dec(v_a_4753_);
                        lean_dec(v_className_4752_);
                        lean_dec_ref(v_argNames_4751_);
                        v_a_4868_ = lean_ctor_get(v___x_4765_, 0);
                        v_isSharedCheck_4875_ = (!lean_is_exclusive(v___x_4765_)) as u8;
                        if v_isSharedCheck_4875_ == 0 {
                            v___x_4870_ = v___x_4765_;
                            v_isShared_4871_ = v_isSharedCheck_4875_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4868_);
                            lean_dec(v___x_4765_);
                            v___x_4870_ = lean_box(0);
                            v_isShared_4871_ = v_isSharedCheck_4875_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4774_ = l_Array_toSubarray___redArg(v_a_4766_, v_lower_4772_, v_upper_4773_);
                lean_inc_ref(v___x_4774_);
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
                if lean_obj_tag(v___x_4776_) == 0 {
                    v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
                    lean_inc(v_a_4777_);
                    lean_dec_ref_known(v___x_4776_, 1);
                    v___x_4778_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_4768_);
                    lean_inc_ref(v_argNames_4751_);
                    v___x_4779_ = l_Array_toSubarray___redArg(
                        v_argNames_4751_,
                        v___x_4778_,
                        v_numParams_4768_,
                    );
                    v___x_4780_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
                    v___x_4781_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_4779_, v___x_4780_);
                    v___x_4782_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_4774_, v___x_4780_);
                    v_a_4783_ = l_Array_append___redArg(v___x_4781_, v___x_4782_);
                    lean_dec_ref(v___x_4782_);
                    v___x_4784_ = lean_array_get_size(v_a_4783_);
                    v___x_4785_ = l_Array_toSubarray___redArg(v_a_4783_, v___x_4778_, v___x_4784_);
                    v___x_4786_ = l_Subarray_copy___redArg(v___x_4785_);
                    lean_inc(v___x_4764_);
                    v___x_4787_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                        v___x_4764_,
                        v___x_4786_,
                        v___y_4759_,
                    );
                    if lean_obj_tag(v___x_4787_) == 0 {
                        v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
                        lean_inc(v_a_4788_);
                        lean_dec_ref_known(v___x_4787_, 1);
                        v_ref_4789_ = lean_ctor_get(v___y_4759_, 5);
                        v___x_4790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
                        if lean_obj_tag(v___x_4790_) == 0 {
                            v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
                            lean_inc(v_a_4791_);
                            lean_dec_ref_known(v___x_4790_, 1);
                            v___x_4792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1;
                            v___x_4793_ =
                                l_Lean_Core_mkFreshUserName(v___x_4792_, v___y_4759_, v___y_4760_);
                            if lean_obj_tag(v___x_4793_) == 0 {
                                v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
                                lean_inc(v_a_4794_);
                                lean_dec_ref_known(v___x_4793_, 1);
                                v___x_4795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
                                if lean_obj_tag(v___x_4795_) == 0 {
                                    v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
                                    lean_inc_n(v_a_4796_, 8);
                                    lean_dec_ref_known(v___x_4795_, 1);
                                    v___x_4797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2;
                                    lean_inc_n(v_a_4791_, 3);
                                    v___x_4798_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_4798_, 0, v_a_4791_);
                                    lean_ctor_set(v___x_4798_, 1, v___x_4797_);
                                    v___x_4799_ =
                                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                    lean_inc(v___x_4770_);
                                    v___x_4800_ = lean_mk_syntax_ident(v___x_4770_);
                                    v___x_4801_ =
                                        l_Lean_Syntax_node1(v_a_4791_, v___x_4799_, v___x_4800_);
                                    v___x_4802_ = 0;
                                    v___x_4803_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4789_, v___x_4802_);
                                    lean_inc(v___x_4803_);
                                    v___x_4804_ =
                                        l_Lean_Syntax_node1(v___x_4803_, v___x_4799_, v_a_4788_);
                                    v___x_4805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3;
                                    v___x_4806_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_4806_, 0, v_a_4791_);
                                    lean_ctor_set(v___x_4806_, 1, v___x_4805_);
                                    v___x_4807_ =
                                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                    lean_inc(v_className_4752_);
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
                                    v___x_4817_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once), _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
                                    v___x_4818_ = l_Array_append___redArg(v___x_4817_, v_a_4777_);
                                    lean_dec(v_a_4777_);
                                    v___x_4819_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_4819_, 0, v_a_4796_);
                                    lean_ctor_set(v___x_4819_, 1, v___x_4799_);
                                    lean_ctor_set(v___x_4819_, 2, v___x_4818_);
                                    v___x_4820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13;
                                    v___x_4821_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                                    v___x_4822_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_4822_, 0, v_a_4796_);
                                    lean_ctor_set(v___x_4822_, 1, v___x_4821_);
                                    v___x_4823_ = l_Lean_Syntax_node2(
                                        v_a_4796_,
                                        v___x_4820_,
                                        v___x_4822_,
                                        v___x_4809_,
                                    );
                                    v___x_4824_ =
                                        l_Lean_Syntax_node1(v_a_4796_, v___x_4799_, v___x_4823_);
                                    v___x_4825_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15;
                                    v___x_4826_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_4826_, 0, v_a_4796_);
                                    lean_ctor_set(v___x_4826_, 1, v___x_4825_);
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
                                    v___x_4830_ = lean_unsigned_to_nat(1);
                                    v___x_4831_ = lean_nat_add(v_a_4753_, v___x_4830_);
                                    lean_dec(v_a_4753_);
                                    v_a_4753_ = v___x_4831_;
                                    v_b_4754_ = v___x_4829_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec(v_a_4794_);
                                    lean_dec(v_a_4791_);
                                    lean_dec(v_a_4788_);
                                    lean_dec(v_a_4777_);
                                    lean_dec_ref(v_b_4754_);
                                    lean_dec(v_a_4753_);
                                    lean_dec(v_className_4752_);
                                    lean_dec_ref(v_argNames_4751_);
                                    v_a_4833_ = lean_ctor_get(v___x_4795_, 0);
                                    v_isSharedCheck_4840_ = (!lean_is_exclusive(v___x_4795_)) as u8;
                                    if v_isSharedCheck_4840_ == 0 {
                                        v___x_4835_ = v___x_4795_;
                                        v_isShared_4836_ = v_isSharedCheck_4840_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4833_);
                                        lean_dec(v___x_4795_);
                                        v___x_4835_ = lean_box(0);
                                        v_isShared_4836_ = v_isSharedCheck_4840_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4791_);
                                lean_dec(v_a_4788_);
                                lean_dec(v_a_4777_);
                                lean_dec_ref(v_b_4754_);
                                lean_dec(v_a_4753_);
                                lean_dec(v_className_4752_);
                                lean_dec_ref(v_argNames_4751_);
                                v_a_4841_ = lean_ctor_get(v___x_4793_, 0);
                                v_isSharedCheck_4848_ = (!lean_is_exclusive(v___x_4793_)) as u8;
                                if v_isSharedCheck_4848_ == 0 {
                                    v___x_4843_ = v___x_4793_;
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4841_);
                                    lean_dec(v___x_4793_);
                                    v___x_4843_ = lean_box(0);
                                    v_isShared_4844_ = v_isSharedCheck_4848_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4788_);
                            lean_dec(v_a_4777_);
                            lean_dec_ref(v_b_4754_);
                            lean_dec(v_a_4753_);
                            lean_dec(v_className_4752_);
                            lean_dec_ref(v_argNames_4751_);
                            v_a_4849_ = lean_ctor_get(v___x_4790_, 0);
                            v_isSharedCheck_4856_ = (!lean_is_exclusive(v___x_4790_)) as u8;
                            if v_isSharedCheck_4856_ == 0 {
                                v___x_4851_ = v___x_4790_;
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4849_);
                                lean_dec(v___x_4790_);
                                v___x_4851_ = lean_box(0);
                                v_isShared_4852_ = v_isSharedCheck_4856_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4777_);
                        lean_dec_ref(v_b_4754_);
                        lean_dec(v_a_4753_);
                        lean_dec(v_className_4752_);
                        lean_dec_ref(v_argNames_4751_);
                        v_a_4857_ = lean_ctor_get(v___x_4787_, 0);
                        v_isSharedCheck_4864_ = (!lean_is_exclusive(v___x_4787_)) as u8;
                        if v_isSharedCheck_4864_ == 0 {
                            v___x_4859_ = v___x_4787_;
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4857_);
                            lean_dec(v___x_4787_);
                            v___x_4859_ = lean_box(0);
                            v_isShared_4860_ = v_isSharedCheck_4864_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_4774_);
                    lean_dec_ref(v_b_4754_);
                    lean_dec(v_a_4753_);
                    lean_dec(v_className_4752_);
                    lean_dec_ref(v_argNames_4751_);
                    return v___x_4776_;
                }
            }
            2 => {
                if v_isShared_4836_ == 0 {
                    v___x_4838_ = v___x_4835_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
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
                    v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
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
                    v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
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
                    v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
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
                    v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
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
    mut v_upperBound_4876_: *mut LeanObject,
    mut v___x_4877_: *mut LeanObject,
    mut v_ctx_4878_: *mut LeanObject,
    mut v_argNames_4879_: *mut LeanObject,
    mut v_className_4880_: *mut LeanObject,
    mut v_a_4881_: *mut LeanObject,
    mut v_b_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4890_: *mut LeanObject = core::ptr::null_mut();
    v_res_4890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_4876_, v___x_4877_, v_ctx_4878_, v_argNames_4879_, v_className_4880_, v_a_4881_, v_b_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
    lean_dec(v___y_4888_);
    lean_dec_ref(v___y_4887_);
    lean_dec(v___y_4886_);
    lean_dec_ref(v___y_4885_);
    lean_dec(v___y_4884_);
    lean_dec_ref(v___y_4883_);
    lean_dec_ref(v_ctx_4878_);
    lean_dec_ref(v___x_4877_);
    lean_dec(v_upperBound_4876_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(
    mut v_ctx_4891_: *mut LeanObject,
    mut v_className_4892_: *mut LeanObject,
    mut v_argNames_4893_: *mut LeanObject,
    mut v_a_4894_: *mut LeanObject,
    mut v_a_4895_: *mut LeanObject,
    mut v_a_4896_: *mut LeanObject,
    mut v_a_4897_: *mut LeanObject,
    mut v_a_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_typeInfos_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_letDecls_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    v_typeInfos_4901_ = lean_ctor_get(v_ctx_4891_, 1);
    v___x_4902_ = lean_array_get_size(v_typeInfos_4901_);
    v___x_4903_ = lean_unsigned_to_nat(0);
    v_letDecls_4904_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
    v___x_4905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_4902_, v_typeInfos_4901_, v_ctx_4891_, v_argNames_4893_, v_className_4892_, v___x_4903_, v_letDecls_4904_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(
    mut v_ctx_4906_: *mut LeanObject,
    mut v_className_4907_: *mut LeanObject,
    mut v_argNames_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
    mut v_a_4910_: *mut LeanObject,
    mut v_a_4911_: *mut LeanObject,
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4916_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4914_);
    lean_dec_ref(v_a_4913_);
    lean_dec(v_a_4912_);
    lean_dec_ref(v_a_4911_);
    lean_dec(v_a_4910_);
    lean_dec_ref(v_a_4909_);
    lean_dec_ref(v_ctx_4906_);
    return v_res_4916_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(
    mut v_inst_4917_: *mut LeanObject,
    mut v_R_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
    mut v_b_4920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    v___x_4921_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_4919_, v_b_4920_);
    return v___x_4921_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(
    mut v_upperBound_4922_: *mut LeanObject,
    mut v___x_4923_: *mut LeanObject,
    mut v_ctx_4924_: *mut LeanObject,
    mut v_argNames_4925_: *mut LeanObject,
    mut v_className_4926_: *mut LeanObject,
    mut v_inst_4927_: *mut LeanObject,
    mut v_R_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
    mut v_b_4930_: *mut LeanObject,
    mut v_c_4931_: *mut LeanObject,
    mut v___y_4932_: *mut LeanObject,
    mut v___y_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_4922_, v___x_4923_, v_ctx_4924_, v_argNames_4925_, v_className_4926_, v_a_4929_, v_b_4930_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
    return v___x_4939_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_4940_: *mut LeanObject = *_args.add(0);
    let mut v___x_4941_: *mut LeanObject = *_args.add(1);
    let mut v_ctx_4942_: *mut LeanObject = *_args.add(2);
    let mut v_argNames_4943_: *mut LeanObject = *_args.add(3);
    let mut v_className_4944_: *mut LeanObject = *_args.add(4);
    let mut v_inst_4945_: *mut LeanObject = *_args.add(5);
    let mut v_R_4946_: *mut LeanObject = *_args.add(6);
    let mut v_a_4947_: *mut LeanObject = *_args.add(7);
    let mut v_b_4948_: *mut LeanObject = *_args.add(8);
    let mut v_c_4949_: *mut LeanObject = *_args.add(9);
    let mut v___y_4950_: *mut LeanObject = *_args.add(10);
    let mut v___y_4951_: *mut LeanObject = *_args.add(11);
    let mut v___y_4952_: *mut LeanObject = *_args.add(12);
    let mut v___y_4953_: *mut LeanObject = *_args.add(13);
    let mut v___y_4954_: *mut LeanObject = *_args.add(14);
    let mut v___y_4955_: *mut LeanObject = *_args.add(15);
    let mut v___y_4956_: *mut LeanObject = *_args.add(16);
    let mut v_res_4957_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4955_);
    lean_dec_ref(v___y_4954_);
    lean_dec(v___y_4953_);
    lean_dec_ref(v___y_4952_);
    lean_dec(v___y_4951_);
    lean_dec_ref(v___y_4950_);
    lean_dec_ref(v_ctx_4942_);
    lean_dec_ref(v___x_4941_);
    lean_dec(v_upperBound_4940_);
    return v_res_4957_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(
    mut v_as_4971_: *mut LeanObject,
    mut v_i_4972_: usize,
    mut v_stop_4973_: usize,
    mut v_b_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4977_: u8 = 0;
    let mut v_ref_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = lean_usize_dec_eq(v_i_4972_, v_stop_4973_);
                if v___x_4977_ == 0 {
                    v_ref_4978_ = lean_ctor_get(v___y_4975_, 5);
                    v___x_4979_ = 1usize;
                    v___x_4980_ = lean_usize_sub(v_i_4972_, v___x_4979_);
                    v___x_4981_ = lean_array_uget_borrowed(v_as_4971_, v___x_4980_);
                    v___x_4982_ = l_Lean_SourceInfo_fromRef(v_ref_4978_, v___x_4977_);
                    v___x_4983_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0;
                    v___x_4984_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1;
                    lean_inc_n(v___x_4982_, 4);
                    v___x_4985_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4985_, 0, v___x_4982_);
                    lean_ctor_set(v___x_4985_, 1, v___x_4983_);
                    v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3;
                    v___x_4987_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_4988_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_4989_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4989_, 0, v___x_4982_);
                    lean_ctor_set(v___x_4989_, 1, v___x_4987_);
                    lean_ctor_set(v___x_4989_, 2, v___x_4988_);
                    v___x_4990_ = l_Lean_Syntax_node1(v___x_4982_, v___x_4986_, v___x_4989_);
                    v___x_4991_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4;
                    v___x_4992_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4992_, 0, v___x_4982_);
                    lean_ctor_set(v___x_4992_, 1, v___x_4991_);
                    lean_inc(v___x_4981_);
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
                    v___x_4995_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4995_, 0, v_b_4974_);
                    return v___x_4995_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(
    mut v_as_4996_: *mut LeanObject,
    mut v_i_4997_: *mut LeanObject,
    mut v_stop_4998_: *mut LeanObject,
    mut v_b_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5002_: usize = 0;
    let mut v_stop_boxed_5003_: usize = 0;
    let mut v_res_5004_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5002_ = lean_unbox_usize(v_i_4997_);
    lean_dec(v_i_4997_);
    v_stop_boxed_5003_ = lean_unbox_usize(v_stop_4998_);
    lean_dec(v_stop_4998_);
    v_res_5004_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_4996_, v_i_boxed_5002_, v_stop_boxed_5003_, v_b_4999_, v___y_5000_);
    lean_dec_ref(v___y_5000_);
    lean_dec_ref(v_as_4996_);
    return v_res_5004_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkLet(
    mut v_letDecls_5005_: *mut LeanObject,
    mut v_body_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
    mut v_a_5010_: *mut LeanObject,
    mut v_a_5011_: *mut LeanObject,
    mut v_a_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    v___x_5014_ = lean_array_get_size(v_letDecls_5005_);
    v___x_5015_ = lean_unsigned_to_nat(0);
    v___x_5016_ = lean_nat_dec_lt(v___x_5015_, v___x_5014_);
    if v___x_5016_ == 0 {
        let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
        v___x_5017_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5017_, 0, v_body_5006_);
        return v___x_5017_;
    } else {
        let mut v___x_5018_: usize = 0;
        let mut v___x_5019_: usize = 0;
        let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
        v___x_5018_ = lean_usize_of_nat(v___x_5014_);
        v___x_5019_ = 0usize;
        v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_5005_, v___x_5018_, v___x_5019_, v_body_5006_, v_a_5011_);
        return v___x_5020_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_mkLet___boxed(
    mut v_letDecls_5021_: *mut LeanObject,
    mut v_body_5022_: *mut LeanObject,
    mut v_a_5023_: *mut LeanObject,
    mut v_a_5024_: *mut LeanObject,
    mut v_a_5025_: *mut LeanObject,
    mut v_a_5026_: *mut LeanObject,
    mut v_a_5027_: *mut LeanObject,
    mut v_a_5028_: *mut LeanObject,
    mut v_a_5029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5030_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5028_);
    lean_dec_ref(v_a_5027_);
    lean_dec(v_a_5026_);
    lean_dec_ref(v_a_5025_);
    lean_dec(v_a_5024_);
    lean_dec_ref(v_a_5023_);
    lean_dec_ref(v_letDecls_5021_);
    return v_res_5030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(
    mut v_as_5031_: *mut LeanObject,
    mut v_i_5032_: usize,
    mut v_stop_5033_: usize,
    mut v_b_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_5031_, v_i_5032_, v_stop_5033_, v_b_5034_, v___y_5039_);
    return v___x_5042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(
    mut v_as_5043_: *mut LeanObject,
    mut v_i_5044_: *mut LeanObject,
    mut v_stop_5045_: *mut LeanObject,
    mut v_b_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5054_: usize = 0;
    let mut v_stop_boxed_5055_: usize = 0;
    let mut v_res_5056_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5054_ = lean_unbox_usize(v_i_5044_);
    lean_dec(v_i_5044_);
    v_stop_boxed_5055_ = lean_unbox_usize(v_stop_5045_);
    lean_dec(v_stop_5045_);
    v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_5043_, v_i_boxed_5054_, v_stop_boxed_5055_, v_b_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
    lean_dec(v___y_5052_);
    lean_dec_ref(v___y_5051_);
    lean_dec(v___y_5050_);
    lean_dec_ref(v___y_5049_);
    lean_dec(v___y_5048_);
    lean_dec_ref(v___y_5047_);
    lean_dec_ref(v_as_5043_);
    return v_res_5056_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(
    mut v___f_5066_: *mut LeanObject,
    mut v___x_5067_: *mut LeanObject,
    mut v___x_5068_: *mut LeanObject,
    mut v___x_5069_: *mut LeanObject,
    mut v___x_5070_: *mut LeanObject,
    mut v_instName_5071_: *mut LeanObject,
    mut v___x_5072_: *mut LeanObject,
    mut v___x_5073_: *mut LeanObject,
    mut v_b_5074_: *mut LeanObject,
    mut v_____r_5075_: *mut LeanObject,
    mut v_val_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v_a_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5082_);
                lean_inc_ref(v___y_5081_);
                lean_inc(v___y_5080_);
                lean_inc_ref(v___y_5079_);
                lean_inc(v___y_5078_);
                lean_inc_ref(v___y_5077_);
                v___x_5084_ = lean_apply_7(
                    v___f_5066_,
                    v___y_5077_,
                    v___y_5078_,
                    v___y_5079_,
                    v___y_5080_,
                    v___y_5081_,
                    v___y_5082_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5084_) == 0 {
                    v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
                    v_isSharedCheck_5134_ = (!lean_is_exclusive(v___x_5084_)) as u8;
                    if v_isSharedCheck_5134_ == 0 {
                        v___x_5087_ = v___x_5084_;
                        v_isShared_5088_ = v_isSharedCheck_5134_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5085_);
                        lean_dec(v___x_5084_);
                        v___x_5087_ = lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5134_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_val_5076_);
                    lean_dec_ref(v_b_5074_);
                    lean_dec(v___x_5073_);
                    lean_dec(v_instName_5071_);
                    lean_dec_ref(v___x_5070_);
                    lean_dec(v___x_5069_);
                    lean_dec_ref(v___x_5068_);
                    lean_dec_ref(v___x_5067_);
                    v_a_5135_ = lean_ctor_get(v___x_5084_, 0);
                    v_isSharedCheck_5142_ = (!lean_is_exclusive(v___x_5084_)) as u8;
                    if v_isSharedCheck_5142_ == 0 {
                        v___x_5137_ = v___x_5084_;
                        v_isShared_5138_ = v_isSharedCheck_5142_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5135_);
                        lean_dec(v___x_5084_);
                        v___x_5137_ = lean_box(0);
                        v_isShared_5138_ = v_isSharedCheck_5142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0;
                v___x_5090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1;
                lean_inc_ref_n(v___x_5068_, 8);
                lean_inc_ref_n(v___x_5067_, 8);
                v___x_5091_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5090_);
                v___x_5092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2;
                v___x_5093_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5092_);
                v___x_5094_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                    ),
                    _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                );
                lean_inc_n(v___x_5069_, 2);
                lean_inc_n(v_a_5085_, 14);
                v___x_5095_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5095_, 0, v_a_5085_);
                lean_ctor_set(v___x_5095_, 1, v___x_5069_);
                lean_ctor_set(v___x_5095_, 2, v___x_5094_);
                lean_inc_ref_n(v___x_5095_, 12);
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
                lean_inc_ref(v___x_5070_);
                v___x_5100_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5070_, v___x_5099_);
                v___x_5101_ = l_Lean_Syntax_node1(v_a_5085_, v___x_5100_, v___x_5095_);
                v___x_5102_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5102_, 0, v_a_5085_);
                lean_ctor_set(v___x_5102_, 1, v___x_5097_);
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
                v___x_5111_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5111_, 0, v_a_5085_);
                lean_ctor_set(v___x_5111_, 1, v___x_5069_);
                lean_ctor_set(v___x_5111_, 2, v___x_5110_);
                v___x_5112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12;
                v___x_5113_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5070_, v___x_5112_);
                v___x_5114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                v___x_5115_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5115_, 0, v_a_5085_);
                lean_ctor_set(v___x_5115_, 1, v___x_5114_);
                v___x_5116_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5113_, v___x_5115_, v___x_5073_);
                v___x_5117_ = l_Lean_Syntax_node2(v_a_5085_, v___x_5109_, v___x_5111_, v___x_5116_);
                v___x_5118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6;
                v___x_5119_ =
                    l_Lean_Name_mkStr4(v___x_5067_, v___x_5068_, v___x_5089_, v___x_5118_);
                v___x_5120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15;
                v___x_5121_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5121_, 0, v_a_5085_);
                lean_ctor_set(v___x_5121_, 1, v___x_5120_);
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
                v___x_5130_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5130_, 0, v___x_5129_);
                if v_isShared_5088_ == 0 {
                    lean_ctor_set(v___x_5087_, 0, v___x_5130_);
                    v___x_5132_ = v___x_5087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5130_);
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
                    v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5143_: *mut LeanObject = *_args.add(0);
    let mut v___x_5144_: *mut LeanObject = *_args.add(1);
    let mut v___x_5145_: *mut LeanObject = *_args.add(2);
    let mut v___x_5146_: *mut LeanObject = *_args.add(3);
    let mut v___x_5147_: *mut LeanObject = *_args.add(4);
    let mut v_instName_5148_: *mut LeanObject = *_args.add(5);
    let mut v___x_5149_: *mut LeanObject = *_args.add(6);
    let mut v___x_5150_: *mut LeanObject = *_args.add(7);
    let mut v_b_5151_: *mut LeanObject = *_args.add(8);
    let mut v_____r_5152_: *mut LeanObject = *_args.add(9);
    let mut v_val_5153_: *mut LeanObject = *_args.add(10);
    let mut v___y_5154_: *mut LeanObject = *_args.add(11);
    let mut v___y_5155_: *mut LeanObject = *_args.add(12);
    let mut v___y_5156_: *mut LeanObject = *_args.add(13);
    let mut v___y_5157_: *mut LeanObject = *_args.add(14);
    let mut v___y_5158_: *mut LeanObject = *_args.add(15);
    let mut v___y_5159_: *mut LeanObject = *_args.add(16);
    let mut v___y_5160_: *mut LeanObject = *_args.add(17);
    let mut v_res_5161_: *mut LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5143_, v___x_5144_, v___x_5145_, v___x_5146_, v___x_5147_, v_instName_5148_, v___x_5149_, v___x_5150_, v_b_5151_, v_____r_5152_, v_val_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
    lean_dec(v___y_5159_);
    lean_dec_ref(v___y_5158_);
    lean_dec(v___y_5157_);
    lean_dec_ref(v___y_5156_);
    lean_dec(v___y_5155_);
    lean_dec_ref(v___y_5154_);
    lean_dec_ref(v___x_5149_);
    return v_res_5161_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(
    mut v_a_5162_: *mut LeanObject,
    mut v_as_5163_: *mut LeanObject,
    mut v_i_5164_: usize,
    mut v_stop_5165_: usize,
) -> u8 {
    let mut v___x_5166_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5173_: *mut LeanObject,
    mut v_as_5174_: *mut LeanObject,
    mut v_i_5175_: *mut LeanObject,
    mut v_stop_5176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5177_: usize = 0;
    let mut v_stop_boxed_5178_: usize = 0;
    let mut v_res_5179_: u8 = 0;
    let mut v_r_5180_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5177_ = lean_unbox_usize(v_i_5175_);
    lean_dec(v_i_5175_);
    v_stop_boxed_5178_ = lean_unbox_usize(v_stop_5176_);
    lean_dec(v_stop_5176_);
    v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_5173_, v_as_5174_, v_i_boxed_5177_, v_stop_boxed_5178_);
    lean_dec_ref(v_as_5174_);
    lean_dec(v_a_5173_);
    v_r_5180_ = lean_box((v_res_5179_) as usize);
    return v_r_5180_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(
    mut v_as_5181_: *mut LeanObject,
    mut v_a_5182_: *mut LeanObject,
) -> u8 {
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    v___x_5183_ = lean_unsigned_to_nat(0);
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
    mut v_as_5189_: *mut LeanObject,
    mut v_a_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5191_: u8 = 0;
    let mut v_r_5192_: *mut LeanObject = core::ptr::null_mut();
    v_res_5191_ =
        l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_5189_, v_a_5190_);
    lean_dec(v_a_5190_);
    lean_dec_ref(v_as_5189_);
    v_r_5192_ = lean_box((v_res_5191_) as usize);
    return v_r_5192_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(
    mut v_upperBound_5194_: *mut LeanObject,
    mut v___x_5195_: *mut LeanObject,
    mut v_typeNames_5196_: *mut LeanObject,
    mut v_className_5197_: *mut LeanObject,
    mut v_ctx_5198_: *mut LeanObject,
    mut v_useAnonCtor_5199_: u8,
    mut v_a_5200_: *mut LeanObject,
    mut v_b_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v_a_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_a_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instName_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxFunNames_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_a_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_a_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5303_: u8 = 0;
    let mut v_a_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5307_: u8 = 0;
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5234_ = lean_nat_dec_lt(v_a_5200_, v_upperBound_5194_);
                if v___x_5234_ == 0 {
                    lean_dec(v_a_5200_);
                    lean_dec_ref(v_ctx_5198_);
                    lean_dec(v_className_5197_);
                    v___x_5235_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5235_, 0, v_b_5201_);
                    return v___x_5235_;
                } else {
                    v___x_5236_ = l_Lean_instInhabitedInductiveVal_default;
                    v___x_5237_ = lean_array_get_borrowed(v___x_5236_, v___x_5195_, v_a_5200_);
                    v_toConstantVal_5238_ = lean_ctor_get(v___x_5237_, 0);
                    v_name_5239_ = lean_ctor_get(v_toConstantVal_5238_, 0);
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
                        lean_inc(v___x_5237_);
                        v___x_5241_ = l_Lean_Elab_Deriving_mkInductArgNames(
                            v___x_5237_,
                            v___y_5202_,
                            v___y_5203_,
                            v___y_5204_,
                            v___y_5205_,
                            v___y_5206_,
                            v___y_5207_,
                        );
                        if lean_obj_tag(v___x_5241_) == 0 {
                            v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
                            lean_inc_n(v_a_5242_, 2);
                            lean_dec_ref_known(v___x_5241_, 1);
                            v___x_5243_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                                v_a_5242_,
                                v___y_5202_,
                                v___y_5203_,
                                v___y_5204_,
                                v___y_5205_,
                                v___y_5206_,
                                v___y_5207_,
                            );
                            if lean_obj_tag(v___x_5243_) == 0 {
                                v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
                                lean_inc(v_a_5244_);
                                lean_dec_ref_known(v___x_5243_, 1);
                                lean_inc(v_a_5242_);
                                lean_inc(v___x_5237_);
                                lean_inc(v_className_5197_);
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
                                if lean_obj_tag(v___x_5245_) == 0 {
                                    v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
                                    lean_inc(v_a_5246_);
                                    lean_dec_ref_known(v___x_5245_, 1);
                                    lean_inc(v___x_5237_);
                                    v___x_5247_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                        v___x_5237_,
                                        v_a_5242_,
                                        v___y_5206_,
                                    );
                                    if lean_obj_tag(v___x_5247_) == 0 {
                                        v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
                                        lean_inc(v_a_5248_);
                                        lean_dec_ref_known(v___x_5247_, 1);
                                        v_instName_5249_ = lean_ctor_get(v_ctx_5198_, 0);
                                        v_auxFunNames_5250_ = lean_ctor_get(v_ctx_5198_, 2);
                                        v_ref_5251_ = lean_ctor_get(v___y_5206_, 5);
                                        v___f_5252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0;
                                        v___x_5253_ = lean_box(0);
                                        v___x_5254_ = lean_array_get_borrowed(
                                            v___x_5253_,
                                            v_auxFunNames_5250_,
                                            v_a_5200_,
                                        );
                                        v___x_5255_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0;
                                        v___x_5256_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1;
                                        v___x_5257_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2;
                                        v___x_5258_ = l_Array_append___redArg(v_a_5244_, v_a_5246_);
                                        lean_dec(v_a_5246_);
                                        v___x_5259_ = 0;
                                        v___x_5260_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_5251_, v___x_5259_);
                                        v___x_5261_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4;
                                        lean_inc(v_className_5197_);
                                        v___x_5262_ = l_Lean_mkCIdent(v_className_5197_);
                                        v___x_5263_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                                        lean_inc(v___x_5260_);
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
                                        lean_inc(v___x_5254_);
                                        v___x_5266_ = lean_mk_syntax_ident(v___x_5254_);
                                        if v_useAnonCtor_5199_ == 0 {
                                            v___x_5267_ = lean_box(0);
                                            lean_inc(v_instName_5249_);
                                            v___x_5268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5252_, v___x_5255_, v___x_5256_, v___x_5263_, v___x_5257_, v_instName_5249_, v___x_5258_, v___x_5265_, v_b_5201_, v___x_5267_, v___x_5266_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                            lean_dec_ref(v___x_5258_);
                                            v___y_5215_ = v___x_5268_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_5269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                            if lean_obj_tag(v___x_5269_) == 0 {
                                                v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
                                                lean_inc_n(v_a_5270_, 4);
                                                lean_dec_ref_known(v___x_5269_, 1);
                                                v___x_5271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5;
                                                v___x_5272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2;
                                                v___x_5273_ = lean_alloc_ctor(2, 2, (0) as u32);
                                                lean_ctor_set(v___x_5273_, 0, v_a_5270_);
                                                lean_ctor_set(v___x_5273_, 1, v___x_5272_);
                                                v___x_5274_ = l_Lean_Syntax_node1(
                                                    v_a_5270_,
                                                    v___x_5263_,
                                                    v___x_5266_,
                                                );
                                                v___x_5275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3;
                                                v___x_5276_ = lean_alloc_ctor(2, 2, (0) as u32);
                                                lean_ctor_set(v___x_5276_, 0, v_a_5270_);
                                                lean_ctor_set(v___x_5276_, 1, v___x_5275_);
                                                v___x_5277_ = l_Lean_Syntax_node3(
                                                    v_a_5270_,
                                                    v___x_5271_,
                                                    v___x_5273_,
                                                    v___x_5274_,
                                                    v___x_5276_,
                                                );
                                                v___x_5278_ = lean_box(0);
                                                lean_inc(v_instName_5249_);
                                                v___x_5279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_5252_, v___x_5255_, v___x_5256_, v___x_5263_, v___x_5257_, v_instName_5249_, v___x_5258_, v___x_5265_, v_b_5201_, v___x_5278_, v___x_5277_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                                                lean_dec_ref(v___x_5258_);
                                                v___y_5215_ = v___x_5279_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_dec(v___x_5266_);
                                                lean_dec(v___x_5265_);
                                                lean_dec_ref(v___x_5258_);
                                                lean_dec_ref(v_b_5201_);
                                                lean_dec(v_a_5200_);
                                                lean_dec_ref(v_ctx_5198_);
                                                lean_dec(v_className_5197_);
                                                v_a_5280_ = lean_ctor_get(v___x_5269_, 0);
                                                v_isSharedCheck_5287_ =
                                                    (!lean_is_exclusive(v___x_5269_)) as u8;
                                                if v_isSharedCheck_5287_ == 0 {
                                                    v___x_5282_ = v___x_5269_;
                                                    v_isShared_5283_ = v_isSharedCheck_5287_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5280_);
                                                    lean_dec(v___x_5269_);
                                                    v___x_5282_ = lean_box(0);
                                                    v_isShared_5283_ = v_isSharedCheck_5287_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5246_);
                                        lean_dec(v_a_5244_);
                                        lean_dec_ref(v_b_5201_);
                                        lean_dec(v_a_5200_);
                                        lean_dec_ref(v_ctx_5198_);
                                        lean_dec(v_className_5197_);
                                        v_a_5288_ = lean_ctor_get(v___x_5247_, 0);
                                        v_isSharedCheck_5295_ =
                                            (!lean_is_exclusive(v___x_5247_)) as u8;
                                        if v_isSharedCheck_5295_ == 0 {
                                            v___x_5290_ = v___x_5247_;
                                            v_isShared_5291_ = v_isSharedCheck_5295_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5288_);
                                            lean_dec(v___x_5247_);
                                            v___x_5290_ = lean_box(0);
                                            v_isShared_5291_ = v_isSharedCheck_5295_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5244_);
                                    lean_dec(v_a_5242_);
                                    lean_dec_ref(v_b_5201_);
                                    lean_dec(v_a_5200_);
                                    lean_dec_ref(v_ctx_5198_);
                                    lean_dec(v_className_5197_);
                                    v_a_5296_ = lean_ctor_get(v___x_5245_, 0);
                                    v_isSharedCheck_5303_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                                    if v_isSharedCheck_5303_ == 0 {
                                        v___x_5298_ = v___x_5245_;
                                        v_isShared_5299_ = v_isSharedCheck_5303_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5296_);
                                        lean_dec(v___x_5245_);
                                        v___x_5298_ = lean_box(0);
                                        v_isShared_5299_ = v_isSharedCheck_5303_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5242_);
                                lean_dec_ref(v_b_5201_);
                                lean_dec(v_a_5200_);
                                lean_dec_ref(v_ctx_5198_);
                                lean_dec(v_className_5197_);
                                return v___x_5243_;
                            }
                        } else {
                            lean_dec_ref(v_b_5201_);
                            lean_dec(v_a_5200_);
                            lean_dec_ref(v_ctx_5198_);
                            lean_dec(v_className_5197_);
                            v_a_5304_ = lean_ctor_get(v___x_5241_, 0);
                            v_isSharedCheck_5311_ = (!lean_is_exclusive(v___x_5241_)) as u8;
                            if v_isSharedCheck_5311_ == 0 {
                                v___x_5306_ = v___x_5241_;
                                v_isShared_5307_ = v_isSharedCheck_5311_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_5304_);
                                lean_dec(v___x_5241_);
                                v___x_5306_ = lean_box(0);
                                v_isShared_5307_ = v_isSharedCheck_5311_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5211_ = lean_unsigned_to_nat(1);
                v___x_5212_ = lean_nat_add(v_a_5200_, v___x_5211_);
                lean_dec(v_a_5200_);
                v_a_5200_ = v___x_5212_;
                v_b_5201_ = v_a_5210_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_5215_) == 0 {
                    v_a_5216_ = lean_ctor_get(v___y_5215_, 0);
                    v_isSharedCheck_5225_ = (!lean_is_exclusive(v___y_5215_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5218_ = v___y_5215_;
                        v_isShared_5219_ = v_isSharedCheck_5225_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5216_);
                        lean_dec(v___y_5215_);
                        v___x_5218_ = lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5225_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5200_);
                    lean_dec_ref(v_ctx_5198_);
                    lean_dec(v_className_5197_);
                    v_a_5226_ = lean_ctor_get(v___y_5215_, 0);
                    v_isSharedCheck_5233_ = (!lean_is_exclusive(v___y_5215_)) as u8;
                    if v_isSharedCheck_5233_ == 0 {
                        v___x_5228_ = v___y_5215_;
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5226_);
                        lean_dec(v___y_5215_);
                        v___x_5228_ = lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_5216_) == 0 {
                    lean_dec(v_a_5200_);
                    lean_dec_ref(v_ctx_5198_);
                    lean_dec(v_className_5197_);
                    v_a_5220_ = lean_ctor_get(v_a_5216_, 0);
                    lean_inc(v_a_5220_);
                    lean_dec_ref_known(v_a_5216_, 1);
                    if v_isShared_5219_ == 0 {
                        lean_ctor_set(v___x_5218_, 0, v_a_5220_);
                        v___x_5222_ = v___x_5218_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5220_);
                        v___x_5222_ = v_reuseFailAlloc_5223_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5218_);
                    v_a_5224_ = lean_ctor_get(v_a_5216_, 0);
                    lean_inc(v_a_5224_);
                    lean_dec_ref_known(v_a_5216_, 1);
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
                    v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
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
                    v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
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
                    v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
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
                    v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
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
                    v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
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
    mut v_upperBound_5312_: *mut LeanObject,
    mut v___x_5313_: *mut LeanObject,
    mut v_typeNames_5314_: *mut LeanObject,
    mut v_className_5315_: *mut LeanObject,
    mut v_ctx_5316_: *mut LeanObject,
    mut v_useAnonCtor_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
    mut v_b_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAnonCtor_boxed_5327_: u8 = 0;
    let mut v_res_5328_: *mut LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5327_ = (lean_unbox(v_useAnonCtor_5317_) as u8);
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
    lean_dec(v___y_5325_);
    lean_dec_ref(v___y_5324_);
    lean_dec(v___y_5323_);
    lean_dec_ref(v___y_5322_);
    lean_dec(v___y_5321_);
    lean_dec_ref(v___y_5320_);
    lean_dec_ref(v_typeNames_5314_);
    lean_dec_ref(v___x_5313_);
    lean_dec(v_upperBound_5312_);
    return v_res_5328_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstanceCmds(
    mut v_ctx_5329_: *mut LeanObject,
    mut v_className_5330_: *mut LeanObject,
    mut v_typeNames_5331_: *mut LeanObject,
    mut v_useAnonCtor_5332_: u8,
    mut v_a_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
    mut v_a_5336_: *mut LeanObject,
    mut v_a_5337_: *mut LeanObject,
    mut v_a_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_typeInfos_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instances_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    v_typeInfos_5340_ = lean_ctor_get(v_ctx_5329_, 1);
    lean_inc_ref(v_typeInfos_5340_);
    v___x_5341_ = lean_array_get_size(v_typeInfos_5340_);
    v___x_5342_ = lean_unsigned_to_nat(0);
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
    lean_dec_ref(v_typeInfos_5340_);
    return v___x_5344_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkInstanceCmds___boxed(
    mut v_ctx_5345_: *mut LeanObject,
    mut v_className_5346_: *mut LeanObject,
    mut v_typeNames_5347_: *mut LeanObject,
    mut v_useAnonCtor_5348_: *mut LeanObject,
    mut v_a_5349_: *mut LeanObject,
    mut v_a_5350_: *mut LeanObject,
    mut v_a_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
    mut v_a_5353_: *mut LeanObject,
    mut v_a_5354_: *mut LeanObject,
    mut v_a_5355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAnonCtor_boxed_5356_: u8 = 0;
    let mut v_res_5357_: *mut LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5356_ = (lean_unbox(v_useAnonCtor_5348_) as u8);
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
    lean_dec(v_a_5354_);
    lean_dec_ref(v_a_5353_);
    lean_dec(v_a_5352_);
    lean_dec_ref(v_a_5351_);
    lean_dec(v_a_5350_);
    lean_dec_ref(v_a_5349_);
    lean_dec_ref(v_typeNames_5347_);
    return v_res_5357_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(
    mut v_upperBound_5358_: *mut LeanObject,
    mut v___x_5359_: *mut LeanObject,
    mut v_typeNames_5360_: *mut LeanObject,
    mut v_className_5361_: *mut LeanObject,
    mut v_ctx_5362_: *mut LeanObject,
    mut v_useAnonCtor_5363_: u8,
    mut v_inst_5364_: *mut LeanObject,
    mut v_R_5365_: *mut LeanObject,
    mut v_a_5366_: *mut LeanObject,
    mut v_b_5367_: *mut LeanObject,
    mut v_c_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
    mut v___y_5371_: *mut LeanObject,
    mut v___y_5372_: *mut LeanObject,
    mut v___y_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_5377_: *mut LeanObject = *_args.add(0);
    let mut v___x_5378_: *mut LeanObject = *_args.add(1);
    let mut v_typeNames_5379_: *mut LeanObject = *_args.add(2);
    let mut v_className_5380_: *mut LeanObject = *_args.add(3);
    let mut v_ctx_5381_: *mut LeanObject = *_args.add(4);
    let mut v_useAnonCtor_5382_: *mut LeanObject = *_args.add(5);
    let mut v_inst_5383_: *mut LeanObject = *_args.add(6);
    let mut v_R_5384_: *mut LeanObject = *_args.add(7);
    let mut v_a_5385_: *mut LeanObject = *_args.add(8);
    let mut v_b_5386_: *mut LeanObject = *_args.add(9);
    let mut v_c_5387_: *mut LeanObject = *_args.add(10);
    let mut v___y_5388_: *mut LeanObject = *_args.add(11);
    let mut v___y_5389_: *mut LeanObject = *_args.add(12);
    let mut v___y_5390_: *mut LeanObject = *_args.add(13);
    let mut v___y_5391_: *mut LeanObject = *_args.add(14);
    let mut v___y_5392_: *mut LeanObject = *_args.add(15);
    let mut v___y_5393_: *mut LeanObject = *_args.add(16);
    let mut v___y_5394_: *mut LeanObject = *_args.add(17);
    let mut v_useAnonCtor_boxed_5395_: u8 = 0;
    let mut v_res_5396_: *mut LeanObject = core::ptr::null_mut();
    v_useAnonCtor_boxed_5395_ = (lean_unbox(v_useAnonCtor_5382_) as u8);
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
    lean_dec(v___y_5393_);
    lean_dec_ref(v___y_5392_);
    lean_dec(v___y_5391_);
    lean_dec_ref(v___y_5390_);
    lean_dec(v___y_5389_);
    lean_dec_ref(v___y_5388_);
    lean_dec_ref(v_typeNames_5379_);
    lean_dec_ref(v___x_5378_);
    lean_dec(v_upperBound_5377_);
    return v_res_5396_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___redArg(
    mut v_varName_5403_: *mut LeanObject,
    mut v_a_5404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5406_ = lean_ctor_get(v_a_5404_, 5);
    v___x_5407_ = 0;
    v___x_5408_ = l_Lean_SourceInfo_fromRef(v_ref_5406_, v___x_5407_);
    v___x_5409_ = l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1;
    v___x_5410_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
    v___x_5411_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once),
        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
    );
    lean_inc(v___x_5408_);
    v___x_5412_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_5412_, 0, v___x_5408_);
    lean_ctor_set(v___x_5412_, 1, v___x_5410_);
    lean_ctor_set(v___x_5412_, 2, v___x_5411_);
    v___x_5413_ = lean_mk_syntax_ident(v_varName_5403_);
    v___x_5414_ = l_Lean_Syntax_node2(v___x_5408_, v___x_5409_, v___x_5412_, v___x_5413_);
    v___x_5415_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5415_, 0, v___x_5414_);
    return v___x_5415_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(
    mut v_varName_5416_: *mut LeanObject,
    mut v_a_5417_: *mut LeanObject,
    mut v_a_5418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5419_: *mut LeanObject = core::ptr::null_mut();
    v_res_5419_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_5416_, v_a_5417_);
    lean_dec_ref(v_a_5417_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr(
    mut v_varName_5420_: *mut LeanObject,
    mut v_a_5421_: *mut LeanObject,
    mut v_a_5422_: *mut LeanObject,
    mut v_a_5423_: *mut LeanObject,
    mut v_a_5424_: *mut LeanObject,
    mut v_a_5425_: *mut LeanObject,
    mut v_a_5426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    v___x_5428_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_5420_, v_a_5425_);
    return v___x_5428_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscr___boxed(
    mut v_varName_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
    mut v_a_5431_: *mut LeanObject,
    mut v_a_5432_: *mut LeanObject,
    mut v_a_5433_: *mut LeanObject,
    mut v_a_5434_: *mut LeanObject,
    mut v_a_5435_: *mut LeanObject,
    mut v_a_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5437_: *mut LeanObject = core::ptr::null_mut();
    v_res_5437_ = l_Lean_Elab_Deriving_mkDiscr(
        v_varName_5429_,
        v_a_5430_,
        v_a_5431_,
        v_a_5432_,
        v_a_5433_,
        v_a_5434_,
        v_a_5435_,
    );
    lean_dec(v_a_5435_);
    lean_dec_ref(v_a_5434_);
    lean_dec(v_a_5433_);
    lean_dec_ref(v_a_5432_);
    lean_dec(v_a_5431_);
    lean_dec_ref(v_a_5430_);
    return v_res_5437_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(
    mut v_upperBound_5441_: *mut LeanObject,
    mut v_a_5442_: *mut LeanObject,
    mut v_b_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5459_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5447_ = lean_nat_dec_lt(v_a_5442_, v_upperBound_5441_);
                if v___x_5447_ == 0 {
                    lean_dec(v_a_5442_);
                    v___x_5448_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5448_, 0, v_b_5443_);
                    return v___x_5448_;
                } else {
                    v___x_5449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1;
                    v___x_5450_ =
                        l_Lean_Core_mkFreshUserName(v___x_5449_, v___y_5444_, v___y_5445_);
                    if lean_obj_tag(v___x_5450_) == 0 {
                        v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
                        lean_inc(v_a_5451_);
                        lean_dec_ref_known(v___x_5450_, 1);
                        v___x_5452_ = lean_array_push(v_b_5443_, v_a_5451_);
                        v___x_5453_ = lean_unsigned_to_nat(1);
                        v___x_5454_ = lean_nat_add(v_a_5442_, v___x_5453_);
                        lean_dec(v_a_5442_);
                        v_a_5442_ = v___x_5454_;
                        v_b_5443_ = v___x_5452_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_5443_);
                        lean_dec(v_a_5442_);
                        v_a_5456_ = lean_ctor_get(v___x_5450_, 0);
                        v_isSharedCheck_5463_ = (!lean_is_exclusive(v___x_5450_)) as u8;
                        if v_isSharedCheck_5463_ == 0 {
                            v___x_5458_ = v___x_5450_;
                            v_isShared_5459_ = v_isSharedCheck_5463_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5456_);
                            lean_dec(v___x_5450_);
                            v___x_5458_ = lean_box(0);
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
                    v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5456_);
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
    mut v_upperBound_5464_: *mut LeanObject,
    mut v_a_5465_: *mut LeanObject,
    mut v_b_5466_: *mut LeanObject,
    mut v___y_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5470_: *mut LeanObject = core::ptr::null_mut();
    v_res_5470_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(
            v_upperBound_5464_,
            v_a_5465_,
            v_b_5466_,
            v___y_5467_,
            v___y_5468_,
        );
    lean_dec(v___y_5468_);
    lean_dec_ref(v___y_5467_);
    lean_dec(v_upperBound_5464_);
    return v_res_5470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(
    mut v_a_5479_: *mut LeanObject,
    mut v_sz_5480_: usize,
    mut v_i_5481_: usize,
    mut v_bs_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: usize = 0;
    let mut v___x_5508_: usize = 0;
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_usize_dec_lt(v_i_5481_, v_sz_5480_);
                if v___x_5485_ == 0 {
                    lean_dec(v_a_5479_);
                    v___x_5486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5486_, 0, v_bs_5482_);
                    return v___x_5486_;
                } else {
                    v_ref_5487_ = lean_ctor_get(v___y_5483_, 5);
                    v_v_5488_ = lean_array_uget(v_bs_5482_, v_i_5481_);
                    v___x_5489_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5490_ = lean_array_uset(v_bs_5482_, v_i_5481_, v___x_5489_);
                    v___x_5491_ = 0;
                    v___x_5492_ = l_Lean_SourceInfo_fromRef(v_ref_5487_, v___x_5491_);
                    v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1;
                    v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2;
                    lean_inc_n(v___x_5492_, 6);
                    v___x_5495_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5495_, 0, v___x_5492_);
                    lean_ctor_set(v___x_5495_, 1, v___x_5494_);
                    v___x_5496_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9;
                    v___x_5497_ = lean_mk_syntax_ident(v_v_5488_);
                    v___x_5498_ = l_Lean_Syntax_node1(v___x_5492_, v___x_5496_, v___x_5497_);
                    v___x_5499_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14;
                    v___x_5500_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5500_, 0, v___x_5492_);
                    lean_ctor_set(v___x_5500_, 1, v___x_5499_);
                    lean_inc(v_a_5479_);
                    v___x_5501_ =
                        l_Lean_Syntax_node2(v___x_5492_, v___x_5496_, v___x_5500_, v_a_5479_);
                    v___x_5502_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once
                        ),
                        _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10,
                    );
                    v___x_5503_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_5503_, 0, v___x_5492_);
                    lean_ctor_set(v___x_5503_, 1, v___x_5496_);
                    lean_ctor_set(v___x_5503_, 2, v___x_5502_);
                    v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3;
                    v___x_5505_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5505_, 0, v___x_5492_);
                    lean_ctor_set(v___x_5505_, 1, v___x_5504_);
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
    mut v_a_5511_: *mut LeanObject,
    mut v_sz_5512_: *mut LeanObject,
    mut v_i_5513_: *mut LeanObject,
    mut v_bs_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5517_: usize = 0;
    let mut v_i_boxed_5518_: usize = 0;
    let mut v_res_5519_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5517_ = lean_unbox_usize(v_sz_5512_);
    lean_dec(v_sz_5512_);
    v_i_boxed_5518_ = lean_unbox_usize(v_i_5513_);
    lean_dec(v_i_5513_);
    v_res_5519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5511_, v_sz_boxed_5517_, v_i_boxed_5518_, v_bs_5514_, v___y_5515_);
    lean_dec_ref(v___y_5515_);
    return v_res_5519_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkHeader(
    mut v_className_5520_: *mut LeanObject,
    mut v_arity_5521_: *mut LeanObject,
    mut v_indVal_5522_: *mut LeanObject,
    mut v_a_5523_: *mut LeanObject,
    mut v_a_5524_: *mut LeanObject,
    mut v_a_5525_: *mut LeanObject,
    mut v_a_5526_: *mut LeanObject,
    mut v_a_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5542_: usize = 0;
    let mut v___x_5543_: usize = 0;
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5548_: u8 = 0;
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_a_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut v_a_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_a_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_a_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut v_a_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_indVal_5522_);
                v___x_5530_ = l_Lean_Elab_Deriving_mkInductArgNames(
                    v_indVal_5522_,
                    v_a_5523_,
                    v_a_5524_,
                    v_a_5525_,
                    v_a_5526_,
                    v_a_5527_,
                    v_a_5528_,
                );
                if lean_obj_tag(v___x_5530_) == 0 {
                    v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
                    lean_inc_n(v_a_5531_, 2);
                    lean_dec_ref_known(v___x_5530_, 1);
                    v___x_5532_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                        v_a_5531_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_,
                    );
                    if lean_obj_tag(v___x_5532_) == 0 {
                        v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
                        lean_inc(v_a_5533_);
                        lean_dec_ref_known(v___x_5532_, 1);
                        lean_inc(v_a_5531_);
                        lean_inc_ref(v_indVal_5522_);
                        v___x_5534_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                            v_indVal_5522_,
                            v_a_5531_,
                            v_a_5527_,
                        );
                        v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
                        lean_inc(v_a_5535_);
                        lean_dec_ref(v___x_5534_);
                        v___x_5536_ = lean_unsigned_to_nat(0);
                        v___x_5537_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0;
                        v___x_5538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_5521_, v___x_5536_, v___x_5537_, v_a_5527_, v_a_5528_);
                        if lean_obj_tag(v___x_5538_) == 0 {
                            v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
                            lean_inc(v_a_5539_);
                            lean_dec_ref_known(v___x_5538_, 1);
                            lean_inc(v_a_5531_);
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
                            if lean_obj_tag(v___x_5540_) == 0 {
                                v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
                                lean_inc(v_a_5541_);
                                lean_dec_ref_known(v___x_5540_, 1);
                                v_sz_5542_ = lean_array_size(v_a_5539_);
                                v___x_5543_ = 0usize;
                                lean_inc(v_a_5539_);
                                lean_inc(v_a_5535_);
                                v___x_5544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5535_, v_sz_5542_, v___x_5543_, v_a_5539_, v_a_5527_);
                                if lean_obj_tag(v___x_5544_) == 0 {
                                    v_a_5545_ = lean_ctor_get(v___x_5544_, 0);
                                    v_isSharedCheck_5555_ = (!lean_is_exclusive(v___x_5544_)) as u8;
                                    if v_isSharedCheck_5555_ == 0 {
                                        v___x_5547_ = v___x_5544_;
                                        v_isShared_5548_ = v_isSharedCheck_5555_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5545_);
                                        lean_dec(v___x_5544_);
                                        v___x_5547_ = lean_box(0);
                                        v_isShared_5548_ = v_isSharedCheck_5555_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5541_);
                                    lean_dec(v_a_5539_);
                                    lean_dec(v_a_5535_);
                                    lean_dec(v_a_5533_);
                                    lean_dec(v_a_5531_);
                                    v_a_5556_ = lean_ctor_get(v___x_5544_, 0);
                                    v_isSharedCheck_5563_ = (!lean_is_exclusive(v___x_5544_)) as u8;
                                    if v_isSharedCheck_5563_ == 0 {
                                        v___x_5558_ = v___x_5544_;
                                        v_isShared_5559_ = v_isSharedCheck_5563_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5556_);
                                        lean_dec(v___x_5544_);
                                        v___x_5558_ = lean_box(0);
                                        v_isShared_5559_ = v_isSharedCheck_5563_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5539_);
                                lean_dec(v_a_5535_);
                                lean_dec(v_a_5533_);
                                lean_dec(v_a_5531_);
                                v_a_5564_ = lean_ctor_get(v___x_5540_, 0);
                                v_isSharedCheck_5571_ = (!lean_is_exclusive(v___x_5540_)) as u8;
                                if v_isSharedCheck_5571_ == 0 {
                                    v___x_5566_ = v___x_5540_;
                                    v_isShared_5567_ = v_isSharedCheck_5571_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5564_);
                                    lean_dec(v___x_5540_);
                                    v___x_5566_ = lean_box(0);
                                    v_isShared_5567_ = v_isSharedCheck_5571_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5535_);
                            lean_dec(v_a_5533_);
                            lean_dec(v_a_5531_);
                            lean_dec_ref(v_indVal_5522_);
                            lean_dec(v_className_5520_);
                            v_a_5572_ = lean_ctor_get(v___x_5538_, 0);
                            v_isSharedCheck_5579_ = (!lean_is_exclusive(v___x_5538_)) as u8;
                            if v_isSharedCheck_5579_ == 0 {
                                v___x_5574_ = v___x_5538_;
                                v_isShared_5575_ = v_isSharedCheck_5579_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5572_);
                                lean_dec(v___x_5538_);
                                v___x_5574_ = lean_box(0);
                                v_isShared_5575_ = v_isSharedCheck_5579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5531_);
                        lean_dec_ref(v_indVal_5522_);
                        lean_dec(v_className_5520_);
                        v_a_5580_ = lean_ctor_get(v___x_5532_, 0);
                        v_isSharedCheck_5587_ = (!lean_is_exclusive(v___x_5532_)) as u8;
                        if v_isSharedCheck_5587_ == 0 {
                            v___x_5582_ = v___x_5532_;
                            v_isShared_5583_ = v_isSharedCheck_5587_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5580_);
                            lean_dec(v___x_5532_);
                            v___x_5582_ = lean_box(0);
                            v_isShared_5583_ = v_isSharedCheck_5587_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_indVal_5522_);
                    lean_dec(v_className_5520_);
                    v_a_5588_ = lean_ctor_get(v___x_5530_, 0);
                    v_isSharedCheck_5595_ = (!lean_is_exclusive(v___x_5530_)) as u8;
                    if v_isSharedCheck_5595_ == 0 {
                        v___x_5590_ = v___x_5530_;
                        v_isShared_5591_ = v_isSharedCheck_5595_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5588_);
                        lean_dec(v___x_5530_);
                        v___x_5590_ = lean_box(0);
                        v_isShared_5591_ = v_isSharedCheck_5595_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5549_ = l_Array_append___redArg(v_a_5533_, v_a_5541_);
                lean_dec(v_a_5541_);
                v___x_5550_ = l_Array_append___redArg(v___x_5549_, v_a_5545_);
                lean_dec(v_a_5545_);
                v___x_5551_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5551_, 0, v___x_5550_);
                lean_ctor_set(v___x_5551_, 1, v_a_5531_);
                lean_ctor_set(v___x_5551_, 2, v_a_5539_);
                lean_ctor_set(v___x_5551_, 3, v_a_5535_);
                if v_isShared_5548_ == 0 {
                    lean_ctor_set(v___x_5547_, 0, v___x_5551_);
                    v___x_5553_ = v___x_5547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5551_);
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
                    v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
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
                    v_reuseFailAlloc_5570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_a_5564_);
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
                    v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
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
                    v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
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
                    v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
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
    mut v_className_5596_: *mut LeanObject,
    mut v_arity_5597_: *mut LeanObject,
    mut v_indVal_5598_: *mut LeanObject,
    mut v_a_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
    mut v_a_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
    mut v_a_5603_: *mut LeanObject,
    mut v_a_5604_: *mut LeanObject,
    mut v_a_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5606_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5604_);
    lean_dec_ref(v_a_5603_);
    lean_dec(v_a_5602_);
    lean_dec_ref(v_a_5601_);
    lean_dec(v_a_5600_);
    lean_dec_ref(v_a_5599_);
    lean_dec(v_arity_5597_);
    return v_res_5606_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(
    mut v_a_5607_: *mut LeanObject,
    mut v_sz_5608_: usize,
    mut v_i_5609_: usize,
    mut v_bs_5610_: *mut LeanObject,
    mut v___y_5611_: *mut LeanObject,
    mut v___y_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
    mut v___y_5615_: *mut LeanObject,
    mut v___y_5616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    v___x_5618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_5607_, v_sz_5608_, v_i_5609_, v_bs_5610_, v___y_5615_);
    return v___x_5618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(
    mut v_a_5619_: *mut LeanObject,
    mut v_sz_5620_: *mut LeanObject,
    mut v_i_5621_: *mut LeanObject,
    mut v_bs_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
    mut v___y_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5630_: usize = 0;
    let mut v_i_boxed_5631_: usize = 0;
    let mut v_res_5632_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5630_ = lean_unbox_usize(v_sz_5620_);
    lean_dec(v_sz_5620_);
    v_i_boxed_5631_ = lean_unbox_usize(v_i_5621_);
    lean_dec(v_i_5621_);
    v_res_5632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_5619_, v_sz_boxed_5630_, v_i_boxed_5631_, v_bs_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
    lean_dec(v___y_5628_);
    lean_dec_ref(v___y_5627_);
    lean_dec(v___y_5626_);
    lean_dec_ref(v___y_5625_);
    lean_dec(v___y_5624_);
    lean_dec_ref(v___y_5623_);
    return v_res_5632_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(
    mut v_upperBound_5633_: *mut LeanObject,
    mut v_inst_5634_: *mut LeanObject,
    mut v_R_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
    mut v_b_5637_: *mut LeanObject,
    mut v_c_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_upperBound_5647_: *mut LeanObject,
    mut v_inst_5648_: *mut LeanObject,
    mut v_R_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_b_5651_: *mut LeanObject,
    mut v_c_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5660_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5658_);
    lean_dec_ref(v___y_5657_);
    lean_dec(v___y_5656_);
    lean_dec_ref(v___y_5655_);
    lean_dec(v___y_5654_);
    lean_dec_ref(v___y_5653_);
    lean_dec(v_upperBound_5647_);
    return v_res_5660_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
    mut v_a_5661_: *mut LeanObject,
    mut v_b_5662_: *mut LeanObject,
    mut v___y_5663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5670_: u8 = 0;
    let mut v___x_5671_: u8 = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5686_: u8 = 0;
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5690_: u8 = 0;
    let mut v_isSharedCheck_5691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5665_ = lean_ctor_get(v_a_5661_, 0);
                v_start_5666_ = lean_ctor_get(v_a_5661_, 1);
                v_stop_5667_ = lean_ctor_get(v_a_5661_, 2);
                v_isSharedCheck_5691_ = (!lean_is_exclusive(v_a_5661_)) as u8;
                if v_isSharedCheck_5691_ == 0 {
                    v___x_5669_ = v_a_5661_;
                    v_isShared_5670_ = v_isSharedCheck_5691_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_5667_);
                    lean_inc(v_start_5666_);
                    lean_inc(v_array_5665_);
                    lean_dec(v_a_5661_);
                    v___x_5669_ = lean_box(0);
                    v_isShared_5670_ = v_isSharedCheck_5691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5671_ = lean_nat_dec_lt(v_start_5666_, v_stop_5667_);
                if v___x_5671_ == 0 {
                    lean_del_object(v___x_5669_);
                    lean_dec(v_stop_5667_);
                    lean_dec(v_start_5666_);
                    lean_dec_ref(v_array_5665_);
                    v___x_5672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5672_, 0, v_b_5662_);
                    return v___x_5672_;
                } else {
                    v___x_5673_ = lean_array_fget_borrowed(v_array_5665_, v_start_5666_);
                    lean_inc(v___x_5673_);
                    v___x_5674_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_5673_, v___y_5663_);
                    if lean_obj_tag(v___x_5674_) == 0 {
                        v_a_5675_ = lean_ctor_get(v___x_5674_, 0);
                        lean_inc(v_a_5675_);
                        lean_dec_ref_known(v___x_5674_, 1);
                        v___x_5676_ = lean_unsigned_to_nat(1);
                        v___x_5677_ = lean_nat_add(v_start_5666_, v___x_5676_);
                        lean_dec(v_start_5666_);
                        if v_isShared_5670_ == 0 {
                            lean_ctor_set(v___x_5669_, 1, v___x_5677_);
                            v___x_5679_ = v___x_5669_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_array_5665_);
                            lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___x_5677_);
                            lean_ctor_set(v_reuseFailAlloc_5682_, 2, v_stop_5667_);
                            v___x_5679_ = v_reuseFailAlloc_5682_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5669_);
                        lean_dec(v_stop_5667_);
                        lean_dec(v_start_5666_);
                        lean_dec_ref(v_array_5665_);
                        lean_dec_ref(v_b_5662_);
                        v_a_5683_ = lean_ctor_get(v___x_5674_, 0);
                        v_isSharedCheck_5690_ = (!lean_is_exclusive(v___x_5674_)) as u8;
                        if v_isSharedCheck_5690_ == 0 {
                            v___x_5685_ = v___x_5674_;
                            v_isShared_5686_ = v_isSharedCheck_5690_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5683_);
                            lean_dec(v___x_5674_);
                            v___x_5685_ = lean_box(0);
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
                    v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
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
    mut v_a_5692_: *mut LeanObject,
    mut v_b_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5696_: *mut LeanObject = core::ptr::null_mut();
    v_res_5696_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
            v_a_5692_,
            v_b_5693_,
            v___y_5694_,
        );
    lean_dec_ref(v___y_5694_);
    return v_res_5696_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(
    mut v_sz_5697_: usize,
    mut v_i_5698_: usize,
    mut v_bs_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: usize = 0;
    let mut v___x_5710_: usize = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5716_: u8 = 0;
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5702_ = lean_usize_dec_lt(v_i_5698_, v_sz_5697_);
                if v___x_5702_ == 0 {
                    v___x_5703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5703_, 0, v_bs_5699_);
                    return v___x_5703_;
                } else {
                    v_v_5704_ = lean_array_uget_borrowed(v_bs_5699_, v_i_5698_);
                    lean_inc(v_v_5704_);
                    v___x_5705_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_5704_, v___y_5700_);
                    if lean_obj_tag(v___x_5705_) == 0 {
                        v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
                        lean_inc(v_a_5706_);
                        lean_dec_ref_known(v___x_5705_, 1);
                        v___x_5707_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5708_ = lean_array_uset(v_bs_5699_, v_i_5698_, v___x_5707_);
                        v___x_5709_ = 1usize;
                        v___x_5710_ = lean_usize_add(v_i_5698_, v___x_5709_);
                        v___x_5711_ = lean_array_uset(v_bs_x27_5708_, v_i_5698_, v_a_5706_);
                        v_i_5698_ = v___x_5710_;
                        v_bs_5699_ = v___x_5711_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5699_);
                        v_a_5713_ = lean_ctor_get(v___x_5705_, 0);
                        v_isSharedCheck_5720_ = (!lean_is_exclusive(v___x_5705_)) as u8;
                        if v_isSharedCheck_5720_ == 0 {
                            v___x_5715_ = v___x_5705_;
                            v_isShared_5716_ = v_isSharedCheck_5720_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5713_);
                            lean_dec(v___x_5705_);
                            v___x_5715_ = lean_box(0);
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
                    v_reuseFailAlloc_5719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_a_5713_);
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
    mut v_sz_5721_: *mut LeanObject,
    mut v_i_5722_: *mut LeanObject,
    mut v_bs_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5726_: usize = 0;
    let mut v_i_boxed_5727_: usize = 0;
    let mut v_res_5728_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5726_ = lean_unbox_usize(v_sz_5721_);
    lean_dec(v_sz_5721_);
    v_i_boxed_5727_ = lean_unbox_usize(v_i_5722_);
    lean_dec(v_i_5722_);
    v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_5726_, v_i_boxed_5727_, v_bs_5723_, v___y_5724_);
    lean_dec_ref(v___y_5724_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Deriving_mkDiscrs(
    mut v_header_5729_: *mut LeanObject,
    mut v_indVal_5730_: *mut LeanObject,
    mut v_a_5731_: *mut LeanObject,
    mut v_a_5732_: *mut LeanObject,
    mut v_a_5733_: *mut LeanObject,
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
    mut v_a_5736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_argNames_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetNames_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5749_: usize = 0;
    let mut v___x_5750_: usize = 0;
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5755_: u8 = 0;
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_argNames_5738_ = lean_ctor_get(v_header_5729_, 1);
                lean_inc_ref(v_argNames_5738_);
                v_targetNames_5739_ = lean_ctor_get(v_header_5729_, 2);
                lean_inc_ref(v_targetNames_5739_);
                lean_dec_ref(v_header_5729_);
                v_numParams_5740_ = lean_ctor_get(v_indVal_5730_, 1);
                lean_inc(v_numParams_5740_);
                lean_dec_ref(v_indVal_5730_);
                v___x_5741_ = lean_unsigned_to_nat(0);
                v_discrs_5742_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0;
                v___x_5761_ = lean_array_get_size(v_argNames_5738_);
                v___x_5762_ = lean_nat_dec_le(v_numParams_5740_, v___x_5741_);
                if v___x_5762_ == 0 {
                    v_lower_5744_ = v_numParams_5740_;
                    v_upper_5745_ = v___x_5761_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_numParams_5740_);
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
                if lean_obj_tag(v___x_5747_) == 0 {
                    v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
                    lean_inc(v_a_5748_);
                    lean_dec_ref_known(v___x_5747_, 1);
                    v_sz_5749_ = lean_array_size(v_targetNames_5739_);
                    v___x_5750_ = 0usize;
                    v___x_5751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_5749_, v___x_5750_, v_targetNames_5739_, v_a_5735_);
                    if lean_obj_tag(v___x_5751_) == 0 {
                        v_a_5752_ = lean_ctor_get(v___x_5751_, 0);
                        v_isSharedCheck_5760_ = (!lean_is_exclusive(v___x_5751_)) as u8;
                        if v_isSharedCheck_5760_ == 0 {
                            v___x_5754_ = v___x_5751_;
                            v_isShared_5755_ = v_isSharedCheck_5760_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5752_);
                            lean_dec(v___x_5751_);
                            v___x_5754_ = lean_box(0);
                            v_isShared_5755_ = v_isSharedCheck_5760_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5748_);
                        return v___x_5751_;
                    }
                } else {
                    lean_dec_ref(v_targetNames_5739_);
                    return v___x_5747_;
                }
            }
            2 => {
                v___x_5756_ = l_Array_append___redArg(v_a_5748_, v_a_5752_);
                lean_dec(v_a_5752_);
                if v_isShared_5755_ == 0 {
                    lean_ctor_set(v___x_5754_, 0, v___x_5756_);
                    v___x_5758_ = v___x_5754_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
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
    mut v_header_5763_: *mut LeanObject,
    mut v_indVal_5764_: *mut LeanObject,
    mut v_a_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v_a_5767_: *mut LeanObject,
    mut v_a_5768_: *mut LeanObject,
    mut v_a_5769_: *mut LeanObject,
    mut v_a_5770_: *mut LeanObject,
    mut v_a_5771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5772_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5770_);
    lean_dec_ref(v_a_5769_);
    lean_dec(v_a_5768_);
    lean_dec_ref(v_a_5767_);
    lean_dec(v_a_5766_);
    lean_dec_ref(v_a_5765_);
    return v_res_5772_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(
    mut v_inst_5773_: *mut LeanObject,
    mut v_R_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_b_5776_: *mut LeanObject,
    mut v_c_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    v___x_5785_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(
            v_a_5775_,
            v_b_5776_,
            v___y_5782_,
        );
    return v___x_5785_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(
    mut v_inst_5786_: *mut LeanObject,
    mut v_R_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_b_5789_: *mut LeanObject,
    mut v_c_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5798_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5796_);
    lean_dec_ref(v___y_5795_);
    lean_dec(v___y_5794_);
    lean_dec_ref(v___y_5793_);
    lean_dec(v___y_5792_);
    lean_dec_ref(v___y_5791_);
    return v_res_5798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(
    mut v_sz_5799_: usize,
    mut v_i_5800_: usize,
    mut v_bs_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_5799_, v_i_5800_, v_bs_5801_, v___y_5806_);
    return v___x_5809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(
    mut v_sz_5810_: *mut LeanObject,
    mut v_i_5811_: *mut LeanObject,
    mut v_bs_5812_: *mut LeanObject,
    mut v___y_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5820_: usize = 0;
    let mut v_i_boxed_5821_: usize = 0;
    let mut v_res_5822_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5820_ = lean_unbox_usize(v_sz_5810_);
    lean_dec(v_sz_5810_);
    v_i_boxed_5821_ = lean_unbox_usize(v_i_5811_);
    lean_dec(v_i_5811_);
    v_res_5822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_5820_, v_i_boxed_5821_, v_bs_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
    lean_dec(v___y_5818_);
    lean_dec_ref(v___y_5817_);
    lean_dec(v___y_5816_);
    lean_dec_ref(v___y_5815_);
    lean_dec(v___y_5814_);
    lean_dec_ref(v___y_5813_);
    return v_res_5822_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Elab_Deriving_implicitBinderF = _init_l_Lean_Elab_Deriving_implicitBinderF();
    lean_mark_persistent(l_Lean_Elab_Deriving_implicitBinderF);
    l_Lean_Elab_Deriving_instBinderF = _init_l_Lean_Elab_Deriving_instBinderF();
    lean_mark_persistent(l_Lean_Elab_Deriving_instBinderF);
    l_Lean_Elab_Deriving_explicitBinderF = _init_l_Lean_Elab_Deriving_explicitBinderF();
    lean_mark_persistent(l_Lean_Elab_Deriving_explicitBinderF);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Deriving_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclNameGen(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_Util(builtin);
}
