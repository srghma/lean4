// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: Lean.Parser.Module
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{l_Lean_isLetterLike, l_Lean_isSubScriptAlnum};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_str___override};
use crate::r#gen::Init::System::IO::l_IO_FS_readFile;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_mkObj;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Position::{l_Lean_FileMap_toPosition, l_String_toFileMap};
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::Setup::l_Lean_instToJsonModuleHeader_toJson;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_sub, lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::lean_imports_rs::Init::System::IO::lean_get_stdout;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_box_uint32, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_ParseImports_instInhabitedState_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_ParseImports_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ParseImports_instInhabitedState_default___closed__1_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedState_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_ParseImports_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedState_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_ParseImports_instInhabitedState_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedState_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_ParseImports_instInhabitedState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedState_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ParseImports_instInhabitedParser_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ParseImports_skip___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_Lean_ParseImports_instInhabitedParser: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instInhabitedParser_value) as *mut LeanObject;
pub static l_Lean_ParseImports_State_mkEOIError___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32,
            105, 110, 112, 117, 116, 0,
        ],
    };
static mut l_Lean_ParseImports_State_mkEOIError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_State_mkEOIError___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_State_mkEOIError___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_ParseImports_State_mkEOIError___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_ParseImports_State_mkEOIError___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_State_mkEOIError___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 99, 111, 109, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1_value) as *mut LeanObject;
pub static l_Lean_ParseImports_instAndThenParser___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ParseImports_instAndThenParser___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ParseImports_instAndThenParser___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instAndThenParser___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_ParseImports_instAndThenParser: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_instAndThenParser___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_whitespace___closed__0_value: LeanStringObject<66> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 66,
        m_capacity: 66,
        m_length: 65,
        m_data: [
            116, 97, 98, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 97, 108, 108, 111, 119, 101,
            100, 59, 32, 112, 108, 101, 97, 115, 101, 32, 99, 111, 110, 102, 105, 103, 117, 114,
            101, 32, 121, 111, 117, 114, 32, 101, 100, 105, 116, 111, 114, 32, 116, 111, 32, 101,
            120, 112, 97, 110, 100, 32, 116, 104, 101, 109, 0,
        ],
    };
static mut l_Lean_ParseImports_whitespace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_whitespace___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_whitespace___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ParseImports_whitespace___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_ParseImports_whitespace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_whitespace___closed__1_value) as *mut LeanObject;
pub static l_Lean_ParseImports_keyword___lam__0___closed__0_value: LeanStringObject<2> =
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
static mut l_Lean_ParseImports_keyword___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_keyword___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_keyword___lam__0___closed__1_value: LeanStringObject<11> =
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
        m_data: [96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0],
    };
static mut l_Lean_ParseImports_keyword___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_keyword___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 101, 115, 99, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3_value) as *mut LeanObject;
pub static l_Lean_ParseImports_moduleIdent___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ParseImports_moduleIdent___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ParseImports_moduleIdent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_moduleIdent___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___closed__0_value: LeanStringObject<55> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 55,
        m_capacity: 55,
        m_length: 54,
        m_data: [
            99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 39, 112, 117, 98, 108, 105, 99, 39,
            44, 32, 39, 109, 101, 116, 97, 39, 44, 32, 111, 114, 32, 39, 97, 108, 108, 39, 32, 119,
            105, 116, 104, 111, 117, 116, 32, 39, 109, 111, 100, 117, 108, 101, 39, 0,
        ],
    };
static mut l_Lean_ParseImports_manyImports___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_manyImports___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ParseImports_manyImports___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_ParseImports_manyImports___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_manyImports___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 105, 116, 0]};
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__0_value) as *mut LeanObject,1882184448842950296 as *mut LeanObject] };
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 105, 109, 112, 111, 114, 116, 96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0_value
) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1_value
) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2_value
) as *mut LeanObject;
pub static l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 109, 112, 111, 114, 116, 0]};
static mut l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3_value
) as *mut LeanObject;
pub static l_Lean_ParseImports_main___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_ParseImports_main___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_main___closed__0_value) as *mut LeanObject;
pub static l_Lean_ParseImports_main___closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 114, 101, 108, 117, 100, 101, 0],
};
static mut l_Lean_ParseImports_main___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ParseImports_main___closed__1_value) as *mut LeanObject;
pub static l_Lean_parseImports_x27___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_parseImports_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_parseImports_x27___closed__0_value) as *mut LeanObject;
pub static l_Lean_parseImports_x27___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_parseImports_x27___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_parseImports_x27___closed__1_value) as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportResult_toJson___closed__0_value: LeanStringObject<7> =
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
        m_data: [114, 101, 115, 117, 108, 116, 0],
    };
static mut l_Lean_instToJsonPrintImportResult_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportResult_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportResult_toJson___closed__1_value: LeanStringObject<7> =
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
        m_data: [101, 114, 114, 111, 114, 115, 0],
    };
static mut l_Lean_instToJsonPrintImportResult_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportResult_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportResult_toJson___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_instToJsonPrintImportResult_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportResult_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportResult___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonPrintImportResult_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonPrintImportResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportResult___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonPrintImportResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportResult___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value: LeanStringObject<8> =
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
        m_data: [105, 109, 112, 111, 114, 116, 115, 0],
    };
static mut l_Lean_instToJsonPrintImportsResult_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportsResult_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonPrintImportsResult___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonPrintImportsResult_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonPrintImportsResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportsResult___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonPrintImportsResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPrintImportsResult___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_ParseImports_skip___redArg(mut v_s_1760_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_s_1760_);
    return v_s_1760_;
}
pub unsafe fn l_Lean_ParseImports_skip___redArg___boxed(
    mut v_s_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_ParseImports_skip___redArg(v_s_1761_);
    lean_dec_ref(v_s_1761_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_ParseImports_skip(
    mut v_x_1763_: *mut LeanObject,
    mut v_s_1764_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_1764_);
    return v_s_1764_;
}
pub unsafe fn l_Lean_ParseImports_skip___boxed(
    mut v_x_1765_: *mut LeanObject,
    mut v_s_1766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1767_: *mut LeanObject = core::ptr::null_mut();
    v_res_1767_ = l_Lean_ParseImports_skip(v_x_1765_, v_s_1766_);
    lean_dec_ref(v_s_1766_);
    lean_dec_ref(v_x_1765_);
    return v_res_1767_;
}
pub unsafe fn l_Lean_ParseImports_State_setPos(
    mut v_s_1769_: *mut LeanObject,
    mut v_pos_1770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1772_: u8 = 0;
    let mut v_error_x3f_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1774_: u8 = 0;
    let mut v_isMeta_1775_: u8 = 0;
    let mut v_isExported_1776_: u8 = 0;
    let mut v_importAll_1777_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut v_unused_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1771_ = lean_ctor_get(v_s_1769_, 0);
                v_badModifier_1772_ = lean_ctor_get_uint8(
                    v_s_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_1773_ = lean_ctor_get(v_s_1769_, 2);
                v_isModule_1774_ = lean_ctor_get_uint8(
                    v_s_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1775_ = lean_ctor_get_uint8(
                    v_s_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1776_ = lean_ctor_get_uint8(
                    v_s_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1777_ = lean_ctor_get_uint8(
                    v_s_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1784_ = (!lean_is_exclusive(v_s_1769_)) as u8;
                if v_isSharedCheck_1784_ == 0 {
                    v_unused_1785_ = lean_ctor_get(v_s_1769_, 1);
                    lean_dec(v_unused_1785_);
                    v___x_1779_ = v_s_1769_;
                    v_isShared_1780_ = v_isSharedCheck_1784_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_1773_);
                    lean_inc(v_imports_1771_);
                    lean_dec(v_s_1769_);
                    v___x_1779_ = lean_box(0);
                    v_isShared_1780_ = v_isSharedCheck_1784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1780_ == 0 {
                    lean_ctor_set(v___x_1779_, 1, v_pos_1770_);
                    v___x_1782_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_imports_1771_);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_pos_1770_);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_error_x3f_1773_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1783_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1772_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1783_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1774_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1783_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1775_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1783_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1776_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1783_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1777_,
                    );
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_mkError(
    mut v_s_1786_: *mut LeanObject,
    mut v_msg_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1790_: u8 = 0;
    let mut v_isModule_1791_: u8 = 0;
    let mut v_isMeta_1792_: u8 = 0;
    let mut v_isExported_1793_: u8 = 0;
    let mut v_importAll_1794_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v_unused_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1788_ = lean_ctor_get(v_s_1786_, 0);
                v_pos_1789_ = lean_ctor_get(v_s_1786_, 1);
                v_badModifier_1790_ = lean_ctor_get_uint8(
                    v_s_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isModule_1791_ = lean_ctor_get_uint8(
                    v_s_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1792_ = lean_ctor_get_uint8(
                    v_s_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1793_ = lean_ctor_get_uint8(
                    v_s_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1794_ = lean_ctor_get_uint8(
                    v_s_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1802_ = (!lean_is_exclusive(v_s_1786_)) as u8;
                if v_isSharedCheck_1802_ == 0 {
                    v_unused_1803_ = lean_ctor_get(v_s_1786_, 2);
                    lean_dec(v_unused_1803_);
                    v___x_1796_ = v_s_1786_;
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_1789_);
                    lean_inc(v_imports_1788_);
                    lean_dec(v_s_1786_);
                    v___x_1796_ = lean_box(0);
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1798_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1798_, 0, v_msg_1787_);
                if v_isShared_1797_ == 0 {
                    lean_ctor_set(v___x_1796_, 2, v___x_1798_);
                    v___x_1800_ = v___x_1796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_imports_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_pos_1789_);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 2, v___x_1798_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1790_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1791_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1792_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1793_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1794_,
                    );
                    v___x_1800_ = v_reuseFailAlloc_1801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_mkEOIError(
    mut v_s_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1810_: u8 = 0;
    let mut v_isModule_1811_: u8 = 0;
    let mut v_isMeta_1812_: u8 = 0;
    let mut v_isExported_1813_: u8 = 0;
    let mut v_importAll_1814_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_unused_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1808_ = lean_ctor_get(v_s_1807_, 0);
                v_pos_1809_ = lean_ctor_get(v_s_1807_, 1);
                v_badModifier_1810_ = lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isModule_1811_ = lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1812_ = lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1813_ = lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1814_ = lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1822_ = (!lean_is_exclusive(v_s_1807_)) as u8;
                if v_isSharedCheck_1822_ == 0 {
                    v_unused_1823_ = lean_ctor_get(v_s_1807_, 2);
                    lean_dec(v_unused_1823_);
                    v___x_1816_ = v_s_1807_;
                    v_isShared_1817_ = v_isSharedCheck_1822_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_1809_);
                    lean_inc(v_imports_1808_);
                    lean_dec(v_s_1807_);
                    v___x_1816_ = lean_box(0);
                    v_isShared_1817_ = v_isSharedCheck_1822_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1818_ = l_Lean_ParseImports_State_mkEOIError___closed__1;
                if v_isShared_1817_ == 0 {
                    lean_ctor_set(v___x_1816_, 2, v___x_1818_);
                    v___x_1820_ = v___x_1816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_imports_1808_);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_pos_1809_);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 2, v___x_1818_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1821_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1810_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1821_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1811_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1821_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1812_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1821_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1813_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1821_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1814_,
                    );
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_clearError(
    mut v_s_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1827_: u8 = 0;
    let mut v_isMeta_1828_: u8 = 0;
    let mut v_isExported_1829_: u8 = 0;
    let mut v_importAll_1830_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_unused_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1825_ = lean_ctor_get(v_s_1824_, 0);
                v_pos_1826_ = lean_ctor_get(v_s_1824_, 1);
                v_isModule_1827_ = lean_ctor_get_uint8(
                    v_s_1824_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1828_ = lean_ctor_get_uint8(
                    v_s_1824_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1829_ = lean_ctor_get_uint8(
                    v_s_1824_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1830_ = lean_ctor_get_uint8(
                    v_s_1824_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1839_ = (!lean_is_exclusive(v_s_1824_)) as u8;
                if v_isSharedCheck_1839_ == 0 {
                    v_unused_1840_ = lean_ctor_get(v_s_1824_, 2);
                    lean_dec(v_unused_1840_);
                    v___x_1832_ = v_s_1824_;
                    v_isShared_1833_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_1826_);
                    lean_inc(v_imports_1825_);
                    lean_dec(v_s_1824_);
                    v___x_1832_ = lean_box(0);
                    v_isShared_1833_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1834_ = 0;
                v___x_1835_ = lean_box(0);
                if v_isShared_1833_ == 0 {
                    lean_ctor_set(v___x_1832_, 2, v___x_1835_);
                    v___x_1837_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_imports_1825_);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_pos_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1838_, 2, v___x_1835_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1838_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1827_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1838_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1828_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1838_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1829_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1838_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1830_,
                    );
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1837_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1834_,
                );
                return v___x_1837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_next(
    mut v_s_1841_: *mut LeanObject,
    mut v_input_1842_: *mut LeanObject,
    mut v_pos_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1845_: u8 = 0;
    let mut v_error_x3f_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1847_: u8 = 0;
    let mut v_isMeta_1848_: u8 = 0;
    let mut v_isExported_1849_: u8 = 0;
    let mut v_importAll_1850_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_unused_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1844_ = lean_ctor_get(v_s_1841_, 0);
                v_badModifier_1845_ = lean_ctor_get_uint8(
                    v_s_1841_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_1846_ = lean_ctor_get(v_s_1841_, 2);
                v_isModule_1847_ = lean_ctor_get_uint8(
                    v_s_1841_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1848_ = lean_ctor_get_uint8(
                    v_s_1841_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1849_ = lean_ctor_get_uint8(
                    v_s_1841_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1850_ = lean_ctor_get_uint8(
                    v_s_1841_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1858_ = (!lean_is_exclusive(v_s_1841_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v_unused_1859_ = lean_ctor_get(v_s_1841_, 1);
                    lean_dec(v_unused_1859_);
                    v___x_1852_ = v_s_1841_;
                    v_isShared_1853_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_1846_);
                    lean_inc(v_imports_1844_);
                    lean_dec(v_s_1841_);
                    v___x_1852_ = lean_box(0);
                    v_isShared_1853_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1854_ = lean_string_utf8_next(v_input_1842_, v_pos_1843_);
                if v_isShared_1853_ == 0 {
                    lean_ctor_set(v___x_1852_, 1, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_imports_1844_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_error_x3f_1846_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1845_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1847_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1848_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1849_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1850_,
                    );
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_next___boxed(
    mut v_s_1860_: *mut LeanObject,
    mut v_input_1861_: *mut LeanObject,
    mut v_pos_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1863_: *mut LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Lean_ParseImports_State_next(v_s_1860_, v_input_1861_, v_pos_1862_);
    lean_dec(v_pos_1862_);
    lean_dec_ref(v_input_1861_);
    return v_res_1863_;
}
pub unsafe fn l_Lean_ParseImports_State_next_x27___redArg(
    mut v_s_1864_: *mut LeanObject,
    mut v_input_1865_: *mut LeanObject,
    mut v_pos_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1868_: u8 = 0;
    let mut v_error_x3f_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1870_: u8 = 0;
    let mut v_isMeta_1871_: u8 = 0;
    let mut v_isExported_1872_: u8 = 0;
    let mut v_importAll_1873_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_unused_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1867_ = lean_ctor_get(v_s_1864_, 0);
                v_badModifier_1868_ = lean_ctor_get_uint8(
                    v_s_1864_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_1869_ = lean_ctor_get(v_s_1864_, 2);
                v_isModule_1870_ = lean_ctor_get_uint8(
                    v_s_1864_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1871_ = lean_ctor_get_uint8(
                    v_s_1864_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1872_ = lean_ctor_get_uint8(
                    v_s_1864_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1873_ = lean_ctor_get_uint8(
                    v_s_1864_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1881_ = (!lean_is_exclusive(v_s_1864_)) as u8;
                if v_isSharedCheck_1881_ == 0 {
                    v_unused_1882_ = lean_ctor_get(v_s_1864_, 1);
                    lean_dec(v_unused_1882_);
                    v___x_1875_ = v_s_1864_;
                    v_isShared_1876_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_1869_);
                    lean_inc(v_imports_1867_);
                    lean_dec(v_s_1864_);
                    v___x_1875_ = lean_box(0);
                    v_isShared_1876_ = v_isSharedCheck_1881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1877_ = lean_string_utf8_next_fast(v_input_1865_, v_pos_1866_);
                if v_isShared_1876_ == 0 {
                    lean_ctor_set(v___x_1875_, 1, v___x_1877_);
                    v___x_1879_ = v___x_1875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_imports_1867_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
                    lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_error_x3f_1869_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1868_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1870_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1871_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1872_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1880_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1873_,
                    );
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_next_x27___redArg___boxed(
    mut v_s_1883_: *mut LeanObject,
    mut v_input_1884_: *mut LeanObject,
    mut v_pos_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1886_ =
        l_Lean_ParseImports_State_next_x27___redArg(v_s_1883_, v_input_1884_, v_pos_1885_);
    lean_dec(v_pos_1885_);
    lean_dec_ref(v_input_1884_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_ParseImports_State_next_x27(
    mut v_s_1887_: *mut LeanObject,
    mut v_input_1888_: *mut LeanObject,
    mut v_pos_1889_: *mut LeanObject,
    mut v_h_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1892_: u8 = 0;
    let mut v_error_x3f_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1894_: u8 = 0;
    let mut v_isMeta_1895_: u8 = 0;
    let mut v_isExported_1896_: u8 = 0;
    let mut v_importAll_1897_: u8 = 0;
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_unused_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1891_ = lean_ctor_get(v_s_1887_, 0);
                v_badModifier_1892_ = lean_ctor_get_uint8(
                    v_s_1887_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_1893_ = lean_ctor_get(v_s_1887_, 2);
                v_isModule_1894_ = lean_ctor_get_uint8(
                    v_s_1887_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1895_ = lean_ctor_get_uint8(
                    v_s_1887_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1896_ = lean_ctor_get_uint8(
                    v_s_1887_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1897_ = lean_ctor_get_uint8(
                    v_s_1887_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1905_ = (!lean_is_exclusive(v_s_1887_)) as u8;
                if v_isSharedCheck_1905_ == 0 {
                    v_unused_1906_ = lean_ctor_get(v_s_1887_, 1);
                    lean_dec(v_unused_1906_);
                    v___x_1899_ = v_s_1887_;
                    v_isShared_1900_ = v_isSharedCheck_1905_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_1893_);
                    lean_inc(v_imports_1891_);
                    lean_dec(v_s_1887_);
                    v___x_1899_ = lean_box(0);
                    v_isShared_1900_ = v_isSharedCheck_1905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1901_ = lean_string_utf8_next_fast(v_input_1888_, v_pos_1889_);
                if v_isShared_1900_ == 0 {
                    lean_ctor_set(v___x_1899_, 1, v___x_1901_);
                    v___x_1903_ = v___x_1899_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_imports_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_error_x3f_1893_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1892_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1894_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1895_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1896_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1897_,
                    );
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_State_next_x27___boxed(
    mut v_s_1907_: *mut LeanObject,
    mut v_input_1908_: *mut LeanObject,
    mut v_pos_1909_: *mut LeanObject,
    mut v_h_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1911_: *mut LeanObject = core::ptr::null_mut();
    v_res_1911_ =
        l_Lean_ParseImports_State_next_x27(v_s_1907_, v_input_1908_, v_pos_1909_, v_h_1910_);
    lean_dec(v_pos_1909_);
    lean_dec_ref(v_input_1908_);
    return v_res_1911_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(
    mut v_s_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1918_: u8 = 0;
    let mut v_isModule_1919_: u8 = 0;
    let mut v_isMeta_1920_: u8 = 0;
    let mut v_isExported_1921_: u8 = 0;
    let mut v_importAll_1922_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_unused_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1916_ = lean_ctor_get(v_s_1915_, 0);
                v_pos_1917_ = lean_ctor_get(v_s_1915_, 1);
                v_badModifier_1918_ = lean_ctor_get_uint8(
                    v_s_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isModule_1919_ = lean_ctor_get_uint8(
                    v_s_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1920_ = lean_ctor_get_uint8(
                    v_s_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1921_ = lean_ctor_get_uint8(
                    v_s_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1922_ = lean_ctor_get_uint8(
                    v_s_1915_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_1930_ = (!lean_is_exclusive(v_s_1915_)) as u8;
                if v_isSharedCheck_1930_ == 0 {
                    v_unused_1931_ = lean_ctor_get(v_s_1915_, 2);
                    lean_dec(v_unused_1931_);
                    v___x_1924_ = v_s_1915_;
                    v_isShared_1925_ = v_isSharedCheck_1930_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_1917_);
                    lean_inc(v_imports_1916_);
                    lean_dec(v_s_1915_);
                    v___x_1924_ = lean_box(0);
                    v_isShared_1925_ = v_isSharedCheck_1930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1926_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi___closed__1;
                if v_isShared_1925_ == 0 {
                    lean_ctor_set(v___x_1924_, 2, v___x_1926_);
                    v___x_1928_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_imports_1916_);
                    lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_pos_1917_);
                    lean_ctor_set(v_reuseFailAlloc_1929_, 2, v___x_1926_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1929_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1918_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1929_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1919_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1929_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1920_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1929_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1921_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1929_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1922_,
                    );
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_finishCommentBlock(
    mut v_nesting_1932_: *mut LeanObject,
    mut v_input_1933_: *mut LeanObject,
    mut v_s_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_1937_: u8 = 0;
    let mut v_error_x3f_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1939_: u8 = 0;
    let mut v_isMeta_1940_: u8 = 0;
    let mut v_isExported_1941_: u8 = 0;
    let mut v_importAll_1942_: u8 = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v_curr_1944_: u32 = 0;
    let mut v_i_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u32 = 0;
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: u32 = 0;
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_unused_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v_curr_1965_: u32 = 0;
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_unused_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v_curr_1987_: u32 = 0;
    let mut v___x_1988_: u32 = 0;
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_unused_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_1935_ = lean_ctor_get(v_s_1934_, 0);
                v_pos_1936_ = lean_ctor_get(v_s_1934_, 1);
                v_badModifier_1937_ = lean_ctor_get_uint8(
                    v_s_1934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_1938_ = lean_ctor_get(v_s_1934_, 2);
                v_isModule_1939_ = lean_ctor_get_uint8(
                    v_s_1934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_1940_ = lean_ctor_get_uint8(
                    v_s_1934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_1941_ = lean_ctor_get_uint8(
                    v_s_1934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_1942_ = lean_ctor_get_uint8(
                    v_s_1934_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_1943_ = lean_string_utf8_at_end(v_input_1933_, v_pos_1936_);
                if v___x_1943_ == 0 {
                    v_curr_1944_ = lean_string_utf8_get_fast(v_input_1933_, v_pos_1936_);
                    v_i_1945_ = lean_string_utf8_next_fast(v_input_1933_, v_pos_1936_);
                    v___x_1946_ = 45;
                    v___x_1947_ = lean_uint32_dec_eq(v_curr_1944_, v___x_1946_);
                    if v___x_1947_ == 0 {
                        v___x_1948_ = 47;
                        v___x_1949_ = lean_uint32_dec_eq(v_curr_1944_, v___x_1948_);
                        if v___x_1949_ == 0 {
                            lean_inc(v_error_x3f_1938_);
                            lean_inc_ref(v_imports_1935_);
                            v_isSharedCheck_1957_ = (!lean_is_exclusive(v_s_1934_)) as u8;
                            if v_isSharedCheck_1957_ == 0 {
                                v_unused_1958_ = lean_ctor_get(v_s_1934_, 2);
                                lean_dec(v_unused_1958_);
                                v_unused_1959_ = lean_ctor_get(v_s_1934_, 1);
                                lean_dec(v_unused_1959_);
                                v_unused_1960_ = lean_ctor_get(v_s_1934_, 0);
                                lean_dec(v_unused_1960_);
                                v___x_1951_ = v_s_1934_;
                                v_isShared_1952_ = v_isSharedCheck_1957_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_s_1934_);
                                v___x_1951_ = lean_box(0);
                                v_isShared_1952_ = v_isSharedCheck_1957_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1961_ = lean_string_utf8_at_end(v_input_1933_, v_i_1945_);
                            if v___x_1961_ == 0 {
                                lean_inc(v_error_x3f_1938_);
                                lean_inc_ref(v_imports_1935_);
                                v_isSharedCheck_1978_ = (!lean_is_exclusive(v_s_1934_)) as u8;
                                if v_isSharedCheck_1978_ == 0 {
                                    v_unused_1979_ = lean_ctor_get(v_s_1934_, 2);
                                    lean_dec(v_unused_1979_);
                                    v_unused_1980_ = lean_ctor_get(v_s_1934_, 1);
                                    lean_dec(v_unused_1980_);
                                    v_unused_1981_ = lean_ctor_get(v_s_1934_, 0);
                                    lean_dec(v_unused_1981_);
                                    v___x_1963_ = v_s_1934_;
                                    v_isShared_1964_ = v_isSharedCheck_1978_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_s_1934_);
                                    v___x_1963_ = lean_box(0);
                                    v_isShared_1964_ = v_isSharedCheck_1978_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_nesting_1932_);
                                v___x_1982_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_1934_);
                                return v___x_1982_;
                            }
                        }
                    } else {
                        v___x_1983_ = lean_string_utf8_at_end(v_input_1933_, v_i_1945_);
                        if v___x_1983_ == 0 {
                            lean_inc(v_error_x3f_1938_);
                            lean_inc_ref(v_imports_1935_);
                            v_isSharedCheck_2007_ = (!lean_is_exclusive(v_s_1934_)) as u8;
                            if v_isSharedCheck_2007_ == 0 {
                                v_unused_2008_ = lean_ctor_get(v_s_1934_, 2);
                                lean_dec(v_unused_2008_);
                                v_unused_2009_ = lean_ctor_get(v_s_1934_, 1);
                                lean_dec(v_unused_2009_);
                                v_unused_2010_ = lean_ctor_get(v_s_1934_, 0);
                                lean_dec(v_unused_2010_);
                                v___x_1985_ = v_s_1934_;
                                v_isShared_1986_ = v_isSharedCheck_2007_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v_s_1934_);
                                v___x_1985_ = lean_box(0);
                                v_isShared_1986_ = v_isSharedCheck_2007_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_nesting_1932_);
                            v___x_2011_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_1934_);
                            return v___x_2011_;
                        }
                    }
                } else {
                    lean_dec(v_nesting_1932_);
                    v___x_2012_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_finishCommentBlock_eoi(v_s_1934_);
                    return v___x_2012_;
                }
            }
            1 => {
                if v_isShared_1952_ == 0 {
                    lean_ctor_set(v___x_1951_, 1, v_i_1945_);
                    v___x_1954_ = v___x_1951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_imports_1935_);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_i_1945_);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_error_x3f_1938_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1956_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_1937_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1956_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_1939_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1956_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_1940_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1956_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_1941_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1956_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_1942_,
                    );
                    v___x_1954_ = v_reuseFailAlloc_1956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s_1934_ = v___x_1954_;
                state = 0;
                continue;
            }
            3 => {
                v_curr_1965_ = lean_string_utf8_get_fast(v_input_1933_, v_i_1945_);
                v___x_1966_ = lean_uint32_dec_eq(v_curr_1965_, v___x_1946_);
                if v___x_1966_ == 0 {
                    if v_isShared_1964_ == 0 {
                        lean_ctor_set(v___x_1963_, 1, v_i_1945_);
                        v___x_1968_ = v___x_1963_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_imports_1935_);
                        lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_i_1945_);
                        lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_error_x3f_1938_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1970_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_1937_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1970_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_1939_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1970_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_1940_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1970_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_1941_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1970_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_1942_,
                        );
                        v___x_1968_ = v_reuseFailAlloc_1970_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1971_ = lean_unsigned_to_nat(1);
                    v___x_1972_ = lean_nat_add(v_nesting_1932_, v___x_1971_);
                    lean_dec(v_nesting_1932_);
                    v___x_1973_ = lean_string_utf8_next_fast(v_input_1933_, v_i_1945_);
                    if v_isShared_1964_ == 0 {
                        lean_ctor_set(v___x_1963_, 1, v___x_1973_);
                        v___x_1975_ = v___x_1963_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_imports_1935_);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1973_);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_error_x3f_1938_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1977_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_1937_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1977_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_1939_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1977_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_1940_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1977_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_1941_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1977_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_1942_,
                        );
                        v___x_1975_ = v_reuseFailAlloc_1977_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_s_1934_ = v___x_1968_;
                state = 0;
                continue;
            }
            5 => {
                v_nesting_1932_ = v___x_1972_;
                v_s_1934_ = v___x_1975_;
                state = 0;
                continue;
            }
            6 => {
                v_curr_1987_ = lean_string_utf8_get_fast(v_input_1933_, v_i_1945_);
                v___x_1988_ = 47;
                v___x_1989_ = lean_uint32_dec_eq(v_curr_1987_, v___x_1988_);
                if v___x_1989_ == 0 {
                    v___x_1990_ = lean_string_utf8_next_fast(v_input_1933_, v_i_1945_);
                    if v_isShared_1986_ == 0 {
                        lean_ctor_set(v___x_1985_, 1, v___x_1990_);
                        v___x_1992_ = v___x_1985_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_imports_1935_);
                        lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1990_);
                        lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_error_x3f_1938_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1994_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_1937_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1994_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_1939_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1994_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_1940_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1994_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_1941_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1994_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_1942_,
                        );
                        v___x_1992_ = v_reuseFailAlloc_1994_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_1995_ = lean_unsigned_to_nat(1);
                    v___x_1996_ = lean_nat_dec_eq(v_nesting_1932_, v___x_1995_);
                    if v___x_1996_ == 0 {
                        v___x_1997_ = lean_nat_sub(v_nesting_1932_, v___x_1995_);
                        lean_dec(v_nesting_1932_);
                        v___x_1998_ = lean_string_utf8_next_fast(v_input_1933_, v_i_1945_);
                        if v_isShared_1986_ == 0 {
                            lean_ctor_set(v___x_1985_, 1, v___x_1998_);
                            v___x_2000_ = v___x_1985_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 3, (5) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_imports_1935_);
                            lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1998_);
                            lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_error_x3f_1938_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2002_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v_badModifier_1937_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2002_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                                v_isModule_1939_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2002_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                                v_isMeta_1940_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2002_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                                v_isExported_1941_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2002_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                                v_importAll_1942_,
                            );
                            v___x_2000_ = v_reuseFailAlloc_2002_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_nesting_1932_);
                        v___x_2003_ = lean_string_utf8_next(v_input_1933_, v_i_1945_);
                        if v_isShared_1986_ == 0 {
                            lean_ctor_set(v___x_1985_, 1, v___x_2003_);
                            v___x_2005_ = v___x_1985_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 3, (5) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_imports_1935_);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_2003_);
                            lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_error_x3f_1938_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2006_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v_badModifier_1937_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2006_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                                v_isModule_1939_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2006_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                                v_isMeta_1940_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2006_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                                v_isExported_1941_,
                            );
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_2006_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                                v_importAll_1942_,
                            );
                            v___x_2005_ = v_reuseFailAlloc_2006_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v_s_1934_ = v___x_1992_;
                state = 0;
                continue;
            }
            8 => {
                v_nesting_1932_ = v___x_1997_;
                v_s_1934_ = v___x_2000_;
                state = 0;
                continue;
            }
            9 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_finishCommentBlock___boxed(
    mut v_nesting_2013_: *mut LeanObject,
    mut v_input_2014_: *mut LeanObject,
    mut v_s_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2016_: *mut LeanObject = core::ptr::null_mut();
    v_res_2016_ = l_Lean_ParseImports_finishCommentBlock(v_nesting_2013_, v_input_2014_, v_s_2015_);
    lean_dec_ref(v_input_2014_);
    return v_res_2016_;
}
pub unsafe fn l_Lean_ParseImports_takeUntil(
    mut v_p_2017_: *mut LeanObject,
    mut v_input_2018_: *mut LeanObject,
    mut v_s_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2022_: u8 = 0;
    let mut v_error_x3f_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2024_: u8 = 0;
    let mut v_isMeta_2025_: u8 = 0;
    let mut v_isExported_2026_: u8 = 0;
    let mut v_importAll_2027_: u8 = 0;
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: u32 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_unused_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2020_ = lean_ctor_get(v_s_2019_, 0);
                v_pos_2021_ = lean_ctor_get(v_s_2019_, 1);
                v_badModifier_2022_ = lean_ctor_get_uint8(
                    v_s_2019_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2023_ = lean_ctor_get(v_s_2019_, 2);
                v_isModule_2024_ = lean_ctor_get_uint8(
                    v_s_2019_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2025_ = lean_ctor_get_uint8(
                    v_s_2019_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2026_ = lean_ctor_get_uint8(
                    v_s_2019_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2027_ = lean_ctor_get_uint8(
                    v_s_2019_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2028_ = lean_string_utf8_at_end(v_input_2018_, v_pos_2021_);
                if v___x_2028_ == 0 {
                    v___x_2029_ = lean_string_utf8_get_fast(v_input_2018_, v_pos_2021_);
                    v___x_2030_ = lean_box_uint32(v___x_2029_);
                    lean_inc_ref(v_p_2017_);
                    v___x_2031_ = lean_apply_1(v_p_2017_, v___x_2030_);
                    v___x_2032_ = (lean_unbox(v___x_2031_) as u8);
                    if v___x_2032_ == 0 {
                        lean_inc(v_error_x3f_2023_);
                        lean_inc(v_pos_2021_);
                        lean_inc_ref(v_imports_2020_);
                        v_isSharedCheck_2041_ = (!lean_is_exclusive(v_s_2019_)) as u8;
                        if v_isSharedCheck_2041_ == 0 {
                            v_unused_2042_ = lean_ctor_get(v_s_2019_, 2);
                            lean_dec(v_unused_2042_);
                            v_unused_2043_ = lean_ctor_get(v_s_2019_, 1);
                            lean_dec(v_unused_2043_);
                            v_unused_2044_ = lean_ctor_get(v_s_2019_, 0);
                            lean_dec(v_unused_2044_);
                            v___x_2034_ = v_s_2019_;
                            v_isShared_2035_ = v_isSharedCheck_2041_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2019_);
                            v___x_2034_ = lean_box(0);
                            v_isShared_2035_ = v_isSharedCheck_2041_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_p_2017_);
                        return v_s_2019_;
                    }
                } else {
                    lean_dec_ref(v_p_2017_);
                    return v_s_2019_;
                }
            }
            1 => {
                v___x_2036_ = lean_string_utf8_next_fast(v_input_2018_, v_pos_2021_);
                lean_dec(v_pos_2021_);
                if v_isShared_2035_ == 0 {
                    lean_ctor_set(v___x_2034_, 1, v___x_2036_);
                    v___x_2038_ = v___x_2034_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_imports_2020_);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2036_);
                    lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_error_x3f_2023_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2022_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2024_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2025_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2026_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2040_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2027_,
                    );
                    v___x_2038_ = v_reuseFailAlloc_2040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s_2019_ = v___x_2038_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_takeUntil___boxed(
    mut v_p_2045_: *mut LeanObject,
    mut v_input_2046_: *mut LeanObject,
    mut v_s_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2048_: *mut LeanObject = core::ptr::null_mut();
    v_res_2048_ = l_Lean_ParseImports_takeUntil(v_p_2045_, v_input_2046_, v_s_2047_);
    lean_dec_ref(v_input_2046_);
    return v_res_2048_;
}
pub unsafe fn l_Lean_ParseImports_takeWhile___lam__0(
    mut v_p_2049_: *mut LeanObject,
    mut v_c_2050_: u32,
) -> u8 {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    v___x_2051_ = lean_box_uint32(v_c_2050_);
    v___x_2052_ = lean_apply_1(v_p_2049_, v___x_2051_);
    v___x_2053_ = (lean_unbox(v___x_2052_) as u8);
    if v___x_2053_ == 0 {
        let mut v___x_2054_: u8 = 0;
        v___x_2054_ = 1;
        return v___x_2054_;
    } else {
        let mut v___x_2055_: u8 = 0;
        v___x_2055_ = 0;
        return v___x_2055_;
    }
}
pub unsafe fn l_Lean_ParseImports_takeWhile___lam__0___boxed(
    mut v_p_2056_: *mut LeanObject,
    mut v_c_2057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2058_: u32 = 0;
    let mut v_res_2059_: u8 = 0;
    let mut v_r_2060_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2058_ = lean_unbox_uint32(v_c_2057_);
    lean_dec(v_c_2057_);
    v_res_2059_ = l_Lean_ParseImports_takeWhile___lam__0(v_p_2056_, v_c_boxed_2058_);
    v_r_2060_ = lean_box((v_res_2059_) as usize);
    return v_r_2060_;
}
pub unsafe fn l_Lean_ParseImports_takeWhile(
    mut v_p_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___f_2064_ = lean_alloc_closure(
        l_Lean_ParseImports_takeWhile___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2064_, 0, v_p_2061_);
    v___x_2065_ = l_Lean_ParseImports_takeUntil(v___f_2064_, v_a_2062_, v_a_2063_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_ParseImports_takeWhile___boxed(
    mut v_p_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_ParseImports_takeWhile(v_p_2066_, v_a_2067_, v_a_2068_);
    lean_dec_ref(v_a_2067_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_ParseImports_andthen(
    mut v_p_2070_: *mut LeanObject,
    mut v_q_2071_: *mut LeanObject,
    mut v_input_2072_: *mut LeanObject,
    mut v_s_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2075_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_input_2072_);
    v_s_2074_ = lean_apply_2(v_p_2070_, v_input_2072_, v_s_2073_);
    v_error_x3f_2075_ = lean_ctor_get(v_s_2074_, 2);
    lean_inc(v_error_x3f_2075_);
    if lean_obj_tag(v_error_x3f_2075_) == 1 {
        lean_dec_ref_known(v_error_x3f_2075_, 1);
        lean_dec_ref(v_input_2072_);
        lean_dec_ref(v_q_2071_);
        return v_s_2074_;
    } else {
        let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_error_x3f_2075_);
        v___x_2076_ = lean_apply_2(v_q_2071_, v_input_2072_, v_s_2074_);
        return v___x_2076_;
    }
}
pub unsafe fn l_Lean_ParseImports_instAndThenParser___lam__0(
    mut v_p_2077_: *mut LeanObject,
    mut v_q_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2082_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_2079_);
    v_s_2081_ = lean_apply_2(v_p_2077_, v___y_2079_, v___y_2080_);
    v_error_x3f_2082_ = lean_ctor_get(v_s_2081_, 2);
    lean_inc(v_error_x3f_2082_);
    if lean_obj_tag(v_error_x3f_2082_) == 1 {
        lean_dec_ref_known(v_error_x3f_2082_, 1);
        lean_dec_ref(v___y_2079_);
        lean_dec_ref(v_q_2078_);
        return v_s_2081_;
    } else {
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_error_x3f_2082_);
        v___x_2083_ = lean_box(0);
        v___x_2084_ = lean_apply_3(v_q_2078_, v___x_2083_, v___y_2079_, v_s_2081_);
        return v___x_2084_;
    }
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(
    mut v_input_2087_: *mut LeanObject,
    mut v_s_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2091_: u8 = 0;
    let mut v_error_x3f_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2093_: u8 = 0;
    let mut v_isMeta_2094_: u8 = 0;
    let mut v_isExported_2095_: u8 = 0;
    let mut v_importAll_2096_: u8 = 0;
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: u32 = 0;
    let mut v___x_2099_: u32 = 0;
    let mut v___x_2100_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2089_ = lean_ctor_get(v_s_2088_, 0);
                v_pos_2090_ = lean_ctor_get(v_s_2088_, 1);
                v_badModifier_2091_ = lean_ctor_get_uint8(
                    v_s_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2092_ = lean_ctor_get(v_s_2088_, 2);
                v_isModule_2093_ = lean_ctor_get_uint8(
                    v_s_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2094_ = lean_ctor_get_uint8(
                    v_s_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2095_ = lean_ctor_get_uint8(
                    v_s_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2096_ = lean_ctor_get_uint8(
                    v_s_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2097_ = lean_string_utf8_at_end(v_input_2087_, v_pos_2090_);
                if v___x_2097_ == 0 {
                    v___x_2098_ = lean_string_utf8_get_fast(v_input_2087_, v_pos_2090_);
                    v___x_2099_ = 10;
                    v___x_2100_ = lean_uint32_dec_eq(v___x_2098_, v___x_2099_);
                    if v___x_2100_ == 0 {
                        lean_inc(v_error_x3f_2092_);
                        lean_inc(v_pos_2090_);
                        lean_inc_ref(v_imports_2089_);
                        v_isSharedCheck_2109_ = (!lean_is_exclusive(v_s_2088_)) as u8;
                        if v_isSharedCheck_2109_ == 0 {
                            v_unused_2110_ = lean_ctor_get(v_s_2088_, 2);
                            lean_dec(v_unused_2110_);
                            v_unused_2111_ = lean_ctor_get(v_s_2088_, 1);
                            lean_dec(v_unused_2111_);
                            v_unused_2112_ = lean_ctor_get(v_s_2088_, 0);
                            lean_dec(v_unused_2112_);
                            v___x_2102_ = v_s_2088_;
                            v_isShared_2103_ = v_isSharedCheck_2109_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2088_);
                            v___x_2102_ = lean_box(0);
                            v_isShared_2103_ = v_isSharedCheck_2109_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_s_2088_;
                    }
                } else {
                    return v_s_2088_;
                }
            }
            1 => {
                v___x_2104_ = lean_string_utf8_next_fast(v_input_2087_, v_pos_2090_);
                lean_dec(v_pos_2090_);
                if v_isShared_2103_ == 0 {
                    lean_ctor_set(v___x_2102_, 1, v___x_2104_);
                    v___x_2106_ = v___x_2102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_imports_2089_);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_error_x3f_2092_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2091_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2093_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2094_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2095_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2096_,
                    );
                    v___x_2106_ = v_reuseFailAlloc_2108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s_2088_ = v___x_2106_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0___boxed(
    mut v_input_2113_: *mut LeanObject,
    mut v_s_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2115_: *mut LeanObject = core::ptr::null_mut();
    v_res_2115_ = l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(
        v_input_2113_,
        v_s_2114_,
    );
    lean_dec_ref(v_input_2113_);
    return v_res_2115_;
}
pub unsafe fn l_Lean_ParseImports_whitespace(
    mut v_input_2119_: *mut LeanObject,
    mut v_s_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2123_: u8 = 0;
    let mut v_error_x3f_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2125_: u8 = 0;
    let mut v_isMeta_2126_: u8 = 0;
    let mut v_isExported_2127_: u8 = 0;
    let mut v_importAll_2128_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: u8 = 0;
    let mut v_curr_2134_: u32 = 0;
    let mut v___y_2136_: u8 = 0;
    let mut v___x_2137_: u32 = 0;
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: u32 = 0;
    let mut v___x_2140_: u8 = 0;
    let mut v_i_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2142_: u32 = 0;
    let mut v___x_2143_: u8 = 0;
    let mut v_i_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2145_: u32 = 0;
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: u32 = 0;
    let mut v___x_2148_: u8 = 0;
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_unused_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2165_: u32 = 0;
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v_unused_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: u8 = 0;
    let mut v___x_2183_: u32 = 0;
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2185_: u32 = 0;
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: u32 = 0;
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: u32 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v_unused_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2121_ = lean_ctor_get(v_s_2120_, 0);
                v_pos_2122_ = lean_ctor_get(v_s_2120_, 1);
                v_badModifier_2123_ = lean_ctor_get_uint8(
                    v_s_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2124_ = lean_ctor_get(v_s_2120_, 2);
                v_isModule_2125_ = lean_ctor_get_uint8(
                    v_s_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2126_ = lean_ctor_get_uint8(
                    v_s_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2127_ = lean_ctor_get_uint8(
                    v_s_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2128_ = lean_ctor_get_uint8(
                    v_s_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2133_ = lean_string_utf8_at_end(v_input_2119_, v_pos_2122_);
                if v___x_2133_ == 0 {
                    v_curr_2134_ = lean_string_utf8_get_fast(v_input_2119_, v_pos_2122_);
                    v___x_2187_ = 9;
                    v___x_2188_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2187_);
                    if v___x_2188_ == 0 {
                        v___x_2189_ = 32;
                        v___x_2190_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2189_);
                        if v___x_2190_ == 0 {
                            v___y_2182_ = v___x_2188_;
                            state = 7;
                            continue;
                        } else {
                            v___y_2182_ = v___x_2190_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_inc(v_pos_2122_);
                        lean_inc_ref(v_imports_2121_);
                        v_isSharedCheck_2198_ = (!lean_is_exclusive(v_s_2120_)) as u8;
                        if v_isSharedCheck_2198_ == 0 {
                            v_unused_2199_ = lean_ctor_get(v_s_2120_, 2);
                            lean_dec(v_unused_2199_);
                            v_unused_2200_ = lean_ctor_get(v_s_2120_, 1);
                            lean_dec(v_unused_2200_);
                            v_unused_2201_ = lean_ctor_get(v_s_2120_, 0);
                            lean_dec(v_unused_2201_);
                            v___x_2192_ = v_s_2120_;
                            v_isShared_2193_ = v_isSharedCheck_2198_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v_s_2120_);
                            v___x_2192_ = lean_box(0);
                            v_isShared_2193_ = v_isSharedCheck_2198_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    return v_s_2120_;
                }
            }
            1 => {
                v___x_2130_ = lean_string_utf8_next(v_input_2119_, v_pos_2122_);
                lean_dec(v_pos_2122_);
                v___x_2131_ = lean_alloc_ctor(0, 3, (5) as u32);
                lean_ctor_set(v___x_2131_, 0, v_imports_2121_);
                lean_ctor_set(v___x_2131_, 1, v___x_2130_);
                lean_ctor_set(v___x_2131_, 2, v_error_x3f_2124_);
                lean_ctor_set_uint8(
                    v___x_2131_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_badModifier_2123_,
                );
                lean_ctor_set_uint8(
                    v___x_2131_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_isModule_2125_,
                );
                lean_ctor_set_uint8(
                    v___x_2131_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v_isMeta_2126_,
                );
                lean_ctor_set_uint8(
                    v___x_2131_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v_isExported_2127_,
                );
                lean_ctor_set_uint8(
                    v___x_2131_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    v_importAll_2128_,
                );
                v_s_2120_ = v___x_2131_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2136_ == 0 {
                    v___x_2137_ = 45;
                    v___x_2138_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2137_);
                    if v___x_2138_ == 0 {
                        v___x_2139_ = 47;
                        v___x_2140_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2139_);
                        if v___x_2140_ == 0 {
                            return v_s_2120_;
                        } else {
                            v_i_2141_ = lean_string_utf8_next_fast(v_input_2119_, v_pos_2122_);
                            v_curr_2142_ = lean_string_utf8_get(v_input_2119_, v_i_2141_);
                            v___x_2143_ = lean_uint32_dec_eq(v_curr_2142_, v___x_2137_);
                            if v___x_2143_ == 0 {
                                return v_s_2120_;
                            } else {
                                v_i_2144_ = lean_string_utf8_next(v_input_2119_, v_i_2141_);
                                v_curr_2145_ = lean_string_utf8_get(v_input_2119_, v_i_2144_);
                                v___x_2146_ = lean_uint32_dec_eq(v_curr_2145_, v___x_2137_);
                                if v___x_2146_ == 0 {
                                    v___x_2147_ = 33;
                                    v___x_2148_ = lean_uint32_dec_eq(v_curr_2145_, v___x_2147_);
                                    if v___x_2148_ == 0 {
                                        lean_inc(v_error_x3f_2124_);
                                        lean_inc_ref(v_imports_2121_);
                                        v_isSharedCheck_2160_ =
                                            (!lean_is_exclusive(v_s_2120_)) as u8;
                                        if v_isSharedCheck_2160_ == 0 {
                                            v_unused_2161_ = lean_ctor_get(v_s_2120_, 2);
                                            lean_dec(v_unused_2161_);
                                            v_unused_2162_ = lean_ctor_get(v_s_2120_, 1);
                                            lean_dec(v_unused_2162_);
                                            v_unused_2163_ = lean_ctor_get(v_s_2120_, 0);
                                            lean_dec(v_unused_2163_);
                                            v___x_2150_ = v_s_2120_;
                                            v_isShared_2151_ = v_isSharedCheck_2160_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_dec(v_s_2120_);
                                            v___x_2150_ = lean_box(0);
                                            v_isShared_2151_ = v_isSharedCheck_2160_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_i_2144_);
                                        return v_s_2120_;
                                    }
                                } else {
                                    lean_dec(v_i_2144_);
                                    return v_s_2120_;
                                }
                            }
                        }
                    } else {
                        v_i_2164_ = lean_string_utf8_next_fast(v_input_2119_, v_pos_2122_);
                        v_curr_2165_ = lean_string_utf8_get(v_input_2119_, v_i_2164_);
                        v___x_2166_ = lean_uint32_dec_eq(v_curr_2165_, v___x_2137_);
                        if v___x_2166_ == 0 {
                            return v_s_2120_;
                        } else {
                            lean_inc(v_error_x3f_2124_);
                            lean_inc_ref(v_imports_2121_);
                            v_isSharedCheck_2177_ = (!lean_is_exclusive(v_s_2120_)) as u8;
                            if v_isSharedCheck_2177_ == 0 {
                                v_unused_2178_ = lean_ctor_get(v_s_2120_, 2);
                                lean_dec(v_unused_2178_);
                                v_unused_2179_ = lean_ctor_get(v_s_2120_, 1);
                                lean_dec(v_unused_2179_);
                                v_unused_2180_ = lean_ctor_get(v_s_2120_, 0);
                                lean_dec(v_unused_2180_);
                                v___x_2168_ = v_s_2120_;
                                v_isShared_2169_ = v_isSharedCheck_2177_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_s_2120_);
                                v___x_2168_ = lean_box(0);
                                v_isShared_2169_ = v_isSharedCheck_2177_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_inc(v_error_x3f_2124_);
                    lean_inc(v_pos_2122_);
                    lean_inc_ref(v_imports_2121_);
                    lean_dec_ref(v_s_2120_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2152_ = lean_unsigned_to_nat(1);
                v___x_2153_ = lean_string_utf8_next(v_input_2119_, v_i_2144_);
                lean_dec(v_i_2144_);
                if v_isShared_2151_ == 0 {
                    lean_ctor_set(v___x_2150_, 1, v___x_2153_);
                    v___x_2155_ = v___x_2150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_imports_2121_);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2153_);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_error_x3f_2124_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2159_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2123_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2159_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2125_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2159_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2126_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2159_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2127_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2159_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2128_,
                    );
                    v___x_2155_ = v_reuseFailAlloc_2159_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_s_2156_ =
                    l_Lean_ParseImports_finishCommentBlock(v___x_2152_, v_input_2119_, v___x_2155_);
                v_error_x3f_2157_ = lean_ctor_get(v_s_2156_, 2);
                lean_inc(v_error_x3f_2157_);
                if lean_obj_tag(v_error_x3f_2157_) == 1 {
                    lean_dec_ref_known(v_error_x3f_2157_, 1);
                    return v_s_2156_;
                } else {
                    lean_dec(v_error_x3f_2157_);
                    v_s_2120_ = v_s_2156_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                v___x_2170_ = lean_string_utf8_next(v_input_2119_, v_i_2164_);
                if v_isShared_2169_ == 0 {
                    lean_ctor_set(v___x_2168_, 1, v___x_2170_);
                    v___x_2172_ = v___x_2168_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_imports_2121_);
                    lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_error_x3f_2124_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2176_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2123_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2176_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2125_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2176_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2126_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2176_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2127_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2176_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2128_,
                    );
                    v___x_2172_ = v_reuseFailAlloc_2176_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_s_2173_ =
                    l_Lean_ParseImports_takeUntil___at___00Lean_ParseImports_whitespace_spec__0(
                        v_input_2119_,
                        v___x_2172_,
                    );
                v_error_x3f_2174_ = lean_ctor_get(v_s_2173_, 2);
                lean_inc(v_error_x3f_2174_);
                if lean_obj_tag(v_error_x3f_2174_) == 1 {
                    lean_dec_ref_known(v_error_x3f_2174_, 1);
                    return v_s_2173_;
                } else {
                    lean_dec(v_error_x3f_2174_);
                    v_s_2120_ = v_s_2173_;
                    state = 0;
                    continue;
                }
            }
            7 => {
                if v___y_2182_ == 0 {
                    v___x_2183_ = 13;
                    v___x_2184_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2183_);
                    if v___x_2184_ == 0 {
                        v___x_2185_ = 10;
                        v___x_2186_ = lean_uint32_dec_eq(v_curr_2134_, v___x_2185_);
                        v___y_2136_ = v___x_2186_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2136_ = v___x_2184_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_error_x3f_2124_);
                    lean_inc(v_pos_2122_);
                    lean_inc_ref(v_imports_2121_);
                    lean_dec_ref(v_s_2120_);
                    state = 1;
                    continue;
                }
            }
            8 => {
                v___x_2194_ = l_Lean_ParseImports_whitespace___closed__1;
                if v_isShared_2193_ == 0 {
                    lean_ctor_set(v___x_2192_, 2, v___x_2194_);
                    v___x_2196_ = v___x_2192_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_imports_2121_);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_pos_2122_);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 2, v___x_2194_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2197_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2123_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2197_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2125_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2197_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2126_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2197_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2127_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2197_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2128_,
                    );
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_whitespace___boxed(
    mut v_input_2202_: *mut LeanObject,
    mut v_s_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2204_: *mut LeanObject = core::ptr::null_mut();
    v_res_2204_ = l_Lean_ParseImports_whitespace(v_input_2202_, v_s_2203_);
    lean_dec_ref(v_input_2202_);
    return v_res_2204_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(
    mut v_k_2205_: *mut LeanObject,
    mut v_failure_2206_: *mut LeanObject,
    mut v_success_2207_: *mut LeanObject,
    mut v_input_2208_: *mut LeanObject,
    mut v_s_2209_: *mut LeanObject,
    mut v_i_2210_: *mut LeanObject,
    mut v_j_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v_curr_u2081_2214_: u32 = 0;
    let mut v_curr_u2082_2215_: u32 = 0;
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2224_: u8 = 0;
    let mut v_error_x3f_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2226_: u8 = 0;
    let mut v_isMeta_2227_: u8 = 0;
    let mut v_isExported_2228_: u8 = 0;
    let mut v_importAll_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_unused_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2212_ = lean_string_utf8_at_end(v_k_2205_, v_i_2210_);
                if v___x_2212_ == 0 {
                    v___x_2213_ = lean_string_utf8_at_end(v_input_2208_, v_j_2211_);
                    if v___x_2213_ == 0 {
                        v_curr_u2081_2214_ = lean_string_utf8_get_fast(v_k_2205_, v_i_2210_);
                        v_curr_u2082_2215_ = lean_string_utf8_get_fast(v_input_2208_, v_j_2211_);
                        v___x_2216_ = lean_uint32_dec_eq(v_curr_u2081_2214_, v_curr_u2082_2215_);
                        if v___x_2216_ == 0 {
                            lean_dec(v_j_2211_);
                            lean_dec(v_i_2210_);
                            lean_dec_ref(v_success_2207_);
                            v___x_2217_ = lean_apply_2(v_failure_2206_, v_input_2208_, v_s_2209_);
                            return v___x_2217_;
                        } else {
                            if v___x_2213_ == 0 {
                                v___x_2218_ = lean_string_utf8_next_fast(v_k_2205_, v_i_2210_);
                                lean_dec(v_i_2210_);
                                v___x_2219_ = lean_string_utf8_next_fast(v_input_2208_, v_j_2211_);
                                lean_dec(v_j_2211_);
                                v_i_2210_ = v___x_2218_;
                                v_j_2211_ = v___x_2219_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_2211_);
                                lean_dec(v_i_2210_);
                                lean_dec_ref(v_success_2207_);
                                v___x_2221_ =
                                    lean_apply_2(v_failure_2206_, v_input_2208_, v_s_2209_);
                                return v___x_2221_;
                            }
                        }
                    } else {
                        lean_dec(v_j_2211_);
                        lean_dec(v_i_2210_);
                        lean_dec_ref(v_success_2207_);
                        v___x_2222_ = lean_apply_2(v_failure_2206_, v_input_2208_, v_s_2209_);
                        return v___x_2222_;
                    }
                } else {
                    lean_dec(v_i_2210_);
                    lean_dec_ref(v_failure_2206_);
                    v_imports_2223_ = lean_ctor_get(v_s_2209_, 0);
                    v_badModifier_2224_ = lean_ctor_get_uint8(
                        v_s_2209_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_2225_ = lean_ctor_get(v_s_2209_, 2);
                    v_isModule_2226_ = lean_ctor_get_uint8(
                        v_s_2209_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_2227_ = lean_ctor_get_uint8(
                        v_s_2209_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_2228_ = lean_ctor_get_uint8(
                        v_s_2209_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_2229_ = lean_ctor_get_uint8(
                        v_s_2209_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2238_ = (!lean_is_exclusive(v_s_2209_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v_unused_2239_ = lean_ctor_get(v_s_2209_, 1);
                        lean_dec(v_unused_2239_);
                        v___x_2231_ = v_s_2209_;
                        v_isShared_2232_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_2225_);
                        lean_inc(v_imports_2223_);
                        lean_dec(v_s_2209_);
                        v___x_2231_ = lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2232_ == 0 {
                    lean_ctor_set(v___x_2231_, 1, v_j_2211_);
                    v___x_2234_ = v___x_2231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_imports_2223_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_j_2211_);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_error_x3f_2225_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2237_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2224_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2237_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2226_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2237_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2227_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2237_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2228_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2237_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2229_,
                    );
                    v___x_2234_ = v_reuseFailAlloc_2237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = l_Lean_ParseImports_whitespace(v_input_2208_, v___x_2234_);
                v___x_2236_ = lean_apply_2(v_success_2207_, v_input_2208_, v___x_2235_);
                return v___x_2236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___boxed(
    mut v_k_2240_: *mut LeanObject,
    mut v_failure_2241_: *mut LeanObject,
    mut v_success_2242_: *mut LeanObject,
    mut v_input_2243_: *mut LeanObject,
    mut v_s_2244_: *mut LeanObject,
    mut v_i_2245_: *mut LeanObject,
    mut v_j_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2247_: *mut LeanObject = core::ptr::null_mut();
    v_res_2247_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(
        v_k_2240_,
        v_failure_2241_,
        v_success_2242_,
        v_input_2243_,
        v_s_2244_,
        v_i_2245_,
        v_j_2246_,
    );
    lean_dec_ref(v_k_2240_);
    return v_res_2247_;
}
pub unsafe fn l_Lean_ParseImports_keywordCore(
    mut v_k_2248_: *mut LeanObject,
    mut v_failure_2249_: *mut LeanObject,
    mut v_success_2250_: *mut LeanObject,
    mut v_input_2251_: *mut LeanObject,
    mut v_s_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v_pos_2253_ = lean_ctor_get(v_s_2252_, 1);
    lean_inc(v_pos_2253_);
    v___x_2254_ = lean_unsigned_to_nat(0);
    v___x_2255_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(
        v_k_2248_,
        v_failure_2249_,
        v_success_2250_,
        v_input_2251_,
        v_s_2252_,
        v___x_2254_,
        v_pos_2253_,
    );
    return v___x_2255_;
}
pub unsafe fn l_Lean_ParseImports_keywordCore___boxed(
    mut v_k_2256_: *mut LeanObject,
    mut v_failure_2257_: *mut LeanObject,
    mut v_success_2258_: *mut LeanObject,
    mut v_input_2259_: *mut LeanObject,
    mut v_s_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_ParseImports_keywordCore(
        v_k_2256_,
        v_failure_2257_,
        v_success_2258_,
        v_input_2259_,
        v_s_2260_,
    );
    lean_dec_ref(v_k_2256_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_ParseImports_keyword___lam__0(
    mut v_k_2264_: *mut LeanObject,
    mut v_x_2265_: *mut LeanObject,
    mut v_s_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2269_: u8 = 0;
    let mut v_isModule_2270_: u8 = 0;
    let mut v_isMeta_2271_: u8 = 0;
    let mut v_isExported_2272_: u8 = 0;
    let mut v_importAll_2273_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2276_: u8 = 0;
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v_unused_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2267_ = lean_ctor_get(v_s_2266_, 0);
                v_pos_2268_ = lean_ctor_get(v_s_2266_, 1);
                v_badModifier_2269_ = lean_ctor_get_uint8(
                    v_s_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isModule_2270_ = lean_ctor_get_uint8(
                    v_s_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2271_ = lean_ctor_get_uint8(
                    v_s_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2272_ = lean_ctor_get_uint8(
                    v_s_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2273_ = lean_ctor_get_uint8(
                    v_s_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2285_ = (!lean_is_exclusive(v_s_2266_)) as u8;
                if v_isSharedCheck_2285_ == 0 {
                    v_unused_2286_ = lean_ctor_get(v_s_2266_, 2);
                    lean_dec(v_unused_2286_);
                    v___x_2275_ = v_s_2266_;
                    v_isShared_2276_ = v_isSharedCheck_2285_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_2268_);
                    lean_inc(v_imports_2267_);
                    lean_dec(v_s_2266_);
                    v___x_2275_ = lean_box(0);
                    v_isShared_2276_ = v_isSharedCheck_2285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2277_ = l_Lean_ParseImports_keyword___lam__0___closed__0;
                v___x_2278_ = lean_string_append(v___x_2277_, v_k_2264_);
                v___x_2279_ = l_Lean_ParseImports_keyword___lam__0___closed__1;
                v___x_2280_ = lean_string_append(v___x_2278_, v___x_2279_);
                v___x_2281_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2281_, 0, v___x_2280_);
                if v_isShared_2276_ == 0 {
                    lean_ctor_set(v___x_2275_, 2, v___x_2281_);
                    v___x_2283_ = v___x_2275_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_imports_2267_);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_pos_2268_);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 2, v___x_2281_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2284_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2269_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2284_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2270_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2284_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2271_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2284_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2272_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2284_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2273_,
                    );
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_keyword___lam__0___boxed(
    mut v_k_2287_: *mut LeanObject,
    mut v_x_2288_: *mut LeanObject,
    mut v_s_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Lean_ParseImports_keyword___lam__0(v_k_2287_, v_x_2288_, v_s_2289_);
    lean_dec_ref(v_x_2288_);
    lean_dec_ref(v_k_2287_);
    return v_res_2290_;
}
pub unsafe fn l_Lean_ParseImports_keyword(
    mut v_k_2291_: *mut LeanObject,
    mut v_a_2292_: *mut LeanObject,
    mut v_a_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v_pos_2294_ = lean_ctor_get(v_a_2293_, 1);
    lean_inc(v_pos_2294_);
    lean_inc_ref(v_k_2291_);
    v___f_2295_ = lean_alloc_closure(
        l_Lean_ParseImports_keyword___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2295_, 0, v_k_2291_);
    v___x_2296_ = lean_alloc_closure(
        l_Lean_ParseImports_skip___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_2297_ = lean_unsigned_to_nat(0);
    v___x_2298_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go(
        v_k_2291_,
        v___f_2295_,
        v___x_2296_,
        v_a_2292_,
        v_a_2293_,
        v___x_2297_,
        v_pos_2294_,
    );
    lean_dec_ref(v_k_2291_);
    return v___x_2298_;
}
pub unsafe fn l_Lean_ParseImports_isIdCont(
    mut v_input_2299_: *mut LeanObject,
    mut v_s_2300_: *mut LeanObject,
) -> u8 {
    let mut v_pos_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2302_: u32 = 0;
    let mut v___x_2303_: u32 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v_i_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v_curr_2307_: u32 = 0;
    let mut v___y_2309_: u8 = 0;
    let mut v___x_2310_: u32 = 0;
    let mut v___x_2311_: u8 = 0;
    let mut v___y_2313_: u8 = 0;
    let mut v___x_2314_: u32 = 0;
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2318_: u32 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: u32 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u32 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: u32 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2301_ = lean_ctor_get(v_s_2300_, 1);
                v_curr_2302_ = lean_string_utf8_get(v_input_2299_, v_pos_2301_);
                v___x_2303_ = 46;
                v___x_2304_ = lean_uint32_dec_eq(v_curr_2302_, v___x_2303_);
                if v___x_2304_ == 0 {
                    return v___x_2304_;
                } else {
                    v_i_2305_ = lean_string_utf8_next(v_input_2299_, v_pos_2301_);
                    v___x_2306_ = lean_string_utf8_at_end(v_input_2299_, v_i_2305_);
                    if v___x_2306_ == 0 {
                        v_curr_2307_ = lean_string_utf8_get_fast(v_input_2299_, v_i_2305_);
                        lean_dec(v_i_2305_);
                        v___x_2322_ = 65;
                        v___x_2323_ = lean_uint32_dec_le(v___x_2322_, v_curr_2307_);
                        if v___x_2323_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___x_2324_ = 90;
                            v___x_2325_ = lean_uint32_dec_le(v_curr_2307_, v___x_2324_);
                            if v___x_2325_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                return v___x_2304_;
                            }
                        }
                    } else {
                        lean_dec(v_i_2305_);
                        v___x_2326_ = 0;
                        return v___x_2326_;
                    }
                }
            }
            1 => {
                if v___y_2309_ == 0 {
                    v___x_2310_ = 171;
                    v___x_2311_ = lean_uint32_dec_eq(v_curr_2307_, v___x_2310_);
                    return v___x_2311_;
                } else {
                    return v___x_2304_;
                }
            }
            2 => {
                if v___y_2313_ == 0 {
                    v___x_2314_ = 95;
                    v___x_2315_ = lean_uint32_dec_eq(v_curr_2307_, v___x_2314_);
                    if v___x_2315_ == 0 {
                        v___x_2316_ = l_Lean_isLetterLike(v_curr_2307_);
                        v___y_2309_ = v___x_2316_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2309_ = v___x_2315_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2304_;
                }
            }
            3 => {
                v___x_2318_ = 97;
                v___x_2319_ = lean_uint32_dec_le(v___x_2318_, v_curr_2307_);
                if v___x_2319_ == 0 {
                    v___y_2313_ = v___x_2319_;
                    state = 2;
                    continue;
                } else {
                    v___x_2320_ = 122;
                    v___x_2321_ = lean_uint32_dec_le(v_curr_2307_, v___x_2320_);
                    v___y_2313_ = v___x_2321_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_isIdCont___boxed(
    mut v_input_2327_: *mut LeanObject,
    mut v_s_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: u8 = 0;
    let mut v_r_2330_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_ParseImports_isIdCont(v_input_2327_, v_s_2328_);
    lean_dec_ref(v_s_2328_);
    lean_dec_ref(v_input_2327_);
    v_r_2330_ = lean_box((v_res_2329_) as usize);
    return v_r_2330_;
}
pub unsafe fn l_Lean_ParseImports_State_pushImport(
    mut v_i_2331_: *mut LeanObject,
    mut v_s_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2335_: u8 = 0;
    let mut v_error_x3f_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2337_: u8 = 0;
    let mut v_isMeta_2338_: u8 = 0;
    let mut v_isExported_2339_: u8 = 0;
    let mut v_importAll_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2333_ = lean_ctor_get(v_s_2332_, 0);
                v_pos_2334_ = lean_ctor_get(v_s_2332_, 1);
                v_badModifier_2335_ = lean_ctor_get_uint8(
                    v_s_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2336_ = lean_ctor_get(v_s_2332_, 2);
                v_isModule_2337_ = lean_ctor_get_uint8(
                    v_s_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2338_ = lean_ctor_get_uint8(
                    v_s_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2339_ = lean_ctor_get_uint8(
                    v_s_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2340_ = lean_ctor_get_uint8(
                    v_s_2332_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2348_ = (!lean_is_exclusive(v_s_2332_)) as u8;
                if v_isSharedCheck_2348_ == 0 {
                    v___x_2342_ = v_s_2332_;
                    v_isShared_2343_ = v_isSharedCheck_2348_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_2336_);
                    lean_inc(v_pos_2334_);
                    lean_inc(v_imports_2333_);
                    lean_dec(v_s_2332_);
                    v___x_2342_ = lean_box(0);
                    v_isShared_2343_ = v_isSharedCheck_2348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2344_ = lean_array_push(v_imports_2333_, v_i_2331_);
                if v_isShared_2343_ == 0 {
                    lean_ctor_set(v___x_2342_, 0, v___x_2344_);
                    v___x_2346_ = v___x_2342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
                    lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_pos_2334_);
                    lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_error_x3f_2336_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2347_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2335_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2347_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2337_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2347_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2338_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2347_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2339_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2347_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2340_,
                    );
                    v___x_2346_ = v_reuseFailAlloc_2347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_isIdRestCold(mut v_c_2349_: u32) -> u8 {
    let mut v___y_2351_: u8 = 0;
    let mut v___x_2352_: u32 = 0;
    let mut v___x_2353_: u8 = 0;
    let mut v___x_2354_: u32 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: u32 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: u32 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = 95;
                v___x_2359_ = lean_uint32_dec_eq(v_c_2349_, v___x_2358_);
                if v___x_2359_ == 0 {
                    v___x_2360_ = 39;
                    v___x_2361_ = lean_uint32_dec_eq(v_c_2349_, v___x_2360_);
                    v___y_2351_ = v___x_2361_;
                    state = 1;
                    continue;
                } else {
                    v___y_2351_ = v___x_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2351_ == 0 {
                    v___x_2352_ = 33;
                    v___x_2353_ = lean_uint32_dec_eq(v_c_2349_, v___x_2352_);
                    if v___x_2353_ == 0 {
                        v___x_2354_ = 63;
                        v___x_2355_ = lean_uint32_dec_eq(v_c_2349_, v___x_2354_);
                        if v___x_2355_ == 0 {
                            v___x_2356_ = l_Lean_isLetterLike(v_c_2349_);
                            if v___x_2356_ == 0 {
                                v___x_2357_ = l_Lean_isSubScriptAlnum(v_c_2349_);
                                return v___x_2357_;
                            } else {
                                return v___x_2356_;
                            }
                        } else {
                            return v___x_2355_;
                        }
                    } else {
                        return v___x_2353_;
                    }
                } else {
                    return v___y_2351_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_isIdRestCold___boxed(
    mut v_c_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2363_: u32 = 0;
    let mut v_res_2364_: u8 = 0;
    let mut v_r_2365_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2363_ = lean_unbox_uint32(v_c_2362_);
    lean_dec(v_c_2362_);
    v_res_2364_ = l_Lean_ParseImports_isIdRestCold(v_c_boxed_2363_);
    v_r_2365_ = lean_box((v_res_2364_) as usize);
    return v_r_2365_;
}
pub unsafe fn l_Lean_ParseImports_isIdRestFast(mut v_c_2366_: u32) -> u8 {
    let mut v___y_2368_: u8 = 0;
    let mut v___x_2369_: u32 = 0;
    let mut v___x_2370_: u8 = 0;
    let mut v___x_2371_: u32 = 0;
    let mut v___x_2372_: u8 = 0;
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: u8 = 0;
    let mut v___y_2376_: u8 = 0;
    let mut v___x_2377_: u32 = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: u32 = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: u32 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut v___x_2383_: u32 = 0;
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: u32 = 0;
    let mut v___x_2386_: u8 = 0;
    let mut v___y_2388_: u8 = 0;
    let mut v___x_2389_: u32 = 0;
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: u32 = 0;
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2394_: u32 = 0;
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: u32 = 0;
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: u32 = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: u32 = 0;
    let mut v___x_2401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2398_ = 65;
                v___x_2399_ = lean_uint32_dec_le(v___x_2398_, v_c_2366_);
                if v___x_2399_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_2400_ = 90;
                    v___x_2401_ = lean_uint32_dec_le(v_c_2366_, v___x_2400_);
                    if v___x_2401_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        return v___x_2401_;
                    }
                }
            }
            1 => {
                if v___y_2368_ == 0 {
                    v___x_2369_ = 33;
                    v___x_2370_ = lean_uint32_dec_eq(v_c_2366_, v___x_2369_);
                    if v___x_2370_ == 0 {
                        v___x_2371_ = 63;
                        v___x_2372_ = lean_uint32_dec_eq(v_c_2366_, v___x_2371_);
                        if v___x_2372_ == 0 {
                            v___x_2373_ = l_Lean_isLetterLike(v_c_2366_);
                            if v___x_2373_ == 0 {
                                v___x_2374_ = l_Lean_isSubScriptAlnum(v_c_2366_);
                                return v___x_2374_;
                            } else {
                                return v___x_2373_;
                            }
                        } else {
                            return v___x_2372_;
                        }
                    } else {
                        return v___x_2370_;
                    }
                } else {
                    return v___y_2368_;
                }
            }
            2 => {
                if v___y_2376_ == 0 {
                    v___x_2377_ = 46;
                    v___x_2378_ = lean_uint32_dec_eq(v_c_2366_, v___x_2377_);
                    if v___x_2378_ == 0 {
                        v___x_2379_ = 10;
                        v___x_2380_ = lean_uint32_dec_eq(v_c_2366_, v___x_2379_);
                        if v___x_2380_ == 0 {
                            v___x_2381_ = 32;
                            v___x_2382_ = lean_uint32_dec_eq(v_c_2366_, v___x_2381_);
                            if v___x_2382_ == 0 {
                                v___x_2383_ = 95;
                                v___x_2384_ = lean_uint32_dec_eq(v_c_2366_, v___x_2383_);
                                if v___x_2384_ == 0 {
                                    v___x_2385_ = 39;
                                    v___x_2386_ = lean_uint32_dec_eq(v_c_2366_, v___x_2385_);
                                    v___y_2368_ = v___x_2386_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_2368_ = v___x_2384_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                return v___y_2376_;
                            }
                        } else {
                            return v___y_2376_;
                        }
                    } else {
                        return v___y_2376_;
                    }
                } else {
                    return v___y_2376_;
                }
            }
            3 => {
                if v___y_2388_ == 0 {
                    v___x_2389_ = 48;
                    v___x_2390_ = lean_uint32_dec_le(v___x_2389_, v_c_2366_);
                    if v___x_2390_ == 0 {
                        v___y_2376_ = v___x_2390_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2391_ = 57;
                        v___x_2392_ = lean_uint32_dec_le(v_c_2366_, v___x_2391_);
                        v___y_2376_ = v___x_2392_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_2388_;
                }
            }
            4 => {
                v___x_2394_ = 97;
                v___x_2395_ = lean_uint32_dec_le(v___x_2394_, v_c_2366_);
                if v___x_2395_ == 0 {
                    v___y_2388_ = v___x_2395_;
                    state = 3;
                    continue;
                } else {
                    v___x_2396_ = 122;
                    v___x_2397_ = lean_uint32_dec_le(v_c_2366_, v___x_2396_);
                    v___y_2388_ = v___x_2397_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_isIdRestFast___boxed(
    mut v_c_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2403_: u32 = 0;
    let mut v_res_2404_: u8 = 0;
    let mut v_r_2405_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2403_ = lean_unbox_uint32(v_c_2402_);
    lean_dec(v_c_2402_);
    v_res_2404_ = l_Lean_ParseImports_isIdRestFast(v_c_boxed_2403_);
    v_r_2405_ = lean_box((v_res_2404_) as usize);
    return v_r_2405_;
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(
    mut v_input_2406_: *mut LeanObject,
    mut v_s_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2410_: u8 = 0;
    let mut v_error_x3f_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2412_: u8 = 0;
    let mut v_isMeta_2413_: u8 = 0;
    let mut v_isExported_2414_: u8 = 0;
    let mut v_importAll_2415_: u8 = 0;
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u32 = 0;
    let mut v___x_2418_: u32 = 0;
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_unused_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2408_ = lean_ctor_get(v_s_2407_, 0);
                v_pos_2409_ = lean_ctor_get(v_s_2407_, 1);
                v_badModifier_2410_ = lean_ctor_get_uint8(
                    v_s_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2411_ = lean_ctor_get(v_s_2407_, 2);
                v_isModule_2412_ = lean_ctor_get_uint8(
                    v_s_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2413_ = lean_ctor_get_uint8(
                    v_s_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2414_ = lean_ctor_get_uint8(
                    v_s_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2415_ = lean_ctor_get_uint8(
                    v_s_2407_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2416_ = lean_string_utf8_at_end(v_input_2406_, v_pos_2409_);
                if v___x_2416_ == 0 {
                    v___x_2417_ = lean_string_utf8_get_fast(v_input_2406_, v_pos_2409_);
                    v___x_2418_ = 187;
                    v___x_2419_ = lean_uint32_dec_eq(v___x_2417_, v___x_2418_);
                    if v___x_2419_ == 0 {
                        lean_inc(v_error_x3f_2411_);
                        lean_inc(v_pos_2409_);
                        lean_inc_ref(v_imports_2408_);
                        v_isSharedCheck_2428_ = (!lean_is_exclusive(v_s_2407_)) as u8;
                        if v_isSharedCheck_2428_ == 0 {
                            v_unused_2429_ = lean_ctor_get(v_s_2407_, 2);
                            lean_dec(v_unused_2429_);
                            v_unused_2430_ = lean_ctor_get(v_s_2407_, 1);
                            lean_dec(v_unused_2430_);
                            v_unused_2431_ = lean_ctor_get(v_s_2407_, 0);
                            lean_dec(v_unused_2431_);
                            v___x_2421_ = v_s_2407_;
                            v_isShared_2422_ = v_isSharedCheck_2428_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2407_);
                            v___x_2421_ = lean_box(0);
                            v_isShared_2422_ = v_isSharedCheck_2428_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_s_2407_;
                    }
                } else {
                    return v_s_2407_;
                }
            }
            1 => {
                v___x_2423_ = lean_string_utf8_next_fast(v_input_2406_, v_pos_2409_);
                lean_dec(v_pos_2409_);
                if v_isShared_2422_ == 0 {
                    lean_ctor_set(v___x_2421_, 1, v___x_2423_);
                    v___x_2425_ = v___x_2421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_imports_2408_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2423_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_error_x3f_2411_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2410_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2412_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2413_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2414_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2427_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2415_,
                    );
                    v___x_2425_ = v_reuseFailAlloc_2427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s_2407_ = v___x_2425_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1___boxed(
    mut v_input_2432_: *mut LeanObject,
    mut v_s_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2434_: *mut LeanObject = core::ptr::null_mut();
    v_res_2434_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_2432_, v_s_2433_);
    lean_dec_ref(v_input_2432_);
    return v_res_2434_;
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(
    mut v___y_2435_: u8,
    mut v_curr_2436_: u32,
    mut v_input_2437_: *mut LeanObject,
    mut v_s_2438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2441_: u8 = 0;
    let mut v_error_x3f_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2443_: u8 = 0;
    let mut v_isMeta_2444_: u8 = 0;
    let mut v_isExported_2445_: u8 = 0;
    let mut v_importAll_2446_: u8 = 0;
    let mut v___y_2448_: u8 = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut v_unused_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: u32 = 0;
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: u32 = 0;
    let mut v___y_2466_: u8 = 0;
    let mut v___x_2467_: u32 = 0;
    let mut v___x_2468_: u8 = 0;
    let mut v___x_2469_: u32 = 0;
    let mut v___x_2470_: u8 = 0;
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: u8 = 0;
    let mut v___y_2474_: u8 = 0;
    let mut v___x_2475_: u32 = 0;
    let mut v___x_2476_: u8 = 0;
    let mut v___x_2477_: u32 = 0;
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: u32 = 0;
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2481_: u32 = 0;
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: u32 = 0;
    let mut v___x_2484_: u8 = 0;
    let mut v___y_2486_: u8 = 0;
    let mut v___x_2487_: u32 = 0;
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: u32 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2492_: u32 = 0;
    let mut v___x_2493_: u8 = 0;
    let mut v___x_2494_: u32 = 0;
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: u32 = 0;
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: u32 = 0;
    let mut v___x_2499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2439_ = lean_ctor_get(v_s_2438_, 0);
                v_pos_2440_ = lean_ctor_get(v_s_2438_, 1);
                v_badModifier_2441_ = lean_ctor_get_uint8(
                    v_s_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2442_ = lean_ctor_get(v_s_2438_, 2);
                v_isModule_2443_ = lean_ctor_get_uint8(
                    v_s_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2444_ = lean_ctor_get_uint8(
                    v_s_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2445_ = lean_ctor_get_uint8(
                    v_s_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2446_ = lean_ctor_get_uint8(
                    v_s_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2461_ = lean_string_utf8_at_end(v_input_2437_, v_pos_2440_);
                if v___x_2461_ == 0 {
                    v___x_2462_ = 171;
                    v___x_2463_ = lean_uint32_dec_eq(v_curr_2436_, v___x_2462_);
                    v___x_2464_ = lean_string_utf8_get_fast(v_input_2437_, v_pos_2440_);
                    v___x_2496_ = 65;
                    v___x_2497_ = lean_uint32_dec_le(v___x_2496_, v___x_2464_);
                    if v___x_2497_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___x_2498_ = 90;
                        v___x_2499_ = lean_uint32_dec_le(v___x_2464_, v___x_2498_);
                        if v___x_2499_ == 0 {
                            state = 7;
                            continue;
                        } else {
                            v___y_2448_ = v___x_2463_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_s_2438_;
                }
            }
            1 => {
                if v___y_2448_ == 0 {
                    lean_inc(v_error_x3f_2442_);
                    lean_inc(v_pos_2440_);
                    lean_inc_ref(v_imports_2439_);
                    v_isSharedCheck_2457_ = (!lean_is_exclusive(v_s_2438_)) as u8;
                    if v_isSharedCheck_2457_ == 0 {
                        v_unused_2458_ = lean_ctor_get(v_s_2438_, 2);
                        lean_dec(v_unused_2458_);
                        v_unused_2459_ = lean_ctor_get(v_s_2438_, 1);
                        lean_dec(v_unused_2459_);
                        v_unused_2460_ = lean_ctor_get(v_s_2438_, 0);
                        lean_dec(v_unused_2460_);
                        v___x_2450_ = v_s_2438_;
                        v_isShared_2451_ = v_isSharedCheck_2457_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_s_2438_);
                        v___x_2450_ = lean_box(0);
                        v_isShared_2451_ = v_isSharedCheck_2457_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_s_2438_;
                }
            }
            2 => {
                v___x_2452_ = lean_string_utf8_next_fast(v_input_2437_, v_pos_2440_);
                lean_dec(v_pos_2440_);
                if v_isShared_2451_ == 0 {
                    lean_ctor_set(v___x_2450_, 1, v___x_2452_);
                    v___x_2454_ = v___x_2450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_imports_2439_);
                    lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2452_);
                    lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_error_x3f_2442_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2441_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2443_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2444_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2445_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2446_,
                    );
                    v___x_2454_ = v_reuseFailAlloc_2456_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_s_2438_ = v___x_2454_;
                state = 0;
                continue;
            }
            4 => {
                if v___y_2466_ == 0 {
                    v___x_2467_ = 33;
                    v___x_2468_ = lean_uint32_dec_eq(v___x_2464_, v___x_2467_);
                    if v___x_2468_ == 0 {
                        v___x_2469_ = 63;
                        v___x_2470_ = lean_uint32_dec_eq(v___x_2464_, v___x_2469_);
                        if v___x_2470_ == 0 {
                            v___x_2471_ = l_Lean_isLetterLike(v___x_2464_);
                            if v___x_2471_ == 0 {
                                v___x_2472_ = l_Lean_isSubScriptAlnum(v___x_2464_);
                                if v___x_2472_ == 0 {
                                    v___y_2448_ = v___y_2435_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_2448_ = v___x_2463_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                if v___x_2471_ == 0 {
                                    v___y_2448_ = v___y_2435_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_2448_ = v___x_2463_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            if v___x_2470_ == 0 {
                                v___y_2448_ = v___y_2435_;
                                state = 1;
                                continue;
                            } else {
                                v___y_2448_ = v___x_2463_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if v___x_2468_ == 0 {
                            v___y_2448_ = v___y_2435_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2448_ = v___x_2463_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___y_2448_ = v___x_2463_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_2474_ == 0 {
                    v___x_2475_ = 46;
                    v___x_2476_ = lean_uint32_dec_eq(v___x_2464_, v___x_2475_);
                    if v___x_2476_ == 0 {
                        v___x_2477_ = 10;
                        v___x_2478_ = lean_uint32_dec_eq(v___x_2464_, v___x_2477_);
                        if v___x_2478_ == 0 {
                            v___x_2479_ = 32;
                            v___x_2480_ = lean_uint32_dec_eq(v___x_2464_, v___x_2479_);
                            if v___x_2480_ == 0 {
                                v___x_2481_ = 95;
                                v___x_2482_ = lean_uint32_dec_eq(v___x_2464_, v___x_2481_);
                                if v___x_2482_ == 0 {
                                    v___x_2483_ = 39;
                                    v___x_2484_ = lean_uint32_dec_eq(v___x_2464_, v___x_2483_);
                                    v___y_2466_ = v___x_2484_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___y_2466_ = v___x_2482_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___y_2448_ = v___x_2480_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_2448_ = v___x_2478_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2448_ = v___x_2476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_2448_ = v___x_2463_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                if v___y_2486_ == 0 {
                    v___x_2487_ = 48;
                    v___x_2488_ = lean_uint32_dec_le(v___x_2487_, v___x_2464_);
                    if v___x_2488_ == 0 {
                        v___y_2474_ = v___x_2488_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2489_ = 57;
                        v___x_2490_ = lean_uint32_dec_le(v___x_2464_, v___x_2489_);
                        v___y_2474_ = v___x_2490_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_2448_ = v___x_2463_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2492_ = 97;
                v___x_2493_ = lean_uint32_dec_le(v___x_2492_, v___x_2464_);
                if v___x_2493_ == 0 {
                    v___y_2486_ = v___x_2493_;
                    state = 6;
                    continue;
                } else {
                    v___x_2494_ = 122;
                    v___x_2495_ = lean_uint32_dec_le(v___x_2464_, v___x_2494_);
                    v___y_2486_ = v___x_2495_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0___boxed(
    mut v___y_2500_: *mut LeanObject,
    mut v_curr_2501_: *mut LeanObject,
    mut v_input_2502_: *mut LeanObject,
    mut v_s_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2267__boxed_2504_: u8 = 0;
    let mut v_curr_boxed_2505_: u32 = 0;
    let mut v_res_2506_: *mut LeanObject = core::ptr::null_mut();
    v___y_2267__boxed_2504_ = (lean_unbox(v___y_2500_) as u8);
    v_curr_boxed_2505_ = lean_unbox_uint32(v_curr_2501_);
    lean_dec(v_curr_2501_);
    v_res_2506_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_2267__boxed_2504_, v_curr_boxed_2505_, v_input_2502_, v_s_2503_);
    lean_dec_ref(v_input_2502_);
    return v_res_2506_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(
    mut v_input_2513_: *mut LeanObject,
    mut v_finalize_2514_: *mut LeanObject,
    mut v_module_2515_: *mut LeanObject,
    mut v_s_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: u8 = 0;
    let mut v___y_2522_: u8 = 0;
    let mut v___y_2523_: u8 = 0;
    let mut v___y_2524_: u8 = 0;
    let mut v___y_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: u8 = 0;
    let mut v___y_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2535_: u8 = 0;
    let mut v_error_x3f_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2537_: u8 = 0;
    let mut v_isMeta_2538_: u8 = 0;
    let mut v_isExported_2539_: u8 = 0;
    let mut v_importAll_2540_: u8 = 0;
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2544_: u8 = 0;
    let mut v_curr_2545_: u32 = 0;
    let mut v___x_2546_: u32 = 0;
    let mut v___y_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: u8 = 0;
    let mut v___y_2551_: u32 = 0;
    let mut v___y_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: u8 = 0;
    let mut v___y_2554_: u8 = 0;
    let mut v___y_2555_: u8 = 0;
    let mut v___y_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2557_: u8 = 0;
    let mut v___y_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: u8 = 0;
    let mut v___y_2560_: u8 = 0;
    let mut v___x_2561_: u8 = 0;
    let mut v___y_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2565_: u8 = 0;
    let mut v___y_2566_: u32 = 0;
    let mut v___y_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2568_: u8 = 0;
    let mut v___y_2569_: u8 = 0;
    let mut v___y_2570_: u8 = 0;
    let mut v___y_2571_: u8 = 0;
    let mut v___y_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2574_: u8 = 0;
    let mut v___y_2575_: u8 = 0;
    let mut v___x_2576_: u32 = 0;
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: u8 = 0;
    let mut v___y_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2582_: u8 = 0;
    let mut v___y_2583_: u32 = 0;
    let mut v___y_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: u8 = 0;
    let mut v___y_2586_: u8 = 0;
    let mut v___y_2587_: u8 = 0;
    let mut v___y_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: u8 = 0;
    let mut v___y_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: u8 = 0;
    let mut v___x_2592_: u32 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: u32 = 0;
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2596_: u8 = 0;
    let mut v___y_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2605_: u8 = 0;
    let mut v_error_x3f_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2607_: u8 = 0;
    let mut v_isMeta_2608_: u8 = 0;
    let mut v_isExported_2609_: u8 = 0;
    let mut v_importAll_2610_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2613_: u32 = 0;
    let mut v___x_2614_: u32 = 0;
    let mut v___x_2615_: u8 = 0;
    let mut v_i_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: u8 = 0;
    let mut v_curr_2618_: u32 = 0;
    let mut v___x_2619_: u32 = 0;
    let mut v___x_2620_: u8 = 0;
    let mut v___x_2621_: u32 = 0;
    let mut v___x_2622_: u8 = 0;
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2629_: u8 = 0;
    let mut v___x_2630_: u32 = 0;
    let mut v___x_2631_: u8 = 0;
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2634_: u32 = 0;
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: u32 = 0;
    let mut v___x_2637_: u8 = 0;
    let mut v___x_2638_: u32 = 0;
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: u32 = 0;
    let mut v___x_2641_: u8 = 0;
    let mut v_startPart_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2647_: u8 = 0;
    let mut v_error_x3f_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2649_: u8 = 0;
    let mut v_isMeta_2650_: u8 = 0;
    let mut v_isExported_2651_: u8 = 0;
    let mut v_importAll_2652_: u8 = 0;
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2656_: u8 = 0;
    let mut v_i_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: u8 = 0;
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2668_: u32 = 0;
    let mut v___x_2669_: u32 = 0;
    let mut v___x_2670_: u8 = 0;
    let mut v_i_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v_curr_2673_: u32 = 0;
    let mut v___y_2675_: u8 = 0;
    let mut v___x_2676_: u8 = 0;
    let mut v___y_2678_: u8 = 0;
    let mut v___x_2679_: u32 = 0;
    let mut v___x_2680_: u8 = 0;
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2683_: u32 = 0;
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: u32 = 0;
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: u32 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: u32 = 0;
    let mut v___x_2690_: u8 = 0;
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_unused_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2533_ = lean_ctor_get(v_s_2516_, 0);
                v_pos_2534_ = lean_ctor_get(v_s_2516_, 1);
                v_badModifier_2535_ = lean_ctor_get_uint8(
                    v_s_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2536_ = lean_ctor_get(v_s_2516_, 2);
                v_isModule_2537_ = lean_ctor_get_uint8(
                    v_s_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2538_ = lean_ctor_get_uint8(
                    v_s_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2539_ = lean_ctor_get_uint8(
                    v_s_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2540_ = lean_ctor_get_uint8(
                    v_s_2516_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2541_ = lean_string_utf8_at_end(v_input_2513_, v_pos_2534_);
                if v___x_2541_ == 0 {
                    lean_inc(v_error_x3f_2536_);
                    lean_inc(v_pos_2534_);
                    lean_inc_ref(v_imports_2533_);
                    v_isSharedCheck_2697_ = (!lean_is_exclusive(v_s_2516_)) as u8;
                    if v_isSharedCheck_2697_ == 0 {
                        v_unused_2698_ = lean_ctor_get(v_s_2516_, 2);
                        lean_dec(v_unused_2698_);
                        v_unused_2699_ = lean_ctor_get(v_s_2516_, 1);
                        lean_dec(v_unused_2699_);
                        v_unused_2700_ = lean_ctor_get(v_s_2516_, 0);
                        lean_dec(v_unused_2700_);
                        v___x_2543_ = v_s_2516_;
                        v_isShared_2544_ = v_isSharedCheck_2697_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_s_2516_);
                        v___x_2543_ = lean_box(0);
                        v_isShared_2544_ = v_isSharedCheck_2697_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_module_2515_);
                    lean_dec_ref(v_finalize_2514_);
                    lean_dec_ref(v_input_2513_);
                    v___x_2701_ = l_Lean_ParseImports_State_mkEOIError(v_s_2516_);
                    return v___x_2701_;
                }
            }
            1 => {
                if v___y_2528_ == 0 {
                    lean_dec_ref(v___y_2526_);
                    lean_dec(v___y_2525_);
                    lean_dec(v___y_2518_);
                    v___x_2529_ =
                        lean_apply_3(v_finalize_2514_, v___y_2519_, v_input_2513_, v___y_2520_);
                    return v___x_2529_;
                } else {
                    lean_dec_ref(v___y_2520_);
                    v___x_2530_ = lean_string_utf8_next(v_input_2513_, v___y_2518_);
                    lean_dec(v___y_2518_);
                    v_s_2531_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_s_2531_, 0, v___y_2526_);
                    lean_ctor_set(v_s_2531_, 1, v___x_2530_);
                    lean_ctor_set(v_s_2531_, 2, v___y_2525_);
                    lean_ctor_set_uint8(
                        v_s_2531_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___y_2523_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2531_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v___y_2527_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2531_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v___y_2522_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2531_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v___y_2524_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2531_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v___y_2521_,
                    );
                    v_module_2515_ = v___y_2519_;
                    v_s_2516_ = v_s_2531_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_curr_2545_ = lean_string_utf8_get_fast(v_input_2513_, v_pos_2534_);
                v___x_2546_ = 171;
                v___x_2596_ = lean_uint32_dec_eq(v_curr_2545_, v___x_2546_);
                if v___x_2596_ == 0 {
                    v___x_2638_ = 65;
                    v___x_2639_ = lean_uint32_dec_le(v___x_2638_, v_curr_2545_);
                    if v___x_2639_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        v___x_2640_ = 90;
                        v___x_2641_ = lean_uint32_dec_le(v_curr_2545_, v___x_2640_);
                        if v___x_2641_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_2598_ = v___x_2641_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2543_);
                    v_startPart_2642_ = lean_string_utf8_next_fast(v_input_2513_, v_pos_2534_);
                    lean_dec(v_pos_2534_);
                    v___x_2643_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v___x_2643_, 0, v_imports_2533_);
                    lean_ctor_set(v___x_2643_, 1, v_startPart_2642_);
                    lean_ctor_set(v___x_2643_, 2, v_error_x3f_2536_);
                    lean_ctor_set_uint8(
                        v___x_2643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2535_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2537_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2538_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2539_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2643_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2540_,
                    );
                    v_s_2644_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__1(v_input_2513_, v___x_2643_);
                    v_imports_2645_ = lean_ctor_get(v_s_2644_, 0);
                    v_pos_2646_ = lean_ctor_get(v_s_2644_, 1);
                    v_badModifier_2647_ = lean_ctor_get_uint8(
                        v_s_2644_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_2648_ = lean_ctor_get(v_s_2644_, 2);
                    v_isModule_2649_ = lean_ctor_get_uint8(
                        v_s_2644_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_2650_ = lean_ctor_get_uint8(
                        v_s_2644_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_2651_ = lean_ctor_get_uint8(
                        v_s_2644_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_2652_ = lean_ctor_get_uint8(
                        v_s_2644_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2696_ = (!lean_is_exclusive(v_s_2644_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2654_ = v_s_2644_;
                        v_isShared_2655_ = v_isSharedCheck_2696_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_2648_);
                        lean_inc(v_pos_2646_);
                        lean_inc(v_imports_2645_);
                        lean_dec(v_s_2644_);
                        v___x_2654_ = lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2696_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_2560_ == 0 {
                    v___x_2561_ = lean_uint32_dec_eq(v___y_2551_, v___x_2546_);
                    v___y_2518_ = v___y_2548_;
                    v___y_2519_ = v___y_2549_;
                    v___y_2520_ = v___y_2552_;
                    v___y_2521_ = v___y_2553_;
                    v___y_2522_ = v___y_2554_;
                    v___y_2523_ = v___y_2555_;
                    v___y_2524_ = v___y_2557_;
                    v___y_2525_ = v___y_2556_;
                    v___y_2526_ = v___y_2558_;
                    v___y_2527_ = v___y_2559_;
                    v___y_2528_ = v___x_2561_;
                    state = 1;
                    continue;
                } else {
                    v___y_2518_ = v___y_2548_;
                    v___y_2519_ = v___y_2549_;
                    v___y_2520_ = v___y_2552_;
                    v___y_2521_ = v___y_2553_;
                    v___y_2522_ = v___y_2554_;
                    v___y_2523_ = v___y_2555_;
                    v___y_2524_ = v___y_2557_;
                    v___y_2525_ = v___y_2556_;
                    v___y_2526_ = v___y_2558_;
                    v___y_2527_ = v___y_2559_;
                    v___y_2528_ = v___y_2550_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_2575_ == 0 {
                    v___x_2576_ = 95;
                    v___x_2577_ = lean_uint32_dec_eq(v___y_2566_, v___x_2576_);
                    if v___x_2577_ == 0 {
                        v___x_2578_ = l_Lean_isLetterLike(v___y_2566_);
                        v___y_2548_ = v___y_2563_;
                        v___y_2549_ = v___y_2564_;
                        v___y_2550_ = v___y_2565_;
                        v___y_2551_ = v___y_2566_;
                        v___y_2552_ = v___y_2567_;
                        v___y_2553_ = v___y_2568_;
                        v___y_2554_ = v___y_2569_;
                        v___y_2555_ = v___y_2570_;
                        v___y_2556_ = v___y_2572_;
                        v___y_2557_ = v___y_2571_;
                        v___y_2558_ = v___y_2573_;
                        v___y_2559_ = v___y_2574_;
                        v___y_2560_ = v___x_2578_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2548_ = v___y_2563_;
                        v___y_2549_ = v___y_2564_;
                        v___y_2550_ = v___y_2565_;
                        v___y_2551_ = v___y_2566_;
                        v___y_2552_ = v___y_2567_;
                        v___y_2553_ = v___y_2568_;
                        v___y_2554_ = v___y_2569_;
                        v___y_2555_ = v___y_2570_;
                        v___y_2556_ = v___y_2572_;
                        v___y_2557_ = v___y_2571_;
                        v___y_2558_ = v___y_2573_;
                        v___y_2559_ = v___y_2574_;
                        v___y_2560_ = v___x_2577_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_2518_ = v___y_2563_;
                    v___y_2519_ = v___y_2564_;
                    v___y_2520_ = v___y_2567_;
                    v___y_2521_ = v___y_2568_;
                    v___y_2522_ = v___y_2569_;
                    v___y_2523_ = v___y_2570_;
                    v___y_2524_ = v___y_2571_;
                    v___y_2525_ = v___y_2572_;
                    v___y_2526_ = v___y_2573_;
                    v___y_2527_ = v___y_2574_;
                    v___y_2528_ = v___y_2565_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_2592_ = 97;
                v___x_2593_ = lean_uint32_dec_le(v___x_2592_, v___y_2583_);
                if v___x_2593_ == 0 {
                    v___y_2563_ = v___y_2580_;
                    v___y_2564_ = v___y_2581_;
                    v___y_2565_ = v___y_2582_;
                    v___y_2566_ = v___y_2583_;
                    v___y_2567_ = v___y_2584_;
                    v___y_2568_ = v___y_2585_;
                    v___y_2569_ = v___y_2586_;
                    v___y_2570_ = v___y_2587_;
                    v___y_2571_ = v___y_2589_;
                    v___y_2572_ = v___y_2588_;
                    v___y_2573_ = v___y_2590_;
                    v___y_2574_ = v___y_2591_;
                    v___y_2575_ = v___x_2593_;
                    state = 4;
                    continue;
                } else {
                    v___x_2594_ = 122;
                    v___x_2595_ = lean_uint32_dec_le(v___y_2583_, v___x_2594_);
                    v___y_2563_ = v___y_2580_;
                    v___y_2564_ = v___y_2581_;
                    v___y_2565_ = v___y_2582_;
                    v___y_2566_ = v___y_2583_;
                    v___y_2567_ = v___y_2584_;
                    v___y_2568_ = v___y_2585_;
                    v___y_2569_ = v___y_2586_;
                    v___y_2570_ = v___y_2587_;
                    v___y_2571_ = v___y_2589_;
                    v___y_2572_ = v___y_2588_;
                    v___y_2573_ = v___y_2590_;
                    v___y_2574_ = v___y_2591_;
                    v___y_2575_ = v___x_2595_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2599_ = lean_string_utf8_next_fast(v_input_2513_, v_pos_2534_);
                if v_isShared_2544_ == 0 {
                    lean_ctor_set(v___x_2543_, 1, v___x_2599_);
                    v___x_2601_ = v___x_2543_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_imports_2533_);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_error_x3f_2536_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2535_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2537_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2538_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2539_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2540_,
                    );
                    v___x_2601_ = v_reuseFailAlloc_2623_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_s_2602_ = l_Lean_ParseImports_takeUntil___at___00__private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse_spec__0(v___y_2598_, v_curr_2545_, v_input_2513_, v___x_2601_);
                v_imports_2603_ = lean_ctor_get(v_s_2602_, 0);
                lean_inc_ref(v_imports_2603_);
                v_pos_2604_ = lean_ctor_get(v_s_2602_, 1);
                lean_inc(v_pos_2604_);
                v_badModifier_2605_ = lean_ctor_get_uint8(
                    v_s_2602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2606_ = lean_ctor_get(v_s_2602_, 2);
                lean_inc(v_error_x3f_2606_);
                v_isModule_2607_ = lean_ctor_get_uint8(
                    v_s_2602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2608_ = lean_ctor_get_uint8(
                    v_s_2602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2609_ = lean_ctor_get_uint8(
                    v_s_2602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2610_ = lean_ctor_get_uint8(
                    v_s_2602_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v___x_2611_ = lean_string_utf8_extract(v_input_2513_, v_pos_2534_, v_pos_2604_);
                lean_dec(v_pos_2534_);
                v_module_2612_ = l_Lean_Name_str___override(v_module_2515_, v___x_2611_);
                v_curr_2613_ = lean_string_utf8_get(v_input_2513_, v_pos_2604_);
                v___x_2614_ = 46;
                v___x_2615_ = lean_uint32_dec_eq(v_curr_2613_, v___x_2614_);
                if v___x_2615_ == 0 {
                    v___y_2518_ = v_pos_2604_;
                    v___y_2519_ = v_module_2612_;
                    v___y_2520_ = v_s_2602_;
                    v___y_2521_ = v_importAll_2610_;
                    v___y_2522_ = v_isMeta_2608_;
                    v___y_2523_ = v_badModifier_2605_;
                    v___y_2524_ = v_isExported_2609_;
                    v___y_2525_ = v_error_x3f_2606_;
                    v___y_2526_ = v_imports_2603_;
                    v___y_2527_ = v_isModule_2607_;
                    v___y_2528_ = v___x_2615_;
                    state = 1;
                    continue;
                } else {
                    v_i_2616_ = lean_string_utf8_next(v_input_2513_, v_pos_2604_);
                    v___x_2617_ = lean_string_utf8_at_end(v_input_2513_, v_i_2616_);
                    if v___x_2617_ == 0 {
                        v_curr_2618_ = lean_string_utf8_get_fast(v_input_2513_, v_i_2616_);
                        lean_dec(v_i_2616_);
                        v___x_2619_ = 65;
                        v___x_2620_ = lean_uint32_dec_le(v___x_2619_, v_curr_2618_);
                        if v___x_2620_ == 0 {
                            v___y_2580_ = v_pos_2604_;
                            v___y_2581_ = v_module_2612_;
                            v___y_2582_ = v___x_2615_;
                            v___y_2583_ = v_curr_2618_;
                            v___y_2584_ = v_s_2602_;
                            v___y_2585_ = v_importAll_2610_;
                            v___y_2586_ = v_isMeta_2608_;
                            v___y_2587_ = v_badModifier_2605_;
                            v___y_2588_ = v_error_x3f_2606_;
                            v___y_2589_ = v_isExported_2609_;
                            v___y_2590_ = v_imports_2603_;
                            v___y_2591_ = v_isModule_2607_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2621_ = 90;
                            v___x_2622_ = lean_uint32_dec_le(v_curr_2618_, v___x_2621_);
                            if v___x_2622_ == 0 {
                                v___y_2580_ = v_pos_2604_;
                                v___y_2581_ = v_module_2612_;
                                v___y_2582_ = v___x_2615_;
                                v___y_2583_ = v_curr_2618_;
                                v___y_2584_ = v_s_2602_;
                                v___y_2585_ = v_importAll_2610_;
                                v___y_2586_ = v_isMeta_2608_;
                                v___y_2587_ = v_badModifier_2605_;
                                v___y_2588_ = v_error_x3f_2606_;
                                v___y_2589_ = v_isExported_2609_;
                                v___y_2590_ = v_imports_2603_;
                                v___y_2591_ = v_isModule_2607_;
                                state = 5;
                                continue;
                            } else {
                                v___y_2518_ = v_pos_2604_;
                                v___y_2519_ = v_module_2612_;
                                v___y_2520_ = v_s_2602_;
                                v___y_2521_ = v_importAll_2610_;
                                v___y_2522_ = v_isMeta_2608_;
                                v___y_2523_ = v_badModifier_2605_;
                                v___y_2524_ = v_isExported_2609_;
                                v___y_2525_ = v_error_x3f_2606_;
                                v___y_2526_ = v_imports_2603_;
                                v___y_2527_ = v_isModule_2607_;
                                v___y_2528_ = v___x_2615_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_i_2616_);
                        v___y_2518_ = v_pos_2604_;
                        v___y_2519_ = v_module_2612_;
                        v___y_2520_ = v_s_2602_;
                        v___y_2521_ = v_importAll_2610_;
                        v___y_2522_ = v_isMeta_2608_;
                        v___y_2523_ = v_badModifier_2605_;
                        v___y_2524_ = v_isExported_2609_;
                        v___y_2525_ = v_error_x3f_2606_;
                        v___y_2526_ = v_imports_2603_;
                        v___y_2527_ = v_isModule_2607_;
                        v___y_2528_ = v___x_2596_;
                        state = 1;
                        continue;
                    }
                }
            }
            8 => {
                if v___y_2625_ == 0 {
                    lean_del_object(v___x_2543_);
                    lean_dec(v_error_x3f_2536_);
                    lean_dec(v_module_2515_);
                    lean_dec_ref(v_finalize_2514_);
                    lean_dec_ref(v_input_2513_);
                    v___x_2626_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__1;
                    v___x_2627_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v___x_2627_, 0, v_imports_2533_);
                    lean_ctor_set(v___x_2627_, 1, v_pos_2534_);
                    lean_ctor_set(v___x_2627_, 2, v___x_2626_);
                    lean_ctor_set_uint8(
                        v___x_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2535_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2537_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2538_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2539_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2627_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2540_,
                    );
                    return v___x_2627_;
                } else {
                    v___y_2598_ = v___y_2625_;
                    state = 6;
                    continue;
                }
            }
            9 => {
                if v___y_2629_ == 0 {
                    v___x_2630_ = 95;
                    v___x_2631_ = lean_uint32_dec_eq(v_curr_2545_, v___x_2630_);
                    if v___x_2631_ == 0 {
                        v___x_2632_ = l_Lean_isLetterLike(v_curr_2545_);
                        v___y_2625_ = v___x_2632_;
                        state = 8;
                        continue;
                    } else {
                        v___y_2625_ = v___x_2631_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_2598_ = v___y_2629_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_2634_ = 97;
                v___x_2635_ = lean_uint32_dec_le(v___x_2634_, v_curr_2545_);
                if v___x_2635_ == 0 {
                    v___y_2629_ = v___x_2635_;
                    state = 9;
                    continue;
                } else {
                    v___x_2636_ = 122;
                    v___x_2637_ = lean_uint32_dec_le(v_curr_2545_, v___x_2636_);
                    v___y_2629_ = v___x_2637_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v___x_2656_ = lean_string_utf8_at_end(v_input_2513_, v_pos_2646_);
                if v___x_2656_ == 0 {
                    v_i_2657_ = lean_string_utf8_next_fast(v_input_2513_, v_pos_2646_);
                    lean_inc(v_error_x3f_2648_);
                    lean_inc_ref(v_imports_2645_);
                    if v_isShared_2655_ == 0 {
                        lean_ctor_set(v___x_2654_, 1, v_i_2657_);
                        v_s_2659_ = v___x_2654_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_imports_2645_);
                        lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_i_2657_);
                        lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_error_x3f_2648_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2691_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2647_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2691_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2649_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2691_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2650_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2691_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2651_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2691_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2652_,
                        );
                        v_s_2659_ = v_reuseFailAlloc_2691_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v_error_x3f_2648_);
                    lean_dec(v_module_2515_);
                    lean_dec_ref(v_finalize_2514_);
                    lean_dec_ref(v_input_2513_);
                    v___x_2692_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse___closed__3;
                    if v_isShared_2655_ == 0 {
                        lean_ctor_set(v___x_2654_, 2, v___x_2692_);
                        v___x_2694_ = v___x_2654_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_imports_2645_);
                        lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_pos_2646_);
                        lean_ctor_set(v_reuseFailAlloc_2695_, 2, v___x_2692_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2695_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2647_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2695_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2649_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2695_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2650_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2695_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2651_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2695_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2652_,
                        );
                        v___x_2694_ = v_reuseFailAlloc_2695_;
                        state = 17;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2660_ =
                    lean_string_utf8_extract(v_input_2513_, v_startPart_2642_, v_pos_2646_);
                lean_dec(v_pos_2646_);
                v_module_2661_ = l_Lean_Name_str___override(v_module_2515_, v___x_2660_);
                v_curr_2668_ = lean_string_utf8_get(v_input_2513_, v_i_2657_);
                v___x_2669_ = 46;
                v___x_2670_ = lean_uint32_dec_eq(v_curr_2668_, v___x_2669_);
                if v___x_2670_ == 0 {
                    v___y_2663_ = v___x_2670_;
                    state = 13;
                    continue;
                } else {
                    v_i_2671_ = lean_string_utf8_next(v_input_2513_, v_i_2657_);
                    v___x_2672_ = lean_string_utf8_at_end(v_input_2513_, v_i_2671_);
                    if v___x_2672_ == 0 {
                        v_curr_2673_ = lean_string_utf8_get_fast(v_input_2513_, v_i_2671_);
                        lean_dec(v_i_2671_);
                        v___x_2687_ = 65;
                        v___x_2688_ = lean_uint32_dec_le(v___x_2687_, v_curr_2673_);
                        if v___x_2688_ == 0 {
                            state = 16;
                            continue;
                        } else {
                            v___x_2689_ = 90;
                            v___x_2690_ = lean_uint32_dec_le(v_curr_2673_, v___x_2689_);
                            if v___x_2690_ == 0 {
                                state = 16;
                                continue;
                            } else {
                                v___y_2663_ = v___x_2670_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_i_2671_);
                        v___y_2663_ = v___x_2656_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v___y_2663_ == 0 {
                    lean_dec(v_error_x3f_2648_);
                    lean_dec_ref(v_imports_2645_);
                    v___x_2664_ =
                        lean_apply_3(v_finalize_2514_, v_module_2661_, v_input_2513_, v_s_2659_);
                    return v___x_2664_;
                } else {
                    lean_dec_ref(v_s_2659_);
                    v___x_2665_ = lean_string_utf8_next(v_input_2513_, v_i_2657_);
                    v_s_2666_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_s_2666_, 0, v_imports_2645_);
                    lean_ctor_set(v_s_2666_, 1, v___x_2665_);
                    lean_ctor_set(v_s_2666_, 2, v_error_x3f_2648_);
                    lean_ctor_set_uint8(
                        v_s_2666_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2647_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2666_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2649_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2666_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2650_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2666_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2651_,
                    );
                    lean_ctor_set_uint8(
                        v_s_2666_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2652_,
                    );
                    v_module_2515_ = v_module_2661_;
                    v_s_2516_ = v_s_2666_;
                    state = 0;
                    continue;
                }
            }
            14 => {
                if v___y_2675_ == 0 {
                    v___x_2676_ = lean_uint32_dec_eq(v_curr_2673_, v___x_2546_);
                    v___y_2663_ = v___x_2676_;
                    state = 13;
                    continue;
                } else {
                    v___y_2663_ = v___x_2670_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                if v___y_2678_ == 0 {
                    v___x_2679_ = 95;
                    v___x_2680_ = lean_uint32_dec_eq(v_curr_2673_, v___x_2679_);
                    if v___x_2680_ == 0 {
                        v___x_2681_ = l_Lean_isLetterLike(v_curr_2673_);
                        v___y_2675_ = v___x_2681_;
                        state = 14;
                        continue;
                    } else {
                        v___y_2675_ = v___x_2680_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___y_2663_ = v___x_2670_;
                    state = 13;
                    continue;
                }
            }
            16 => {
                v___x_2683_ = 97;
                v___x_2684_ = lean_uint32_dec_le(v___x_2683_, v_curr_2673_);
                if v___x_2684_ == 0 {
                    v___y_2678_ = v___x_2684_;
                    state = 15;
                    continue;
                } else {
                    v___x_2685_ = 122;
                    v___x_2686_ = lean_uint32_dec_le(v_curr_2673_, v___x_2685_);
                    v___y_2678_ = v___x_2686_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                return v___x_2694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_moduleIdent___lam__0(
    mut v_module_2702_: *mut LeanObject,
    mut v_input_2703_: *mut LeanObject,
    mut v_s_2704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_2705_: u8 = 0;
    let mut v_isExported_2706_: u8 = 0;
    let mut v_importAll_2707_: u8 = 0;
    let mut v_imp_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2713_: u8 = 0;
    let mut v_error_x3f_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2715_: u8 = 0;
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2719_: u8 = 0;
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isMeta_2705_ = lean_ctor_get_uint8(
                    v_s_2704_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2706_ = lean_ctor_get_uint8(
                    v_s_2704_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2707_ = lean_ctor_get_uint8(
                    v_s_2704_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_imp_2708_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v_imp_2708_, 0, v_module_2702_);
                lean_ctor_set_uint8(
                    v_imp_2708_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_importAll_2707_,
                );
                lean_ctor_set_uint8(
                    v_imp_2708_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isExported_2706_,
                );
                lean_ctor_set_uint8(
                    v_imp_2708_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v_isMeta_2705_,
                );
                v___x_2709_ = l_Lean_ParseImports_State_pushImport(v_imp_2708_, v_s_2704_);
                v_s_2710_ = l_Lean_ParseImports_whitespace(v_input_2703_, v___x_2709_);
                v_imports_2711_ = lean_ctor_get(v_s_2710_, 0);
                v_pos_2712_ = lean_ctor_get(v_s_2710_, 1);
                v_badModifier_2713_ = lean_ctor_get_uint8(
                    v_s_2710_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2714_ = lean_ctor_get(v_s_2710_, 2);
                v_isModule_2715_ = lean_ctor_get_uint8(
                    v_s_2710_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isSharedCheck_2727_ = (!lean_is_exclusive(v_s_2710_)) as u8;
                if v_isSharedCheck_2727_ == 0 {
                    v___x_2717_ = v_s_2710_;
                    v_isShared_2718_ = v_isSharedCheck_2727_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_2714_);
                    lean_inc(v_pos_2712_);
                    lean_inc(v_imports_2711_);
                    lean_dec(v_s_2710_);
                    v___x_2717_ = lean_box(0);
                    v_isShared_2718_ = v_isSharedCheck_2727_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2719_ = 0;
                if v_isModule_2715_ == 0 {
                    v___x_2720_ = 1;
                    if v_isShared_2718_ == 0 {
                        v___x_2722_ = v___x_2717_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_imports_2711_);
                        lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_pos_2712_);
                        lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_error_x3f_2714_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2723_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2713_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2723_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2715_,
                        );
                        v___x_2722_ = v_reuseFailAlloc_2723_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2718_ == 0 {
                        v___x_2725_ = v___x_2717_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_imports_2711_);
                        lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_pos_2712_);
                        lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_error_x3f_2714_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2726_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2713_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2726_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2715_,
                        );
                        v___x_2725_ = v_reuseFailAlloc_2726_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2722_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_2719_,
                );
                lean_ctor_set_uint8(
                    v___x_2722_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v___x_2720_,
                );
                lean_ctor_set_uint8(
                    v___x_2722_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    v___x_2719_,
                );
                return v___x_2722_;
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2725_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_2719_,
                );
                lean_ctor_set_uint8(
                    v___x_2725_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v___x_2719_,
                );
                lean_ctor_set_uint8(
                    v___x_2725_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    v___x_2719_,
                );
                return v___x_2725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_moduleIdent___lam__0___boxed(
    mut v_module_2728_: *mut LeanObject,
    mut v_input_2729_: *mut LeanObject,
    mut v_s_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2731_: *mut LeanObject = core::ptr::null_mut();
    v_res_2731_ =
        l_Lean_ParseImports_moduleIdent___lam__0(v_module_2728_, v_input_2729_, v_s_2730_);
    lean_dec_ref(v_input_2729_);
    return v_res_2731_;
}
pub unsafe fn l_Lean_ParseImports_moduleIdent(
    mut v_input_2733_: *mut LeanObject,
    mut v_s_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finalize_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    v_finalize_2735_ = l_Lean_ParseImports_moduleIdent___closed__0;
    v___x_2736_ = lean_box(0);
    v___x_2737_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_moduleIdent_parse(
        v_input_2733_,
        v_finalize_2735_,
        v___x_2736_,
        v_s_2734_,
    );
    return v___x_2737_;
}
pub unsafe fn l_Lean_ParseImports_atomic(
    mut v_p_2738_: *mut LeanObject,
    mut v_input_2739_: *mut LeanObject,
    mut v_s_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2745_: u8 = 0;
    let mut v_isModule_2746_: u8 = 0;
    let mut v_isMeta_2747_: u8 = 0;
    let mut v_isExported_2748_: u8 = 0;
    let mut v_importAll_2749_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut v_unused_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2741_ = lean_ctor_get(v_s_2740_, 1);
                lean_inc(v_pos_2741_);
                v_s_2742_ = lean_apply_2(v_p_2738_, v_input_2739_, v_s_2740_);
                v_error_x3f_2743_ = lean_ctor_get(v_s_2742_, 2);
                lean_inc(v_error_x3f_2743_);
                if lean_obj_tag(v_error_x3f_2743_) == 1 {
                    v_imports_2744_ = lean_ctor_get(v_s_2742_, 0);
                    v_badModifier_2745_ = lean_ctor_get_uint8(
                        v_s_2742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_isModule_2746_ = lean_ctor_get_uint8(
                        v_s_2742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_2747_ = lean_ctor_get_uint8(
                        v_s_2742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_2748_ = lean_ctor_get_uint8(
                        v_s_2742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_2749_ = lean_ctor_get_uint8(
                        v_s_2742_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2756_ = (!lean_is_exclusive(v_s_2742_)) as u8;
                    if v_isSharedCheck_2756_ == 0 {
                        v_unused_2757_ = lean_ctor_get(v_s_2742_, 2);
                        lean_dec(v_unused_2757_);
                        v_unused_2758_ = lean_ctor_get(v_s_2742_, 1);
                        lean_dec(v_unused_2758_);
                        v___x_2751_ = v_s_2742_;
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_imports_2744_);
                        lean_dec(v_s_2742_);
                        v___x_2751_ = lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_error_x3f_2743_);
                    lean_dec(v_pos_2741_);
                    return v_s_2742_;
                }
            }
            1 => {
                if v_isShared_2752_ == 0 {
                    lean_ctor_set(v___x_2751_, 1, v_pos_2741_);
                    v___x_2754_ = v___x_2751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_imports_2744_);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_pos_2741_);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_error_x3f_2743_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2755_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2745_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2755_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2746_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2755_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2747_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2755_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2748_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2755_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2749_,
                    );
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_manyImports(
    mut v_p_2762_: *mut LeanObject,
    mut v_input_2763_: *mut LeanObject,
    mut v_s_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2770_: u8 = 0;
    let mut v_isMeta_2771_: u8 = 0;
    let mut v_isExported_2772_: u8 = 0;
    let mut v_importAll_2773_: u8 = 0;
    let mut v___x_2774_: u8 = 0;
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_unused_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2787_: u8 = 0;
    let mut v_imports_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2790_: u8 = 0;
    let mut v_isMeta_2791_: u8 = 0;
    let mut v_isExported_2792_: u8 = 0;
    let mut v_importAll_2793_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2802_: u8 = 0;
    let mut v_unused_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2765_ = lean_ctor_get(v_s_2764_, 1);
                lean_inc(v_pos_2765_);
                lean_inc_ref(v_p_2762_);
                lean_inc_ref(v_input_2763_);
                v_s_2766_ = lean_apply_2(v_p_2762_, v_input_2763_, v_s_2764_);
                v_error_x3f_2767_ = lean_ctor_get(v_s_2766_, 2);
                lean_inc(v_error_x3f_2767_);
                if lean_obj_tag(v_error_x3f_2767_) == 1 {
                    lean_dec_ref_known(v_error_x3f_2767_, 1);
                    lean_dec_ref(v_input_2763_);
                    lean_dec_ref(v_p_2762_);
                    v_imports_2768_ = lean_ctor_get(v_s_2766_, 0);
                    lean_inc_ref(v_imports_2768_);
                    v_pos_2769_ = lean_ctor_get(v_s_2766_, 1);
                    lean_inc(v_pos_2769_);
                    v_isModule_2770_ = lean_ctor_get_uint8(
                        v_s_2766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_2771_ = lean_ctor_get_uint8(
                        v_s_2766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_2772_ = lean_ctor_get_uint8(
                        v_s_2766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_2773_ = lean_ctor_get_uint8(
                        v_s_2766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v___x_2774_ = lean_nat_dec_eq(v_pos_2769_, v_pos_2765_);
                    lean_dec(v_pos_2765_);
                    if v___x_2774_ == 0 {
                        lean_dec(v_pos_2769_);
                        lean_dec_ref(v_imports_2768_);
                        return v_s_2766_;
                    } else {
                        v_isSharedCheck_2783_ = (!lean_is_exclusive(v_s_2766_)) as u8;
                        if v_isSharedCheck_2783_ == 0 {
                            v_unused_2784_ = lean_ctor_get(v_s_2766_, 2);
                            lean_dec(v_unused_2784_);
                            v_unused_2785_ = lean_ctor_get(v_s_2766_, 1);
                            lean_dec(v_unused_2785_);
                            v_unused_2786_ = lean_ctor_get(v_s_2766_, 0);
                            lean_dec(v_unused_2786_);
                            v___x_2776_ = v_s_2766_;
                            v_isShared_2777_ = v_isSharedCheck_2783_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2766_);
                            v___x_2776_ = lean_box(0);
                            v_isShared_2777_ = v_isSharedCheck_2783_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_error_x3f_2767_);
                    v_badModifier_2787_ = lean_ctor_get_uint8(
                        v_s_2766_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_badModifier_2787_ == 0 {
                        lean_dec(v_pos_2765_);
                        v_s_2764_ = v_s_2766_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_input_2763_);
                        lean_dec_ref(v_p_2762_);
                        v_imports_2789_ = lean_ctor_get(v_s_2766_, 0);
                        v_isModule_2790_ = lean_ctor_get_uint8(
                            v_s_2766_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_isMeta_2791_ = lean_ctor_get_uint8(
                            v_s_2766_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        );
                        v_isExported_2792_ = lean_ctor_get_uint8(
                            v_s_2766_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        );
                        v_importAll_2793_ = lean_ctor_get_uint8(
                            v_s_2766_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        );
                        v_isSharedCheck_2802_ = (!lean_is_exclusive(v_s_2766_)) as u8;
                        if v_isSharedCheck_2802_ == 0 {
                            v_unused_2803_ = lean_ctor_get(v_s_2766_, 2);
                            lean_dec(v_unused_2803_);
                            v_unused_2804_ = lean_ctor_get(v_s_2766_, 1);
                            lean_dec(v_unused_2804_);
                            v___x_2795_ = v_s_2766_;
                            v_isShared_2796_ = v_isSharedCheck_2802_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_imports_2789_);
                            lean_dec(v_s_2766_);
                            v___x_2795_ = lean_box(0);
                            v_isShared_2796_ = v_isSharedCheck_2802_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2778_ = 0;
                v___x_2779_ = lean_box(0);
                if v_isShared_2777_ == 0 {
                    lean_ctor_set(v___x_2776_, 2, v___x_2779_);
                    v___x_2781_ = v___x_2776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_imports_2768_);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_pos_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 2, v___x_2779_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2782_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2770_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2782_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2771_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2782_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2772_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2782_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2773_,
                    );
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2781_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2778_,
                );
                return v___x_2781_;
            }
            3 => {
                v___x_2797_ = 0;
                v___x_2798_ = l_Lean_ParseImports_manyImports___closed__1;
                if v_isShared_2796_ == 0 {
                    lean_ctor_set(v___x_2795_, 2, v___x_2798_);
                    lean_ctor_set(v___x_2795_, 1, v_pos_2765_);
                    v___x_2800_ = v___x_2795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_imports_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_pos_2765_);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 2, v___x_2798_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2790_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2791_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2792_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2801_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2793_,
                    );
                    v___x_2800_ = v_reuseFailAlloc_2801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_2800_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2797_,
                );
                return v___x_2800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_setIsModule___redArg(
    mut v_isModule_2805_: u8,
    mut v_s_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2809_: u8 = 0;
    let mut v_error_x3f_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isMeta_2811_: u8 = 0;
    let mut v_importAll_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_imports_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2823_: u8 = 0;
    let mut v_error_x3f_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isMeta_2825_: u8 = 0;
    let mut v_importAll_2826_: u8 = 0;
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_isModule_2805_ == 0 {
                    v_imports_2807_ = lean_ctor_get(v_s_2806_, 0);
                    v_pos_2808_ = lean_ctor_get(v_s_2806_, 1);
                    v_badModifier_2809_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_2810_ = lean_ctor_get(v_s_2806_, 2);
                    v_isMeta_2811_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_importAll_2812_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2820_ = (!lean_is_exclusive(v_s_2806_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v___x_2814_ = v_s_2806_;
                        v_isShared_2815_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_2810_);
                        lean_inc(v_pos_2808_);
                        lean_inc(v_imports_2807_);
                        lean_dec(v_s_2806_);
                        v___x_2814_ = lean_box(0);
                        v_isShared_2815_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_imports_2821_ = lean_ctor_get(v_s_2806_, 0);
                    v_pos_2822_ = lean_ctor_get(v_s_2806_, 1);
                    v_badModifier_2823_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_2824_ = lean_ctor_get(v_s_2806_, 2);
                    v_isMeta_2825_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_importAll_2826_ = lean_ctor_get_uint8(
                        v_s_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2834_ = (!lean_is_exclusive(v_s_2806_)) as u8;
                    if v_isSharedCheck_2834_ == 0 {
                        v___x_2828_ = v_s_2806_;
                        v_isShared_2829_ = v_isSharedCheck_2834_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_2824_);
                        lean_inc(v_pos_2822_);
                        lean_inc(v_imports_2821_);
                        lean_dec(v_s_2806_);
                        v___x_2828_ = lean_box(0);
                        v_isShared_2829_ = v_isSharedCheck_2834_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2816_ = 1;
                if v_isShared_2815_ == 0 {
                    v___x_2818_ = v___x_2814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_imports_2807_);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_pos_2808_);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_error_x3f_2810_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2819_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2809_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2819_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2811_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2819_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2812_,
                    );
                    v___x_2818_ = v_reuseFailAlloc_2819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2818_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_isModule_2805_,
                );
                lean_ctor_set_uint8(
                    v___x_2818_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v___x_2816_,
                );
                return v___x_2818_;
            }
            3 => {
                v___x_2830_ = 0;
                if v_isShared_2829_ == 0 {
                    v___x_2832_ = v___x_2828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_imports_2821_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_pos_2822_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_error_x3f_2824_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2833_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2823_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2833_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2825_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2833_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2826_,
                    );
                    v___x_2832_ = v_reuseFailAlloc_2833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_2832_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_isModule_2805_,
                );
                lean_ctor_set_uint8(
                    v___x_2832_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v___x_2830_,
                );
                return v___x_2832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_setIsModule___redArg___boxed(
    mut v_isModule_2835_: *mut LeanObject,
    mut v_s_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isModule_boxed_2837_: u8 = 0;
    let mut v_res_2838_: *mut LeanObject = core::ptr::null_mut();
    v_isModule_boxed_2837_ = (lean_unbox(v_isModule_2835_) as u8);
    v_res_2838_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_boxed_2837_, v_s_2836_);
    return v_res_2838_;
}
pub unsafe fn l_Lean_ParseImports_setIsModule(
    mut v_isModule_2839_: u8,
    mut v_x_2840_: *mut LeanObject,
    mut v_s_2841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    v___x_2842_ = l_Lean_ParseImports_setIsModule___redArg(v_isModule_2839_, v_s_2841_);
    return v___x_2842_;
}
pub unsafe fn l_Lean_ParseImports_setIsModule___boxed(
    mut v_isModule_2843_: *mut LeanObject,
    mut v_x_2844_: *mut LeanObject,
    mut v_s_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isModule_boxed_2846_: u8 = 0;
    let mut v_res_2847_: *mut LeanObject = core::ptr::null_mut();
    v_isModule_boxed_2846_ = (lean_unbox(v_isModule_2843_) as u8);
    v_res_2847_ = l_Lean_ParseImports_setIsModule(v_isModule_boxed_2846_, v_x_2844_, v_s_2845_);
    lean_dec_ref(v_x_2844_);
    return v_res_2847_;
}
pub unsafe fn l_Lean_ParseImports_setMeta___redArg(
    mut v_s_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2851_: u8 = 0;
    let mut v_error_x3f_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2853_: u8 = 0;
    let mut v_isMeta_2854_: u8 = 0;
    let mut v_isExported_2855_: u8 = 0;
    let mut v_importAll_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2849_ = lean_ctor_get(v_s_2848_, 0);
                v_pos_2850_ = lean_ctor_get(v_s_2848_, 1);
                v_badModifier_2851_ = lean_ctor_get_uint8(
                    v_s_2848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2852_ = lean_ctor_get(v_s_2848_, 2);
                v_isModule_2853_ = lean_ctor_get_uint8(
                    v_s_2848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2854_ = lean_ctor_get_uint8(
                    v_s_2848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2855_ = lean_ctor_get_uint8(
                    v_s_2848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2856_ = lean_ctor_get_uint8(
                    v_s_2848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2867_ = (!lean_is_exclusive(v_s_2848_)) as u8;
                if v_isSharedCheck_2867_ == 0 {
                    v___x_2858_ = v_s_2848_;
                    v_isShared_2859_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_2852_);
                    lean_inc(v_pos_2850_);
                    lean_inc(v_imports_2849_);
                    lean_dec(v_s_2848_);
                    v___x_2858_ = lean_box(0);
                    v_isShared_2859_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2860_ = 1;
                if v_isModule_2853_ == 0 {
                    if v_isShared_2859_ == 0 {
                        v___x_2862_ = v___x_2858_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_imports_2849_);
                        lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_pos_2850_);
                        lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_error_x3f_2852_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2863_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2853_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2863_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2854_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2863_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2855_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2863_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2856_,
                        );
                        v___x_2862_ = v_reuseFailAlloc_2863_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2859_ == 0 {
                        v___x_2865_ = v___x_2858_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_imports_2849_);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_pos_2850_);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_error_x3f_2852_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2866_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2851_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2866_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2853_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2866_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2855_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2866_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2856_,
                        );
                        v___x_2865_ = v_reuseFailAlloc_2866_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2862_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2860_,
                );
                return v___x_2862_;
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2865_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_2860_,
                );
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_setMeta(
    mut v_x_2868_: *mut LeanObject,
    mut v_s_2869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    v___x_2870_ = l_Lean_ParseImports_setMeta___redArg(v_s_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_ParseImports_setMeta___boxed(
    mut v_x_2871_: *mut LeanObject,
    mut v_s_2872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2873_: *mut LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Lean_ParseImports_setMeta(v_x_2871_, v_s_2872_);
    lean_dec_ref(v_x_2871_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_ParseImports_setExported___redArg(
    mut v_s_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2877_: u8 = 0;
    let mut v_error_x3f_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2879_: u8 = 0;
    let mut v_isMeta_2880_: u8 = 0;
    let mut v_isExported_2881_: u8 = 0;
    let mut v_importAll_2882_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2875_ = lean_ctor_get(v_s_2874_, 0);
                v_pos_2876_ = lean_ctor_get(v_s_2874_, 1);
                v_badModifier_2877_ = lean_ctor_get_uint8(
                    v_s_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2878_ = lean_ctor_get(v_s_2874_, 2);
                v_isModule_2879_ = lean_ctor_get_uint8(
                    v_s_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2880_ = lean_ctor_get_uint8(
                    v_s_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2881_ = lean_ctor_get_uint8(
                    v_s_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2882_ = lean_ctor_get_uint8(
                    v_s_2874_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2893_ = (!lean_is_exclusive(v_s_2874_)) as u8;
                if v_isSharedCheck_2893_ == 0 {
                    v___x_2884_ = v_s_2874_;
                    v_isShared_2885_ = v_isSharedCheck_2893_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_2878_);
                    lean_inc(v_pos_2876_);
                    lean_inc(v_imports_2875_);
                    lean_dec(v_s_2874_);
                    v___x_2884_ = lean_box(0);
                    v_isShared_2885_ = v_isSharedCheck_2893_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2886_ = 1;
                if v_isModule_2879_ == 0 {
                    if v_isShared_2885_ == 0 {
                        v___x_2888_ = v___x_2884_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_imports_2875_);
                        lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_pos_2876_);
                        lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_error_x3f_2878_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2889_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2879_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2889_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2880_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2889_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2881_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2889_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2882_,
                        );
                        v___x_2888_ = v_reuseFailAlloc_2889_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2885_ == 0 {
                        v___x_2891_ = v___x_2884_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_imports_2875_);
                        lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_pos_2876_);
                        lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_error_x3f_2878_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2892_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2877_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2892_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2879_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2892_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2880_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2892_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2882_,
                        );
                        v___x_2891_ = v_reuseFailAlloc_2892_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2888_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2886_,
                );
                return v___x_2888_;
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2891_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    v___x_2886_,
                );
                return v___x_2891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_setExported(
    mut v_x_2894_: *mut LeanObject,
    mut v_s_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_ParseImports_setExported___redArg(v_s_2895_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_ParseImports_setExported___boxed(
    mut v_x_2897_: *mut LeanObject,
    mut v_s_2898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2899_: *mut LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Lean_ParseImports_setExported(v_x_2897_, v_s_2898_);
    lean_dec_ref(v_x_2897_);
    return v_res_2899_;
}
pub unsafe fn l_Lean_ParseImports_setImportAll___redArg(
    mut v_s_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2903_: u8 = 0;
    let mut v_error_x3f_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2905_: u8 = 0;
    let mut v_isMeta_2906_: u8 = 0;
    let mut v_isExported_2907_: u8 = 0;
    let mut v_importAll_2908_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_2901_ = lean_ctor_get(v_s_2900_, 0);
                v_pos_2902_ = lean_ctor_get(v_s_2900_, 1);
                v_badModifier_2903_ = lean_ctor_get_uint8(
                    v_s_2900_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_error_x3f_2904_ = lean_ctor_get(v_s_2900_, 2);
                v_isModule_2905_ = lean_ctor_get_uint8(
                    v_s_2900_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2906_ = lean_ctor_get_uint8(
                    v_s_2900_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2907_ = lean_ctor_get_uint8(
                    v_s_2900_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2908_ = lean_ctor_get_uint8(
                    v_s_2900_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2919_ = (!lean_is_exclusive(v_s_2900_)) as u8;
                if v_isSharedCheck_2919_ == 0 {
                    v___x_2910_ = v_s_2900_;
                    v_isShared_2911_ = v_isSharedCheck_2919_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_error_x3f_2904_);
                    lean_inc(v_pos_2902_);
                    lean_inc(v_imports_2901_);
                    lean_dec(v_s_2900_);
                    v___x_2910_ = lean_box(0);
                    v_isShared_2911_ = v_isSharedCheck_2919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2912_ = 1;
                if v_isModule_2905_ == 0 {
                    if v_isShared_2911_ == 0 {
                        v___x_2914_ = v___x_2910_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_imports_2901_);
                        lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_pos_2902_);
                        lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_error_x3f_2904_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2915_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2905_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2915_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2906_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2915_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2907_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2915_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v_importAll_2908_,
                        );
                        v___x_2914_ = v_reuseFailAlloc_2915_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2911_ == 0 {
                        v___x_2917_ = v___x_2910_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 3, (5) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_imports_2901_);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_pos_2902_);
                        lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_error_x3f_2904_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2918_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_badModifier_2903_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2918_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_isModule_2905_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2918_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v_isMeta_2906_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2918_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_isExported_2907_,
                        );
                        v___x_2917_ = v_reuseFailAlloc_2918_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2914_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2912_,
                );
                return v___x_2914_;
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_2917_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    v___x_2912_,
                );
                return v___x_2917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParseImports_setImportAll(
    mut v_x_2920_: *mut LeanObject,
    mut v_s_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    v___x_2922_ = l_Lean_ParseImports_setImportAll___redArg(v_s_2921_);
    return v___x_2922_;
}
pub unsafe fn l_Lean_ParseImports_setImportAll___boxed(
    mut v_x_2923_: *mut LeanObject,
    mut v_s_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2925_: *mut LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Lean_ParseImports_setImportAll(v_x_2923_, v_s_2924_);
    lean_dec_ref(v_x_2923_);
    return v_res_2925_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(
    mut v_k_2929_: *mut LeanObject,
    mut v_input_2930_: *mut LeanObject,
    mut v_s_2931_: *mut LeanObject,
    mut v_i_2932_: *mut LeanObject,
    mut v_j_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2935_: u8 = 0;
    let mut v_s_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: u8 = 0;
    let mut v_curr_u2081_2944_: u32 = 0;
    let mut v_curr_u2082_2945_: u32 = 0;
    let mut v___x_2946_: u8 = 0;
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2951_: u8 = 0;
    let mut v_error_x3f_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_2953_: u8 = 0;
    let mut v_isMeta_2954_: u8 = 0;
    let mut v_isExported_2955_: u8 = 0;
    let mut v_importAll_2956_: u8 = 0;
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_unused_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2934_ = lean_string_utf8_at_end(v_k_2929_, v_i_2932_);
                if v___x_2934_ == 0 {
                    v___x_2935_ = 1;
                    v___x_2943_ = lean_string_utf8_at_end(v_input_2930_, v_j_2933_);
                    if v___x_2943_ == 0 {
                        v_curr_u2081_2944_ = lean_string_utf8_get_fast(v_k_2929_, v_i_2932_);
                        v_curr_u2082_2945_ = lean_string_utf8_get_fast(v_input_2930_, v_j_2933_);
                        v___x_2946_ = lean_uint32_dec_eq(v_curr_u2081_2944_, v_curr_u2082_2945_);
                        if v___x_2946_ == 0 {
                            lean_dec(v_j_2933_);
                            lean_dec(v_i_2932_);
                            v_s_2937_ = v_s_2931_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_2943_ == 0 {
                                v___x_2947_ = lean_string_utf8_next_fast(v_k_2929_, v_i_2932_);
                                lean_dec(v_i_2932_);
                                v___x_2948_ = lean_string_utf8_next_fast(v_input_2930_, v_j_2933_);
                                lean_dec(v_j_2933_);
                                v_i_2932_ = v___x_2947_;
                                v_j_2933_ = v___x_2948_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_2933_);
                                lean_dec(v_i_2932_);
                                v_s_2937_ = v_s_2931_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_j_2933_);
                        lean_dec(v_i_2932_);
                        v_s_2937_ = v_s_2931_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_i_2932_);
                    v_imports_2950_ = lean_ctor_get(v_s_2931_, 0);
                    v_badModifier_2951_ = lean_ctor_get_uint8(
                        v_s_2931_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_2952_ = lean_ctor_get(v_s_2931_, 2);
                    v_isModule_2953_ = lean_ctor_get_uint8(
                        v_s_2931_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_2954_ = lean_ctor_get_uint8(
                        v_s_2931_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_2955_ = lean_ctor_get_uint8(
                        v_s_2931_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_2956_ = lean_ctor_get_uint8(
                        v_s_2931_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_2964_ = (!lean_is_exclusive(v_s_2931_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v_unused_2965_ = lean_ctor_get(v_s_2931_, 1);
                        lean_dec(v_unused_2965_);
                        v___x_2958_ = v_s_2931_;
                        v_isShared_2959_ = v_isSharedCheck_2964_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_2952_);
                        lean_inc(v_imports_2950_);
                        lean_dec(v_s_2931_);
                        v___x_2958_ = lean_box(0);
                        v_isShared_2959_ = v_isSharedCheck_2964_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2938_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___closed__1;
                v___x_2939_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v___x_2939_, 0, v___x_2938_);
                lean_ctor_set_uint8(
                    v___x_2939_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2934_,
                );
                lean_ctor_set_uint8(
                    v___x_2939_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_2935_,
                );
                lean_ctor_set_uint8(
                    v___x_2939_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_2935_,
                );
                v___x_2940_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v___x_2940_, 0, v___x_2938_);
                lean_ctor_set_uint8(
                    v___x_2940_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2934_,
                );
                lean_ctor_set_uint8(
                    v___x_2940_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_2935_,
                );
                lean_ctor_set_uint8(
                    v___x_2940_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_2934_,
                );
                v___x_2941_ = l_Lean_ParseImports_State_pushImport(v___x_2940_, v_s_2937_);
                v___x_2942_ = l_Lean_ParseImports_State_pushImport(v___x_2939_, v___x_2941_);
                return v___x_2942_;
            }
            2 => {
                if v_isShared_2959_ == 0 {
                    lean_ctor_set(v___x_2958_, 1, v_j_2933_);
                    v___x_2961_ = v___x_2958_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_imports_2950_);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_j_2933_);
                    lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_error_x3f_2952_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2963_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2951_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2963_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2953_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2963_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2954_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2963_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2955_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2963_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2956_,
                    );
                    v___x_2961_ = v_reuseFailAlloc_2963_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2962_ = l_Lean_ParseImports_whitespace(v_input_2930_, v___x_2961_);
                return v___x_2962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1___boxed(
    mut v_k_2966_: *mut LeanObject,
    mut v_input_2967_: *mut LeanObject,
    mut v_s_2968_: *mut LeanObject,
    mut v_i_2969_: *mut LeanObject,
    mut v_j_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2971_: *mut LeanObject = core::ptr::null_mut();
    v_res_2971_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v_k_2966_, v_input_2967_, v_s_2968_, v_i_2969_, v_j_2970_);
    lean_dec_ref(v_input_2967_);
    lean_dec_ref(v_k_2966_);
    return v_res_2971_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(
    mut v_k_2975_: *mut LeanObject,
    mut v_input_2976_: *mut LeanObject,
    mut v_s_2977_: *mut LeanObject,
    mut v_i_2978_: *mut LeanObject,
    mut v_j_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_2984_: u8 = 0;
    let mut v_isModule_2985_: u8 = 0;
    let mut v_isMeta_2986_: u8 = 0;
    let mut v_isExported_2987_: u8 = 0;
    let mut v_importAll_2988_: u8 = 0;
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_unused_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: u8 = 0;
    let mut v_curr_u2081_3000_: u32 = 0;
    let mut v_curr_u2082_3001_: u32 = 0;
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3007_: u8 = 0;
    let mut v_error_x3f_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3009_: u8 = 0;
    let mut v_isMeta_3010_: u8 = 0;
    let mut v_isExported_3011_: u8 = 0;
    let mut v_importAll_3012_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_unused_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2998_ = lean_string_utf8_at_end(v_k_2975_, v_i_2978_);
                if v___x_2998_ == 0 {
                    v___x_2999_ = lean_string_utf8_at_end(v_input_2976_, v_j_2979_);
                    if v___x_2999_ == 0 {
                        v_curr_u2081_3000_ = lean_string_utf8_get_fast(v_k_2975_, v_i_2978_);
                        v_curr_u2082_3001_ = lean_string_utf8_get_fast(v_input_2976_, v_j_2979_);
                        v___x_3002_ = lean_uint32_dec_eq(v_curr_u2081_3000_, v_curr_u2082_3001_);
                        if v___x_3002_ == 0 {
                            lean_dec(v_j_2979_);
                            lean_dec(v_i_2978_);
                            v_s_2981_ = v_s_2977_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_2999_ == 0 {
                                v___x_3003_ = lean_string_utf8_next_fast(v_k_2975_, v_i_2978_);
                                lean_dec(v_i_2978_);
                                v___x_3004_ = lean_string_utf8_next_fast(v_input_2976_, v_j_2979_);
                                lean_dec(v_j_2979_);
                                v_i_2978_ = v___x_3003_;
                                v_j_2979_ = v___x_3004_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_2979_);
                                lean_dec(v_i_2978_);
                                v_s_2981_ = v_s_2977_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_j_2979_);
                        lean_dec(v_i_2978_);
                        v_s_2981_ = v_s_2977_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_i_2978_);
                    v_imports_3006_ = lean_ctor_get(v_s_2977_, 0);
                    v_badModifier_3007_ = lean_ctor_get_uint8(
                        v_s_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_3008_ = lean_ctor_get(v_s_2977_, 2);
                    v_isModule_3009_ = lean_ctor_get_uint8(
                        v_s_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3010_ = lean_ctor_get_uint8(
                        v_s_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3011_ = lean_ctor_get_uint8(
                        v_s_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3012_ = lean_ctor_get_uint8(
                        v_s_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3020_ = (!lean_is_exclusive(v_s_2977_)) as u8;
                    if v_isSharedCheck_3020_ == 0 {
                        v_unused_3021_ = lean_ctor_get(v_s_2977_, 1);
                        lean_dec(v_unused_3021_);
                        v___x_3014_ = v_s_2977_;
                        v_isShared_3015_ = v_isSharedCheck_3020_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_3008_);
                        lean_inc(v_imports_3006_);
                        lean_dec(v_s_2977_);
                        v___x_3014_ = lean_box(0);
                        v_isShared_3015_ = v_isSharedCheck_3020_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_imports_2982_ = lean_ctor_get(v_s_2981_, 0);
                v_pos_2983_ = lean_ctor_get(v_s_2981_, 1);
                v_badModifier_2984_ = lean_ctor_get_uint8(
                    v_s_2981_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isModule_2985_ = lean_ctor_get_uint8(
                    v_s_2981_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_isMeta_2986_ = lean_ctor_get_uint8(
                    v_s_2981_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_isExported_2987_ = lean_ctor_get_uint8(
                    v_s_2981_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v_importAll_2988_ = lean_ctor_get_uint8(
                    v_s_2981_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                );
                v_isSharedCheck_2996_ = (!lean_is_exclusive(v_s_2981_)) as u8;
                if v_isSharedCheck_2996_ == 0 {
                    v_unused_2997_ = lean_ctor_get(v_s_2981_, 2);
                    lean_dec(v_unused_2997_);
                    v___x_2990_ = v_s_2981_;
                    v_isShared_2991_ = v_isSharedCheck_2996_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_pos_2983_);
                    lean_inc(v_imports_2982_);
                    lean_dec(v_s_2981_);
                    v___x_2990_ = lean_box(0);
                    v_isShared_2991_ = v_isSharedCheck_2996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2992_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___closed__1;
                if v_isShared_2991_ == 0 {
                    lean_ctor_set(v___x_2990_, 2, v___x_2992_);
                    v___x_2994_ = v___x_2990_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_imports_2982_);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_pos_2983_);
                    lean_ctor_set(v_reuseFailAlloc_2995_, 2, v___x_2992_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_2984_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_2985_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_2986_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_2987_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_2988_,
                    );
                    v___x_2994_ = v_reuseFailAlloc_2995_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2994_;
            }
            4 => {
                if v_isShared_3015_ == 0 {
                    lean_ctor_set(v___x_3014_, 1, v_j_2979_);
                    v___x_3017_ = v___x_3014_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_imports_3006_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_j_2979_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_error_x3f_3008_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3007_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3009_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3010_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3011_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3012_,
                    );
                    v___x_3017_ = v_reuseFailAlloc_3019_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3018_ = l_Lean_ParseImports_whitespace(v_input_2976_, v___x_3017_);
                return v___x_3018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5___boxed(
    mut v_k_3022_: *mut LeanObject,
    mut v_input_3023_: *mut LeanObject,
    mut v_s_3024_: *mut LeanObject,
    mut v_i_3025_: *mut LeanObject,
    mut v_j_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3027_: *mut LeanObject = core::ptr::null_mut();
    v_res_3027_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v_k_3022_, v_input_3023_, v_s_3024_, v_i_3025_, v_j_3026_);
    lean_dec_ref(v_input_3023_);
    lean_dec_ref(v_k_3022_);
    return v_res_3027_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(
    mut v_k_3028_: *mut LeanObject,
    mut v_input_3029_: *mut LeanObject,
    mut v_s_3030_: *mut LeanObject,
    mut v_i_3031_: *mut LeanObject,
    mut v_j_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: u8 = 0;
    let mut v_curr_u2081_3035_: u32 = 0;
    let mut v_curr_u2082_3036_: u32 = 0;
    let mut v___x_3037_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3042_: u8 = 0;
    let mut v_error_x3f_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3044_: u8 = 0;
    let mut v_isMeta_3045_: u8 = 0;
    let mut v_isExported_3046_: u8 = 0;
    let mut v_importAll_3047_: u8 = 0;
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v_unused_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3033_ = lean_string_utf8_at_end(v_k_3028_, v_i_3031_);
                if v___x_3033_ == 0 {
                    v___x_3034_ = lean_string_utf8_at_end(v_input_3029_, v_j_3032_);
                    if v___x_3034_ == 0 {
                        v_curr_u2081_3035_ = lean_string_utf8_get_fast(v_k_3028_, v_i_3031_);
                        v_curr_u2082_3036_ = lean_string_utf8_get_fast(v_input_3029_, v_j_3032_);
                        v___x_3037_ = lean_uint32_dec_eq(v_curr_u2081_3035_, v_curr_u2082_3036_);
                        if v___x_3037_ == 0 {
                            lean_dec(v_j_3032_);
                            lean_dec(v_i_3031_);
                            return v_s_3030_;
                        } else {
                            if v___x_3034_ == 0 {
                                v___x_3038_ = lean_string_utf8_next_fast(v_k_3028_, v_i_3031_);
                                lean_dec(v_i_3031_);
                                v___x_3039_ = lean_string_utf8_next_fast(v_input_3029_, v_j_3032_);
                                lean_dec(v_j_3032_);
                                v_i_3031_ = v___x_3038_;
                                v_j_3032_ = v___x_3039_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_3032_);
                                lean_dec(v_i_3031_);
                                return v_s_3030_;
                            }
                        }
                    } else {
                        lean_dec(v_j_3032_);
                        lean_dec(v_i_3031_);
                        return v_s_3030_;
                    }
                } else {
                    lean_dec(v_i_3031_);
                    v_imports_3041_ = lean_ctor_get(v_s_3030_, 0);
                    v_badModifier_3042_ = lean_ctor_get_uint8(
                        v_s_3030_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_3043_ = lean_ctor_get(v_s_3030_, 2);
                    v_isModule_3044_ = lean_ctor_get_uint8(
                        v_s_3030_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3045_ = lean_ctor_get_uint8(
                        v_s_3030_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3046_ = lean_ctor_get_uint8(
                        v_s_3030_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3047_ = lean_ctor_get_uint8(
                        v_s_3030_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3056_ = (!lean_is_exclusive(v_s_3030_)) as u8;
                    if v_isSharedCheck_3056_ == 0 {
                        v_unused_3057_ = lean_ctor_get(v_s_3030_, 1);
                        lean_dec(v_unused_3057_);
                        v___x_3049_ = v_s_3030_;
                        v_isShared_3050_ = v_isSharedCheck_3056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_3043_);
                        lean_inc(v_imports_3041_);
                        lean_dec(v_s_3030_);
                        v___x_3049_ = lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3050_ == 0 {
                    lean_ctor_set(v___x_3049_, 1, v_j_3032_);
                    v___x_3052_ = v___x_3049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_imports_3041_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_j_3032_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_error_x3f_3043_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3042_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3044_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3045_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3046_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3055_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3047_,
                    );
                    v___x_3052_ = v_reuseFailAlloc_3055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3053_ = l_Lean_ParseImports_whitespace(v_input_3029_, v___x_3052_);
                v___x_3054_ = l_Lean_ParseImports_setImportAll___redArg(v___x_3053_);
                return v___x_3054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2___boxed(
    mut v_k_3058_: *mut LeanObject,
    mut v_input_3059_: *mut LeanObject,
    mut v_s_3060_: *mut LeanObject,
    mut v_i_3061_: *mut LeanObject,
    mut v_j_3062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3063_: *mut LeanObject = core::ptr::null_mut();
    v_res_3063_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v_k_3058_, v_input_3059_, v_s_3060_, v_i_3061_, v_j_3062_);
    lean_dec_ref(v_input_3059_);
    lean_dec_ref(v_k_3058_);
    return v_res_3063_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(
    mut v_k_3064_: *mut LeanObject,
    mut v_input_3065_: *mut LeanObject,
    mut v_s_3066_: *mut LeanObject,
    mut v_i_3067_: *mut LeanObject,
    mut v_j_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: u8 = 0;
    let mut v_curr_u2081_3071_: u32 = 0;
    let mut v_curr_u2082_3072_: u32 = 0;
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3078_: u8 = 0;
    let mut v_error_x3f_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3080_: u8 = 0;
    let mut v_isMeta_3081_: u8 = 0;
    let mut v_isExported_3082_: u8 = 0;
    let mut v_importAll_3083_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3086_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_unused_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3069_ = lean_string_utf8_at_end(v_k_3064_, v_i_3067_);
                if v___x_3069_ == 0 {
                    v___x_3070_ = lean_string_utf8_at_end(v_input_3065_, v_j_3068_);
                    if v___x_3070_ == 0 {
                        v_curr_u2081_3071_ = lean_string_utf8_get_fast(v_k_3064_, v_i_3067_);
                        v_curr_u2082_3072_ = lean_string_utf8_get_fast(v_input_3065_, v_j_3068_);
                        v___x_3073_ = lean_uint32_dec_eq(v_curr_u2081_3071_, v_curr_u2082_3072_);
                        if v___x_3073_ == 0 {
                            lean_dec(v_j_3068_);
                            lean_dec(v_i_3067_);
                            return v_s_3066_;
                        } else {
                            if v___x_3070_ == 0 {
                                v___x_3074_ = lean_string_utf8_next_fast(v_k_3064_, v_i_3067_);
                                lean_dec(v_i_3067_);
                                v___x_3075_ = lean_string_utf8_next_fast(v_input_3065_, v_j_3068_);
                                lean_dec(v_j_3068_);
                                v_i_3067_ = v___x_3074_;
                                v_j_3068_ = v___x_3075_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_3068_);
                                lean_dec(v_i_3067_);
                                return v_s_3066_;
                            }
                        }
                    } else {
                        lean_dec(v_j_3068_);
                        lean_dec(v_i_3067_);
                        return v_s_3066_;
                    }
                } else {
                    lean_dec(v_i_3067_);
                    v_imports_3077_ = lean_ctor_get(v_s_3066_, 0);
                    v_badModifier_3078_ = lean_ctor_get_uint8(
                        v_s_3066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_3079_ = lean_ctor_get(v_s_3066_, 2);
                    v_isModule_3080_ = lean_ctor_get_uint8(
                        v_s_3066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3081_ = lean_ctor_get_uint8(
                        v_s_3066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3082_ = lean_ctor_get_uint8(
                        v_s_3066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3083_ = lean_ctor_get_uint8(
                        v_s_3066_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3092_ = (!lean_is_exclusive(v_s_3066_)) as u8;
                    if v_isSharedCheck_3092_ == 0 {
                        v_unused_3093_ = lean_ctor_get(v_s_3066_, 1);
                        lean_dec(v_unused_3093_);
                        v___x_3085_ = v_s_3066_;
                        v_isShared_3086_ = v_isSharedCheck_3092_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_3079_);
                        lean_inc(v_imports_3077_);
                        lean_dec(v_s_3066_);
                        v___x_3085_ = lean_box(0);
                        v_isShared_3086_ = v_isSharedCheck_3092_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3086_ == 0 {
                    lean_ctor_set(v___x_3085_, 1, v_j_3068_);
                    v___x_3088_ = v___x_3085_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_imports_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_j_3068_);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_error_x3f_3079_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3078_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3080_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3081_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3082_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3083_,
                    );
                    v___x_3088_ = v_reuseFailAlloc_3091_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3089_ = l_Lean_ParseImports_whitespace(v_input_3065_, v___x_3088_);
                v___x_3090_ = l_Lean_ParseImports_setExported___redArg(v___x_3089_);
                return v___x_3090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3___boxed(
    mut v_k_3094_: *mut LeanObject,
    mut v_input_3095_: *mut LeanObject,
    mut v_s_3096_: *mut LeanObject,
    mut v_i_3097_: *mut LeanObject,
    mut v_j_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3099_: *mut LeanObject = core::ptr::null_mut();
    v_res_3099_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v_k_3094_, v_input_3095_, v_s_3096_, v_i_3097_, v_j_3098_);
    lean_dec_ref(v_input_3095_);
    lean_dec_ref(v_k_3094_);
    return v_res_3099_;
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(
    mut v_k_3100_: *mut LeanObject,
    mut v_input_3101_: *mut LeanObject,
    mut v_s_3102_: *mut LeanObject,
    mut v_i_3103_: *mut LeanObject,
    mut v_j_3104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v_curr_u2081_3107_: u32 = 0;
    let mut v_curr_u2082_3108_: u32 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3114_: u8 = 0;
    let mut v_error_x3f_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3116_: u8 = 0;
    let mut v_isMeta_3117_: u8 = 0;
    let mut v_isExported_3118_: u8 = 0;
    let mut v_importAll_3119_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v_unused_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3105_ = lean_string_utf8_at_end(v_k_3100_, v_i_3103_);
                if v___x_3105_ == 0 {
                    v___x_3106_ = lean_string_utf8_at_end(v_input_3101_, v_j_3104_);
                    if v___x_3106_ == 0 {
                        v_curr_u2081_3107_ = lean_string_utf8_get_fast(v_k_3100_, v_i_3103_);
                        v_curr_u2082_3108_ = lean_string_utf8_get_fast(v_input_3101_, v_j_3104_);
                        v___x_3109_ = lean_uint32_dec_eq(v_curr_u2081_3107_, v_curr_u2082_3108_);
                        if v___x_3109_ == 0 {
                            lean_dec(v_j_3104_);
                            lean_dec(v_i_3103_);
                            return v_s_3102_;
                        } else {
                            if v___x_3106_ == 0 {
                                v___x_3110_ = lean_string_utf8_next_fast(v_k_3100_, v_i_3103_);
                                lean_dec(v_i_3103_);
                                v___x_3111_ = lean_string_utf8_next_fast(v_input_3101_, v_j_3104_);
                                lean_dec(v_j_3104_);
                                v_i_3103_ = v___x_3110_;
                                v_j_3104_ = v___x_3111_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_3104_);
                                lean_dec(v_i_3103_);
                                return v_s_3102_;
                            }
                        }
                    } else {
                        lean_dec(v_j_3104_);
                        lean_dec(v_i_3103_);
                        return v_s_3102_;
                    }
                } else {
                    lean_dec(v_i_3103_);
                    v_imports_3113_ = lean_ctor_get(v_s_3102_, 0);
                    v_badModifier_3114_ = lean_ctor_get_uint8(
                        v_s_3102_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_3115_ = lean_ctor_get(v_s_3102_, 2);
                    v_isModule_3116_ = lean_ctor_get_uint8(
                        v_s_3102_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3117_ = lean_ctor_get_uint8(
                        v_s_3102_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3118_ = lean_ctor_get_uint8(
                        v_s_3102_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3119_ = lean_ctor_get_uint8(
                        v_s_3102_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3128_ = (!lean_is_exclusive(v_s_3102_)) as u8;
                    if v_isSharedCheck_3128_ == 0 {
                        v_unused_3129_ = lean_ctor_get(v_s_3102_, 1);
                        lean_dec(v_unused_3129_);
                        v___x_3121_ = v_s_3102_;
                        v_isShared_3122_ = v_isSharedCheck_3128_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_3115_);
                        lean_inc(v_imports_3113_);
                        lean_dec(v_s_3102_);
                        v___x_3121_ = lean_box(0);
                        v_isShared_3122_ = v_isSharedCheck_3128_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3122_ == 0 {
                    lean_ctor_set(v___x_3121_, 1, v_j_3104_);
                    v___x_3124_ = v___x_3121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_imports_3113_);
                    lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_j_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_error_x3f_3115_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3127_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3114_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3127_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3116_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3127_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3117_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3127_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3118_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3127_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3119_,
                    );
                    v___x_3124_ = v_reuseFailAlloc_3127_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3125_ = l_Lean_ParseImports_whitespace(v_input_3101_, v___x_3124_);
                v___x_3126_ = l_Lean_ParseImports_setMeta___redArg(v___x_3125_);
                return v___x_3126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4___boxed(
    mut v_k_3130_: *mut LeanObject,
    mut v_input_3131_: *mut LeanObject,
    mut v_s_3132_: *mut LeanObject,
    mut v_i_3133_: *mut LeanObject,
    mut v_j_3134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3135_: *mut LeanObject = core::ptr::null_mut();
    v_res_3135_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v_k_3130_, v_input_3131_, v_s_3132_, v_i_3133_, v_j_3134_);
    lean_dec_ref(v_input_3131_);
    lean_dec_ref(v_k_3130_);
    return v_res_3135_;
}
pub unsafe fn l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(
    mut v_input_3140_: *mut LeanObject,
    mut v_s_3141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3147_: u8 = 0;
    let mut v_isMeta_3148_: u8 = 0;
    let mut v_isExported_3149_: u8 = 0;
    let mut v_importAll_3150_: u8 = 0;
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3160_: u8 = 0;
    let mut v_isMeta_3161_: u8 = 0;
    let mut v_isExported_3162_: u8 = 0;
    let mut v_importAll_3163_: u8 = 0;
    let mut v_badModifier_3164_: u8 = 0;
    let mut v_imports_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3167_: u8 = 0;
    let mut v_isMeta_3168_: u8 = 0;
    let mut v_isExported_3169_: u8 = 0;
    let mut v_importAll_3170_: u8 = 0;
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3186_: u8 = 0;
    let mut v_isModule_3187_: u8 = 0;
    let mut v_isMeta_3188_: u8 = 0;
    let mut v_isExported_3189_: u8 = 0;
    let mut v_importAll_3190_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v_unused_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3202_: u8 = 0;
    let mut v_isMeta_3203_: u8 = 0;
    let mut v_isExported_3204_: u8 = 0;
    let mut v_importAll_3205_: u8 = 0;
    let mut v_pos_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_3142_ = lean_ctor_get(v_s_3141_, 1);
                lean_inc_n(v_pos_3142_, 2);
                v___x_3212_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__1;
                v___x_3213_ = lean_unsigned_to_nat(0);
                v___x_3214_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__3(v___x_3212_, v_input_3140_, v_s_3141_, v___x_3213_, v_pos_3142_);
                v_error_x3f_3215_ = lean_ctor_get(v___x_3214_, 2);
                lean_inc(v_error_x3f_3215_);
                if lean_obj_tag(v_error_x3f_3215_) == 1 {
                    lean_dec_ref_known(v_error_x3f_3215_, 1);
                    v___y_3183_ = v___x_3214_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v_error_x3f_3215_);
                    v_pos_3216_ = lean_ctor_get(v___x_3214_, 1);
                    lean_inc(v_pos_3216_);
                    v___x_3217_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__2;
                    v___x_3218_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__4(v___x_3217_, v_input_3140_, v___x_3214_, v___x_3213_, v_pos_3216_);
                    v_error_x3f_3219_ = lean_ctor_get(v___x_3218_, 2);
                    lean_inc(v_error_x3f_3219_);
                    if lean_obj_tag(v_error_x3f_3219_) == 1 {
                        lean_dec_ref_known(v_error_x3f_3219_, 1);
                        v___y_3183_ = v___x_3218_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_error_x3f_3219_);
                        v_pos_3220_ = lean_ctor_get(v___x_3218_, 1);
                        lean_inc(v_pos_3220_);
                        v___x_3221_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__3;
                        v___x_3222_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__5(v___x_3221_, v_input_3140_, v___x_3218_, v___x_3213_, v_pos_3220_);
                        v___y_3183_ = v___x_3222_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3151_ = lean_nat_dec_eq(v_pos_3146_, v_pos_3142_);
                lean_dec(v_pos_3142_);
                if v___x_3151_ == 0 {
                    lean_dec(v_pos_3146_);
                    lean_dec_ref(v_imports_3145_);
                    return v___y_3144_;
                } else {
                    lean_dec_ref(v___y_3144_);
                    v___x_3152_ = 0;
                    v___x_3153_ = lean_box(0);
                    v___x_3154_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v___x_3154_, 0, v_imports_3145_);
                    lean_ctor_set(v___x_3154_, 1, v_pos_3146_);
                    lean_ctor_set(v___x_3154_, 2, v___x_3153_);
                    lean_ctor_set_uint8(
                        v___x_3154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_3152_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3147_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3148_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3149_,
                    );
                    lean_ctor_set_uint8(
                        v___x_3154_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3150_,
                    );
                    return v___x_3154_;
                }
            }
            2 => {
                v_error_x3f_3157_ = lean_ctor_get(v___y_3156_, 2);
                if lean_obj_tag(v_error_x3f_3157_) == 1 {
                    lean_dec_ref(v_input_3140_);
                    v_imports_3158_ = lean_ctor_get(v___y_3156_, 0);
                    lean_inc_ref(v_imports_3158_);
                    v_pos_3159_ = lean_ctor_get(v___y_3156_, 1);
                    lean_inc(v_pos_3159_);
                    v_isModule_3160_ = lean_ctor_get_uint8(
                        v___y_3156_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3161_ = lean_ctor_get_uint8(
                        v___y_3156_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3162_ = lean_ctor_get_uint8(
                        v___y_3156_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3163_ = lean_ctor_get_uint8(
                        v___y_3156_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v___y_3144_ = v___y_3156_;
                    v_imports_3145_ = v_imports_3158_;
                    v_pos_3146_ = v_pos_3159_;
                    v_isModule_3147_ = v_isModule_3160_;
                    v_isMeta_3148_ = v_isMeta_3161_;
                    v_isExported_3149_ = v_isExported_3162_;
                    v_importAll_3150_ = v_importAll_3163_;
                    state = 1;
                    continue;
                } else {
                    v_badModifier_3164_ = lean_ctor_get_uint8(
                        v___y_3156_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_badModifier_3164_ == 0 {
                        lean_dec(v_pos_3142_);
                        v_s_3141_ = v___y_3156_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_input_3140_);
                        v_imports_3166_ = lean_ctor_get(v___y_3156_, 0);
                        v_isModule_3167_ = lean_ctor_get_uint8(
                            v___y_3156_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_isMeta_3168_ = lean_ctor_get_uint8(
                            v___y_3156_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        );
                        v_isExported_3169_ = lean_ctor_get_uint8(
                            v___y_3156_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        );
                        v_importAll_3170_ = lean_ctor_get_uint8(
                            v___y_3156_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        );
                        v_isSharedCheck_3179_ = (!lean_is_exclusive(v___y_3156_)) as u8;
                        if v_isSharedCheck_3179_ == 0 {
                            v_unused_3180_ = lean_ctor_get(v___y_3156_, 2);
                            lean_dec(v_unused_3180_);
                            v_unused_3181_ = lean_ctor_get(v___y_3156_, 1);
                            lean_dec(v_unused_3181_);
                            v___x_3172_ = v___y_3156_;
                            v_isShared_3173_ = v_isSharedCheck_3179_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_imports_3166_);
                            lean_dec(v___y_3156_);
                            v___x_3172_ = lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3179_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_3174_ = 0;
                v___x_3175_ = l_Lean_ParseImports_manyImports___closed__1;
                if v_isShared_3173_ == 0 {
                    lean_ctor_set(v___x_3172_, 2, v___x_3175_);
                    lean_ctor_set(v___x_3172_, 1, v_pos_3142_);
                    v___x_3177_ = v___x_3172_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_imports_3166_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_pos_3142_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 2, v___x_3175_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3178_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3167_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3178_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3168_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3178_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3169_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3178_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3170_,
                    );
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_3177_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3174_,
                );
                return v___x_3177_;
            }
            5 => {
                v_error_x3f_3184_ = lean_ctor_get(v___y_3183_, 2);
                if lean_obj_tag(v_error_x3f_3184_) == 1 {
                    lean_inc_ref(v_error_x3f_3184_);
                    lean_dec_ref(v_input_3140_);
                    v_imports_3185_ = lean_ctor_get(v___y_3183_, 0);
                    v_badModifier_3186_ = lean_ctor_get_uint8(
                        v___y_3183_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_isModule_3187_ = lean_ctor_get_uint8(
                        v___y_3183_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3188_ = lean_ctor_get_uint8(
                        v___y_3183_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3189_ = lean_ctor_get_uint8(
                        v___y_3183_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3190_ = lean_ctor_get_uint8(
                        v___y_3183_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3197_ = (!lean_is_exclusive(v___y_3183_)) as u8;
                    if v_isSharedCheck_3197_ == 0 {
                        v_unused_3198_ = lean_ctor_get(v___y_3183_, 2);
                        lean_dec(v_unused_3198_);
                        v_unused_3199_ = lean_ctor_get(v___y_3183_, 1);
                        lean_dec(v_unused_3199_);
                        v___x_3192_ = v___y_3183_;
                        v_isShared_3193_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_imports_3185_);
                        lean_dec(v___y_3183_);
                        v___x_3192_ = lean_box(0);
                        v_isShared_3193_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_error_x3f_3184_) == 1 {
                        lean_dec_ref(v_input_3140_);
                        v_imports_3200_ = lean_ctor_get(v___y_3183_, 0);
                        lean_inc_ref(v_imports_3200_);
                        v_pos_3201_ = lean_ctor_get(v___y_3183_, 1);
                        lean_inc(v_pos_3201_);
                        v_isModule_3202_ = lean_ctor_get_uint8(
                            v___y_3183_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_isMeta_3203_ = lean_ctor_get_uint8(
                            v___y_3183_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        );
                        v_isExported_3204_ = lean_ctor_get_uint8(
                            v___y_3183_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        );
                        v_importAll_3205_ = lean_ctor_get_uint8(
                            v___y_3183_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        );
                        v___y_3144_ = v___y_3183_;
                        v_imports_3145_ = v_imports_3200_;
                        v_pos_3146_ = v_pos_3201_;
                        v_isModule_3147_ = v_isModule_3202_;
                        v_isMeta_3148_ = v_isMeta_3203_;
                        v_isExported_3149_ = v_isExported_3204_;
                        v_importAll_3150_ = v_importAll_3205_;
                        state = 1;
                        continue;
                    } else {
                        v_pos_3206_ = lean_ctor_get(v___y_3183_, 1);
                        lean_inc(v_pos_3206_);
                        v___x_3207_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6___closed__0;
                        v___x_3208_ = lean_unsigned_to_nat(0);
                        v___x_3209_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__2(v___x_3207_, v_input_3140_, v___y_3183_, v___x_3208_, v_pos_3206_);
                        v_error_x3f_3210_ = lean_ctor_get(v___x_3209_, 2);
                        lean_inc(v_error_x3f_3210_);
                        if lean_obj_tag(v_error_x3f_3210_) == 1 {
                            lean_dec_ref_known(v_error_x3f_3210_, 1);
                            v___y_3156_ = v___x_3209_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_error_x3f_3210_);
                            lean_inc_ref(v_input_3140_);
                            v___x_3211_ =
                                l_Lean_ParseImports_moduleIdent(v_input_3140_, v___x_3209_);
                            v___y_3156_ = v___x_3211_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            6 => {
                lean_inc(v_pos_3142_);
                lean_inc_ref(v_imports_3185_);
                if v_isShared_3193_ == 0 {
                    lean_ctor_set(v___x_3192_, 1, v_pos_3142_);
                    v___x_3195_ = v___x_3192_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_imports_3185_);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_pos_3142_);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_error_x3f_3184_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3186_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3187_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3188_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3189_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3190_,
                    );
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc(v_pos_3142_);
                v___y_3144_ = v___x_3195_;
                v_imports_3145_ = v_imports_3185_;
                v_pos_3146_ = v_pos_3142_;
                v_isModule_3147_ = v_isModule_3187_;
                v_isMeta_3148_ = v_isMeta_3188_;
                v_isExported_3149_ = v_isExported_3189_;
                v_importAll_3150_ = v_importAll_3190_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(
    mut v_k_3223_: *mut LeanObject,
    mut v_input_3224_: *mut LeanObject,
    mut v_s_3225_: *mut LeanObject,
    mut v_i_3226_: *mut LeanObject,
    mut v_j_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: u8 = 0;
    let mut v_curr_u2081_3230_: u32 = 0;
    let mut v_curr_u2082_3231_: u32 = 0;
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imports_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_badModifier_3240_: u8 = 0;
    let mut v_error_x3f_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3242_: u8 = 0;
    let mut v_isMeta_3243_: u8 = 0;
    let mut v_isExported_3244_: u8 = 0;
    let mut v_importAll_3245_: u8 = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_unused_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3228_ = lean_string_utf8_at_end(v_k_3223_, v_i_3226_);
                if v___x_3228_ == 0 {
                    v___x_3229_ = lean_string_utf8_at_end(v_input_3224_, v_j_3227_);
                    if v___x_3229_ == 0 {
                        v_curr_u2081_3230_ = lean_string_utf8_get_fast(v_k_3223_, v_i_3226_);
                        v_curr_u2082_3231_ = lean_string_utf8_get_fast(v_input_3224_, v_j_3227_);
                        v___x_3232_ = lean_uint32_dec_eq(v_curr_u2081_3230_, v_curr_u2082_3231_);
                        if v___x_3232_ == 0 {
                            lean_dec(v_j_3227_);
                            lean_dec(v_i_3226_);
                            v___x_3233_ =
                                l_Lean_ParseImports_setIsModule___redArg(v___x_3228_, v_s_3225_);
                            return v___x_3233_;
                        } else {
                            if v___x_3229_ == 0 {
                                v___x_3234_ = lean_string_utf8_next_fast(v_k_3223_, v_i_3226_);
                                lean_dec(v_i_3226_);
                                v___x_3235_ = lean_string_utf8_next_fast(v_input_3224_, v_j_3227_);
                                lean_dec(v_j_3227_);
                                v_i_3226_ = v___x_3234_;
                                v_j_3227_ = v___x_3235_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_j_3227_);
                                lean_dec(v_i_3226_);
                                v___x_3237_ = l_Lean_ParseImports_setIsModule___redArg(
                                    v___x_3228_,
                                    v_s_3225_,
                                );
                                return v___x_3237_;
                            }
                        }
                    } else {
                        lean_dec(v_j_3227_);
                        lean_dec(v_i_3226_);
                        v___x_3238_ =
                            l_Lean_ParseImports_setIsModule___redArg(v___x_3228_, v_s_3225_);
                        return v___x_3238_;
                    }
                } else {
                    lean_dec(v_i_3226_);
                    v_imports_3239_ = lean_ctor_get(v_s_3225_, 0);
                    v_badModifier_3240_ = lean_ctor_get_uint8(
                        v_s_3225_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_error_x3f_3241_ = lean_ctor_get(v_s_3225_, 2);
                    v_isModule_3242_ = lean_ctor_get_uint8(
                        v_s_3225_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isMeta_3243_ = lean_ctor_get_uint8(
                        v_s_3225_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    );
                    v_isExported_3244_ = lean_ctor_get_uint8(
                        v_s_3225_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v_importAll_3245_ = lean_ctor_get_uint8(
                        v_s_3225_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                    );
                    v_isSharedCheck_3254_ = (!lean_is_exclusive(v_s_3225_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v_unused_3255_ = lean_ctor_get(v_s_3225_, 1);
                        lean_dec(v_unused_3255_);
                        v___x_3247_ = v_s_3225_;
                        v_isShared_3248_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_error_x3f_3241_);
                        lean_inc(v_imports_3239_);
                        lean_dec(v_s_3225_);
                        v___x_3247_ = lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3248_ == 0 {
                    lean_ctor_set(v___x_3247_, 1, v_j_3227_);
                    v___x_3250_ = v___x_3247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 3, (5) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_imports_3239_);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_j_3227_);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_error_x3f_3241_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_badModifier_3240_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_isModule_3242_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                        v_isMeta_3243_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        v_isExported_3244_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                        v_importAll_3245_,
                    );
                    v___x_3250_ = v_reuseFailAlloc_3253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3251_ = l_Lean_ParseImports_whitespace(v_input_3224_, v___x_3250_);
                v___x_3252_ = l_Lean_ParseImports_setIsModule___redArg(v___x_3228_, v___x_3251_);
                return v___x_3252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0___boxed(
    mut v_k_3256_: *mut LeanObject,
    mut v_input_3257_: *mut LeanObject,
    mut v_s_3258_: *mut LeanObject,
    mut v_i_3259_: *mut LeanObject,
    mut v_j_3260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
    v_res_3261_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v_k_3256_, v_input_3257_, v_s_3258_, v_i_3259_, v_j_3260_);
    lean_dec_ref(v_input_3257_);
    lean_dec_ref(v_k_3256_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_ParseImports_main(
    mut v_a_3264_: *mut LeanObject,
    mut v_a_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3270_: *mut LeanObject = core::ptr::null_mut();
    v_pos_3266_ = lean_ctor_get(v_a_3265_, 1);
    lean_inc(v_pos_3266_);
    v___x_3267_ = l_Lean_ParseImports_main___closed__0;
    v___x_3268_ = lean_unsigned_to_nat(0);
    v_s_3269_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__0(v___x_3267_, v_a_3264_, v_a_3265_, v___x_3268_, v_pos_3266_);
    v_error_x3f_3270_ = lean_ctor_get(v_s_3269_, 2);
    lean_inc(v_error_x3f_3270_);
    if lean_obj_tag(v_error_x3f_3270_) == 1 {
        lean_dec_ref_known(v_error_x3f_3270_, 1);
        lean_dec_ref(v_a_3264_);
        return v_s_3269_;
    } else {
        let mut v_pos_3271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
        let mut v_error_x3f_3274_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_error_x3f_3270_);
        v_pos_3271_ = lean_ctor_get(v_s_3269_, 1);
        lean_inc(v_pos_3271_);
        v___x_3272_ = l_Lean_ParseImports_main___closed__1;
        v___x_3273_ = l___private_Lean_Elab_ParseImportsFast_0__Lean_ParseImports_keywordCore_go___at___00Lean_ParseImports_main_spec__1(v___x_3272_, v_a_3264_, v_s_3269_, v___x_3268_, v_pos_3271_);
        v_error_x3f_3274_ = lean_ctor_get(v___x_3273_, 2);
        lean_inc(v_error_x3f_3274_);
        if lean_obj_tag(v_error_x3f_3274_) == 1 {
            lean_dec_ref_known(v_error_x3f_3274_, 1);
            lean_dec_ref(v_a_3264_);
            return v___x_3273_;
        } else {
            let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_error_x3f_3274_);
            v___x_3275_ = l_Lean_ParseImports_manyImports___at___00Lean_ParseImports_main_spec__6(
                v_a_3264_,
                v___x_3273_,
            );
            return v___x_3275_;
        }
    }
}
pub unsafe fn l_Lean_parseImports_x27(
    mut v_input_3278_: *mut LeanObject,
    mut v_fileName_3279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_x3f_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v_fileMap_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_imports_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3310_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3281_ = l_Lean_ParseImports_instInhabitedState_default___closed__1;
                v___x_3282_ = l_Lean_ParseImports_whitespace(v_input_3278_, v___x_3281_);
                lean_inc_ref(v_input_3278_);
                v_s_3283_ = l_Lean_ParseImports_main(v_input_3278_, v___x_3282_);
                v_error_x3f_3284_ = lean_ctor_get(v_s_3283_, 2);
                lean_inc(v_error_x3f_3284_);
                if lean_obj_tag(v_error_x3f_3284_) == 1 {
                    v_pos_3285_ = lean_ctor_get(v_s_3283_, 1);
                    lean_inc(v_pos_3285_);
                    lean_dec_ref(v_s_3283_);
                    v_val_3286_ = lean_ctor_get(v_error_x3f_3284_, 0);
                    v_isSharedCheck_3308_ = (!lean_is_exclusive(v_error_x3f_3284_)) as u8;
                    if v_isSharedCheck_3308_ == 0 {
                        v___x_3288_ = v_error_x3f_3284_;
                        v_isShared_3289_ = v_isSharedCheck_3308_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3286_);
                        lean_dec(v_error_x3f_3284_);
                        v___x_3288_ = lean_box(0);
                        v_isShared_3289_ = v_isSharedCheck_3308_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_error_x3f_3284_);
                    lean_dec_ref(v_fileName_3279_);
                    lean_dec_ref(v_input_3278_);
                    v_imports_3309_ = lean_ctor_get(v_s_3283_, 0);
                    lean_inc_ref(v_imports_3309_);
                    v_isModule_3310_ = lean_ctor_get_uint8(
                        v_s_3283_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    lean_dec_ref(v_s_3283_);
                    v___x_3311_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3311_, 0, v_imports_3309_);
                    lean_ctor_set_uint8(
                        v___x_3311_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_isModule_3310_,
                    );
                    v___x_3312_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3312_, 0, v___x_3311_);
                    return v___x_3312_;
                }
            }
            1 => {
                v_fileMap_3290_ = l_String_toFileMap(v_input_3278_);
                v_pos_3291_ = l_Lean_FileMap_toPosition(v_fileMap_3290_, v_pos_3285_);
                lean_dec(v_pos_3285_);
                v_line_3292_ = lean_ctor_get(v_pos_3291_, 0);
                lean_inc(v_line_3292_);
                v_column_3293_ = lean_ctor_get(v_pos_3291_, 1);
                lean_inc(v_column_3293_);
                lean_dec_ref(v_pos_3291_);
                v___x_3294_ = l_Lean_parseImports_x27___closed__0;
                v___x_3295_ = lean_string_append(v_fileName_3279_, v___x_3294_);
                v___x_3296_ = l_Nat_reprFast(v_line_3292_);
                v___x_3297_ = lean_string_append(v___x_3295_, v___x_3296_);
                lean_dec_ref(v___x_3296_);
                v___x_3298_ = lean_string_append(v___x_3297_, v___x_3294_);
                v___x_3299_ = l_Nat_reprFast(v_column_3293_);
                v___x_3300_ = lean_string_append(v___x_3298_, v___x_3299_);
                lean_dec_ref(v___x_3299_);
                v___x_3301_ = l_Lean_parseImports_x27___closed__1;
                v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
                v___x_3303_ = lean_string_append(v___x_3302_, v_val_3286_);
                lean_dec(v_val_3286_);
                if v_isShared_3289_ == 0 {
                    lean_ctor_set_tag(v___x_3288_, 18);
                    lean_ctor_set(v___x_3288_, 0, v___x_3303_);
                    v___x_3305_ = v___x_3288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = lean_alloc_ctor(18, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3303_);
                    v___x_3305_ = v_reuseFailAlloc_3307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3306_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3306_, 0, v___x_3305_);
                return v___x_3306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseImports_x27___boxed(
    mut v_input_3313_: *mut LeanObject,
    mut v_fileName_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3316_: *mut LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_parseImports_x27(v_input_3313_, v_fileName_3314_);
    return v_res_3316_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(
    mut v_k_3317_: *mut LeanObject,
    mut v_x_3318_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3318_) == 0 {
        let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_3317_);
        v___x_3319_ = lean_box(0);
        return v___x_3319_;
    } else {
        let mut v_val_3320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
        v_val_3320_ = lean_ctor_get(v_x_3318_, 0);
        lean_inc(v_val_3320_);
        lean_dec_ref_known(v_x_3318_, 1);
        v___x_3321_ = l_Lean_instToJsonModuleHeader_toJson(v_val_3320_);
        v___x_3322_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3322_, 0, v_k_3317_);
        lean_ctor_set(v___x_3322_, 1, v___x_3321_);
        v___x_3323_ = lean_box(0);
        v___x_3324_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3324_, 0, v___x_3322_);
        lean_ctor_set(v___x_3324_, 1, v___x_3323_);
        return v___x_3324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(
    mut v_a_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3325_) == 0 {
                    v___x_3327_ = lean_array_to_list(v_a_3326_);
                    return v___x_3327_;
                } else {
                    v_head_3328_ = lean_ctor_get(v_a_3325_, 0);
                    lean_inc(v_head_3328_);
                    v_tail_3329_ = lean_ctor_get(v_a_3325_, 1);
                    lean_inc(v_tail_3329_);
                    lean_dec_ref_known(v_a_3325_, 2);
                    v___x_3330_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3326_,
                        v_head_3328_,
                    );
                    v_a_3325_ = v_tail_3329_;
                    v_a_3326_ = v___x_3330_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(
    mut v_sz_3332_: usize,
    mut v_i_3333_: usize,
    mut v_bs_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3335_: u8 = 0;
    let mut v_v_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: usize = 0;
    let mut v___x_3341_: usize = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3335_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
                if v___x_3335_ == 0 {
                    return v_bs_3334_;
                } else {
                    v_v_3336_ = lean_array_uget(v_bs_3334_, v_i_3333_);
                    v___x_3337_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3338_ = lean_array_uset(v_bs_3334_, v_i_3333_, v___x_3337_);
                    v___x_3339_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3339_, 0, v_v_3336_);
                    v___x_3340_ = 1usize;
                    v___x_3341_ = lean_usize_add(v_i_3333_, v___x_3340_);
                    v___x_3342_ = lean_array_uset(v_bs_x27_3338_, v_i_3333_, v___x_3339_);
                    v_i_3333_ = v___x_3341_;
                    v_bs_3334_ = v___x_3342_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1___boxed(
    mut v_sz_3344_: *mut LeanObject,
    mut v_i_3345_: *mut LeanObject,
    mut v_bs_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3347_: usize = 0;
    let mut v_i_boxed_3348_: usize = 0;
    let mut v_res_3349_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3347_ = lean_unbox_usize(v_sz_3344_);
    lean_dec(v_sz_3344_);
    v_i_boxed_3348_ = lean_unbox_usize(v_i_3345_);
    lean_dec(v_i_3345_);
    v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_boxed_3347_, v_i_boxed_3348_, v_bs_3346_);
    return v_res_3349_;
}
pub unsafe fn l_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(
    mut v_a_3350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3351_: usize = 0;
    let mut v___x_3352_: usize = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3351_ = lean_array_size(v_a_3350_);
    v___x_3352_ = 0usize;
    v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1_spec__1(v_sz_3351_, v___x_3352_, v_a_3350_);
    v___x_3354_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_3354_, 0, v___x_3353_);
    return v___x_3354_;
}
pub unsafe fn l_Lean_instToJsonPrintImportResult_toJson(
    mut v_x_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_x3f_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errors_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_x3f_3360_ = lean_ctor_get(v_x_3359_, 0);
                v_errors_3361_ = lean_ctor_get(v_x_3359_, 1);
                v_isSharedCheck_3379_ = (!lean_is_exclusive(v_x_3359_)) as u8;
                if v_isSharedCheck_3379_ == 0 {
                    v___x_3363_ = v_x_3359_;
                    v_isShared_3364_ = v_isSharedCheck_3379_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_errors_3361_);
                    lean_inc(v_result_x3f_3360_);
                    lean_dec(v_x_3359_);
                    v___x_3363_ = lean_box(0);
                    v_isShared_3364_ = v_isSharedCheck_3379_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3365_ = l_Lean_instToJsonPrintImportResult_toJson___closed__0;
                v___x_3366_ =
                    l_Lean_Json_opt___at___00Lean_instToJsonPrintImportResult_toJson_spec__0(
                        v___x_3365_,
                        v_result_x3f_3360_,
                    );
                v___x_3367_ = l_Lean_instToJsonPrintImportResult_toJson___closed__1;
                v___x_3368_ =
                    l_Array_toJson___at___00Lean_instToJsonPrintImportResult_toJson_spec__1(
                        v_errors_3361_,
                    );
                if v_isShared_3364_ == 0 {
                    lean_ctor_set(v___x_3363_, 1, v___x_3368_);
                    lean_ctor_set(v___x_3363_, 0, v___x_3367_);
                    v___x_3370_ = v___x_3363_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3367_);
                    lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3368_);
                    v___x_3370_ = v_reuseFailAlloc_3378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3371_ = lean_box(0);
                v___x_3372_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3372_, 0, v___x_3370_);
                lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                v___x_3373_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3373_, 0, v___x_3372_);
                lean_ctor_set(v___x_3373_, 1, v___x_3371_);
                v___x_3374_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3374_, 0, v___x_3366_);
                lean_ctor_set(v___x_3374_, 1, v___x_3373_);
                v___x_3375_ = l_Lean_instToJsonPrintImportResult_toJson___closed__2;
                v___x_3376_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_3374_, v___x_3375_);
                v___x_3377_ = l_Lean_Json_mkObj(v___x_3376_);
                lean_dec(v___x_3376_);
                return v___x_3377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(
    mut v_sz_3382_: usize,
    mut v_i_3383_: usize,
    mut v_bs_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3385_: u8 = 0;
    let mut v_v_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: usize = 0;
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3385_ = lean_usize_dec_lt(v_i_3383_, v_sz_3382_);
                if v___x_3385_ == 0 {
                    return v_bs_3384_;
                } else {
                    v_v_3386_ = lean_array_uget(v_bs_3384_, v_i_3383_);
                    v___x_3387_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3388_ = lean_array_uset(v_bs_3384_, v_i_3383_, v___x_3387_);
                    v___x_3389_ = l_Lean_instToJsonPrintImportResult_toJson(v_v_3386_);
                    v___x_3390_ = 1usize;
                    v___x_3391_ = lean_usize_add(v_i_3383_, v___x_3390_);
                    v___x_3392_ = lean_array_uset(v_bs_x27_3388_, v_i_3383_, v___x_3389_);
                    v_i_3383_ = v___x_3391_;
                    v_bs_3384_ = v___x_3392_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0___boxed(
    mut v_sz_3394_: *mut LeanObject,
    mut v_i_3395_: *mut LeanObject,
    mut v_bs_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3397_: usize = 0;
    let mut v_i_boxed_3398_: usize = 0;
    let mut v_res_3399_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3397_ = lean_unbox_usize(v_sz_3394_);
    lean_dec(v_sz_3394_);
    v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
    lean_dec(v_i_3395_);
    v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_boxed_3397_, v_i_boxed_3398_, v_bs_3396_);
    return v_res_3399_;
}
pub unsafe fn l_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(
    mut v_a_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3401_: usize = 0;
    let mut v___x_3402_: usize = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3401_ = lean_array_size(v_a_3400_);
    v___x_3402_ = 0usize;
    v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0_spec__0(v_sz_3401_, v___x_3402_, v_a_3400_);
    v___x_3404_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_3404_, 0, v___x_3403_);
    return v___x_3404_;
}
pub unsafe fn l_Lean_instToJsonPrintImportsResult_toJson(
    mut v_x_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_instToJsonPrintImportsResult_toJson___closed__0;
    v___x_3408_ =
        l_Array_toJson___at___00Lean_instToJsonPrintImportsResult_toJson_spec__0(v_x_3406_);
    v___x_3409_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3409_, 0, v___x_3407_);
    lean_ctor_set(v___x_3409_, 1, v___x_3408_);
    v___x_3410_ = lean_box(0);
    v___x_3411_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3411_, 0, v___x_3409_);
    lean_ctor_set(v___x_3411_, 1, v___x_3410_);
    v___x_3412_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3412_, 0, v___x_3411_);
    lean_ctor_set(v___x_3412_, 1, v___x_3410_);
    v___x_3413_ = l_Lean_instToJsonPrintImportResult_toJson___closed__2;
    v___x_3414_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPrintImportResult_toJson_spec__2(v___x_3412_, v___x_3413_);
    v___x_3415_ = l_Lean_Json_mkObj(v___x_3414_);
    lean_dec(v___x_3414_);
    return v___x_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(
    mut v_sz_3420_: usize,
    mut v_i_3421_: usize,
    mut v_bs_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: usize = 0;
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3424_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
                if v___x_3424_ == 0 {
                    v___x_3425_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3425_, 0, v_bs_3422_);
                    return v___x_3425_;
                } else {
                    v_v_3426_ = lean_array_uget(v_bs_3422_, v_i_3421_);
                    v___x_3427_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3428_ = lean_array_uset(v_bs_3422_, v_i_3421_, v___x_3427_);
                    v___x_3443_ = l_IO_FS_readFile(v_v_3426_);
                    if lean_obj_tag(v___x_3443_) == 0 {
                        v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
                        lean_inc(v_a_3444_);
                        lean_dec_ref_known(v___x_3443_, 1);
                        v___x_3445_ = l_Lean_parseImports_x27(v_a_3444_, v_v_3426_);
                        if lean_obj_tag(v___x_3445_) == 0 {
                            v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
                            v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3448_ = v___x_3445_;
                                v_isShared_3449_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3446_);
                                lean_dec(v___x_3445_);
                                v___x_3448_ = lean_box(0);
                                v_isShared_3449_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3456_ = lean_ctor_get(v___x_3445_, 0);
                            lean_inc(v_a_3456_);
                            lean_dec_ref_known(v___x_3445_, 1);
                            v_a_3436_ = v_a_3456_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_v_3426_);
                        v_a_3457_ = lean_ctor_get(v___x_3443_, 0);
                        lean_inc(v_a_3457_);
                        lean_dec_ref_known(v___x_3443_, 1);
                        v_a_3436_ = v_a_3457_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3431_ = 1usize;
                v___x_3432_ = lean_usize_add(v_i_3421_, v___x_3431_);
                v___x_3433_ = lean_array_uset(v_bs_x27_3428_, v_i_3421_, v_a_3430_);
                v_i_3421_ = v___x_3432_;
                v_bs_3422_ = v___x_3433_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3437_ = lean_box(0);
                v___x_3438_ = lean_io_error_to_string(v_a_3436_);
                v___x_3439_ = lean_unsigned_to_nat(1);
                v___x_3440_ = lean_mk_empty_array_with_capacity(v___x_3439_);
                v___x_3441_ = lean_array_push(v___x_3440_, v___x_3438_);
                v___x_3442_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3442_, 0, v___x_3437_);
                lean_ctor_set(v___x_3442_, 1, v___x_3441_);
                v_a_3430_ = v___x_3442_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_3449_ == 0 {
                    lean_ctor_set_tag(v___x_3448_, 1);
                    v___x_3451_ = v___x_3448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3446_);
                    v___x_3451_ = v_reuseFailAlloc_3454_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___closed__0;
                v___x_3453_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3453_, 0, v___x_3451_);
                lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                v_a_3430_ = v___x_3453_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0___boxed(
    mut v_sz_3458_: *mut LeanObject,
    mut v_i_3459_: *mut LeanObject,
    mut v_bs_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3462_: usize = 0;
    let mut v_i_boxed_3463_: usize = 0;
    let mut v_res_3464_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3462_ = lean_unbox_usize(v_sz_3458_);
    lean_dec(v_sz_3458_);
    v_i_boxed_3463_ = lean_unbox_usize(v_i_3459_);
    lean_dec(v_i_3459_);
    v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_boxed_3462_, v_i_boxed_3463_, v_bs_3460_);
    return v_res_3464_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(
    mut v_s_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3467_ = lean_get_stdout();
    v_putStr_3468_ = lean_ctor_get(v___x_3467_, 4);
    lean_inc_ref(v_putStr_3468_);
    lean_dec_ref(v___x_3467_);
    v___x_3469_ = lean_apply_2(v_putStr_3468_, v_s_3465_, lean_box(0));
    return v___x_3469_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1___boxed(
    mut v_s_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3472_: *mut LeanObject = core::ptr::null_mut();
    v_res_3472_ =
        l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v_s_3470_);
    return v_res_3472_;
}
pub unsafe fn l_IO_println___at___00Lean_printImportsJson_spec__1(
    mut v_s_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3475_: u32 = 0;
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    v___x_3475_ = 10;
    v___x_3476_ = lean_string_push(v_s_3473_, v___x_3475_);
    v___x_3477_ =
        l_IO_print___at___00IO_println___at___00Lean_printImportsJson_spec__1_spec__1(v___x_3476_);
    return v___x_3477_;
}
pub unsafe fn l_IO_println___at___00Lean_printImportsJson_spec__1___boxed(
    mut v_s_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v_s_3478_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_printImportsJson(mut v_fileNames_3481_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sz_3483_: usize = 0;
    let mut v___x_3484_: usize = 0;
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_3483_ = lean_array_size(v_fileNames_3481_);
                v___x_3484_ = 0usize;
                v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_printImportsJson_spec__0(v_sz_3483_, v___x_3484_, v_fileNames_3481_);
                if lean_obj_tag(v___x_3485_) == 0 {
                    v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
                    lean_inc(v_a_3486_);
                    lean_dec_ref_known(v___x_3485_, 1);
                    v___x_3487_ = l_Lean_instToJsonPrintImportsResult_toJson(v_a_3486_);
                    v___x_3488_ = l_Lean_Json_compress(v___x_3487_);
                    v___x_3489_ = l_IO_println___at___00Lean_printImportsJson_spec__1(v___x_3488_);
                    return v___x_3489_;
                } else {
                    v_a_3490_ = lean_ctor_get(v___x_3485_, 0);
                    v_isSharedCheck_3497_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                    if v_isSharedCheck_3497_ == 0 {
                        v___x_3492_ = v___x_3485_;
                        v_isShared_3493_ = v_isSharedCheck_3497_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3490_);
                        lean_dec(v___x_3485_);
                        v___x_3492_ = lean_box(0);
                        v_isShared_3493_ = v_isSharedCheck_3497_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3493_ == 0 {
                    v___x_3495_ = v___x_3492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
                    v___x_3495_ = v_reuseFailAlloc_3496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_printImportsJson___boxed(
    mut v_fileNames_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Lean_printImportsJson(v_fileNames_3498_);
    return v_res_3500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ParseImportsFast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ParseImportsFast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ParseImportsFast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ParseImportsFast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ParseImportsFast(builtin);
}
