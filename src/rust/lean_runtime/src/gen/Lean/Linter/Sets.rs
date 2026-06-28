// Lean compiler output
// Module: Lean.Linter.Sets
// Imports: Lean.Linter.Init Lean.Elab.Command Init.Notation Lean.Data.KVMap
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_TSyntax_getId, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::KVMap::{
    initialize_Lean_Data_KVMap, runtime_initialize_Lean_Data_KVMap,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_elabCommand___boxed,
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_withMacroExpansion___redArg, meta_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_header, l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_linterSetsExt, meta_initialize_Lean_Linter_Init,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Linter_registerSet___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Linter_registerSet___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Linter_registerSet___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__3_value) as *mut LeanObject;
static l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_registerSet___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Linter_registerSet___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__6_value: LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__6_value) as *mut LeanObject;
static l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_registerSet___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Linter_registerSet___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__10_value: LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__10_value) as *mut LeanObject;
static l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_registerSet___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Lean_Linter_registerSet___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_registerSet___auto__1___closed__14_value: LeanStringObject<5> =
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
static mut l_Lean_Linter_registerSet___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__15_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__15_value) as *mut LeanObject;
static l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Linter_registerSet___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__16_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___auto__1___closed__17_value: LeanStringObject<11> =
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
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_Linter_registerSet___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Lean_Linter_registerSet___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_registerSet___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_registerSet___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Linter_registerSet___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_registerSet___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l_Lean_Linter_registerSet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_registerSet___closed__1_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_registerSet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_registerSet___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value:
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
    m_data: [76, 105, 110, 116, 101, 114, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value:
    LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 82, 101, 103, 105, 115, 116, 101, 114, 95, 108, 105,
        110, 116, 101, 114, 95, 115, 101, 116, 95, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value
)
    as *mut LeanObject;
static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_1:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value
        ) as *mut LeanObject,
        8071394701935581384 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__1_value
        ) as *mut LeanObject,
        10657344386299449956 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value:
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
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__5_value
        ) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__7_value
        ) as *mut LeanObject,
        3961966953292576997 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value
)
    as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__6_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__9_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value:
    LeanStringObject<20> = LeanStringObject {
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
        114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 105, 110, 116, 101, 114, 95, 115, 101,
        116, 0,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__11_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__10_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__12_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value:
    LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__14_value
        ) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__15_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__18_value
    ) as *mut LeanObject],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__17_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__19_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value:
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
    m_data: [109, 97, 110, 121, 0],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value:
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
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__21_value
        ) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__22_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__16_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__20_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__23_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value
) as *mut LeanObject;
pub static l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2_value
        ) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__24_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value
) as *mut LeanObject;
pub static mut l_Lean_Linter_command__Register__linter__set___x3a_x3d__: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__25_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5_value) as *mut LeanObject;
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value) as *mut LeanObject;
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__7_value) as *mut LeanObject,3127099019797772086 as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8_value) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__11_value) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value) as *mut LeanObject;
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15_value) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__17_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__16_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__18_value) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 76, 105, 110, 116, 101, 114, 46, 114, 101, 103, 105, 115, 116, 101, 114, 83, 101, 116, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24_value) as *mut LeanObject;
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 83, 101, 116, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value) as *mut LeanObject;
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__0_value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__26_value) as *mut LeanObject,11820710118905974610 as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__28_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value) as *mut LeanObject;
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34_value) as *mut LeanObject,12014440461648055863 as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35_value) as *mut LeanObject;
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value) as *mut LeanObject;
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter_registerSet___auto__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__36_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37_value) as *mut LeanObject;
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Linter_insertLinterSet___redArg___lam__0(
    mut v_setName_566_: *mut LeanObject,
    mut v_linterNames_567_: *mut LeanObject,
    mut v_x_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_570_ = lean_ctor_get(v___x_569_, 0);
    v_asyncMode_571_ = lean_ctor_get(v_toEnvExtension_570_, 2);
    v___x_572_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_572_, 0, v_setName_566_);
    lean_ctor_set(v___x_572_, 1, v_linterNames_567_);
    v___x_573_ = lean_box(0);
    v___x_574_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v___x_569_,
        v_x_568_,
        v___x_572_,
        v_asyncMode_571_,
        v___x_573_,
    );
    return v___x_574_;
}
pub unsafe fn l_Lean_Linter_insertLinterSet___redArg(
    mut v_inst_575_: *mut LeanObject,
    mut v_setName_576_: *mut LeanObject,
    mut v_linterNames_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_578_ = lean_ctor_get(v_inst_575_, 1);
    lean_inc(v_modifyEnv_578_);
    lean_dec_ref(v_inst_575_);
    v___f_579_ = lean_alloc_closure(
        l_Lean_Linter_insertLinterSet___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_579_, 0, v_setName_576_);
    lean_closure_set(v___f_579_, 1, v_linterNames_577_);
    v___x_580_ = lean_apply_1(v_modifyEnv_578_, v___f_579_);
    return v___x_580_;
}
pub unsafe fn l_Lean_Linter_insertLinterSet(
    mut v_m_581_: *mut LeanObject,
    mut v_inst_582_: *mut LeanObject,
    mut v_setName_583_: *mut LeanObject,
    mut v_linterNames_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_585_ =
        l_Lean_Linter_insertLinterSet___redArg(v_inst_582_, v_setName_583_, v_linterNames_584_);
    return v___x_585_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_612_ = l_Lean_Linter_registerSet___auto__1___closed__10;
    v___x_613_ = l_Lean_mkAtom(v___x_612_);
    return v___x_613_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__12_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__12,
    );
    v___x_615_ = l_Lean_Linter_registerSet___auto__1___closed__5;
    v___x_616_ = lean_array_push(v___x_615_, v___x_614_);
    return v___x_616_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lean_Linter_registerSet___auto__1___closed__17;
    v___x_626_ = l_Lean_mkAtom(v___x_625_);
    return v___x_626_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__18_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__18,
    );
    v___x_628_ = l_Lean_Linter_registerSet___auto__1___closed__5;
    v___x_629_ = lean_array_push(v___x_628_, v___x_627_);
    return v___x_629_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__19_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__19,
    );
    v___x_631_ = l_Lean_Linter_registerSet___auto__1___closed__16;
    v___x_632_ = lean_box(2);
    v___x_633_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_633_, 0, v___x_632_);
    lean_ctor_set(v___x_633_, 1, v___x_631_);
    lean_ctor_set(v___x_633_, 2, v___x_630_);
    return v___x_633_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__20_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__20,
    );
    v___x_635_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__13_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__13,
    );
    v___x_636_ = lean_array_push(v___x_635_, v___x_634_);
    return v___x_636_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_637_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__21_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__21,
    );
    v___x_638_ = l_Lean_Linter_registerSet___auto__1___closed__11;
    v___x_639_ = lean_box(2);
    v___x_640_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_640_, 0, v___x_639_);
    lean_ctor_set(v___x_640_, 1, v___x_638_);
    lean_ctor_set(v___x_640_, 2, v___x_637_);
    return v___x_640_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_641_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__22_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__22,
    );
    v___x_642_ = l_Lean_Linter_registerSet___auto__1___closed__5;
    v___x_643_ = lean_array_push(v___x_642_, v___x_641_);
    return v___x_643_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__23_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__23,
    );
    v___x_645_ = l_Lean_Linter_registerSet___auto__1___closed__9;
    v___x_646_ = lean_box(2);
    v___x_647_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_647_, 0, v___x_646_);
    lean_ctor_set(v___x_647_, 1, v___x_645_);
    lean_ctor_set(v___x_647_, 2, v___x_644_);
    return v___x_647_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    v___x_648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__24_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__24,
    );
    v___x_649_ = l_Lean_Linter_registerSet___auto__1___closed__5;
    v___x_650_ = lean_array_push(v___x_649_, v___x_648_);
    return v___x_650_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v___x_651_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__25_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__25,
    );
    v___x_652_ = l_Lean_Linter_registerSet___auto__1___closed__7;
    v___x_653_ = lean_box(2);
    v___x_654_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_654_, 0, v___x_653_);
    lean_ctor_set(v___x_654_, 1, v___x_652_);
    lean_ctor_set(v___x_654_, 2, v___x_651_);
    return v___x_654_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__26_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__26,
    );
    v___x_656_ = l_Lean_Linter_registerSet___auto__1___closed__5;
    v___x_657_ = lean_array_push(v___x_656_, v___x_655_);
    return v___x_657_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__27_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__27,
    );
    v___x_659_ = l_Lean_Linter_registerSet___auto__1___closed__4;
    v___x_660_ = lean_box(2);
    v___x_661_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_661_, 0, v___x_660_);
    lean_ctor_set(v___x_661_, 1, v___x_659_);
    lean_ctor_set(v___x_661_, 2, v___x_658_);
    return v___x_661_;
}
pub unsafe fn _init_l_Lean_Linter_registerSet___auto__1() -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Linter_registerSet___auto__1___closed__28_once),
        _init_l_Lean_Linter_registerSet___auto__1___closed__28,
    );
    return v___x_662_;
}
pub unsafe fn l_Lean_Linter_registerSet(
    mut v_setName_666_: *mut LeanObject,
    mut v_ref_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut v_unused_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_669_ = 0;
                v___x_670_ = l_Lean_Linter_registerSet___closed__0;
                v___x_671_ = l_Lean_Linter_registerSet___closed__1;
                v___x_672_ = lean_box(0);
                lean_inc_n(v_setName_666_, 2);
                v___x_673_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_673_, 0, v_setName_666_);
                lean_ctor_set(v___x_673_, 1, v_ref_667_);
                lean_ctor_set(v___x_673_, 2, v___x_670_);
                lean_ctor_set(v___x_673_, 3, v___x_671_);
                lean_ctor_set(v___x_673_, 4, v___x_672_);
                v___x_674_ = lean_register_option(v_setName_666_, v___x_673_);
                if lean_obj_tag(v___x_674_) == 0 {
                    v_isSharedCheck_683_ = (!lean_is_exclusive(v___x_674_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v_unused_684_ = lean_ctor_get(v___x_674_, 0);
                        lean_dec(v_unused_684_);
                        v___x_676_ = v___x_674_;
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_674_);
                        v___x_676_ = lean_box(0);
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_setName_666_);
                    v_a_685_ = lean_ctor_get(v___x_674_, 0);
                    v_isSharedCheck_692_ = (!lean_is_exclusive(v___x_674_)) as u8;
                    if v_isSharedCheck_692_ == 0 {
                        v___x_687_ = v___x_674_;
                        v_isShared_688_ = v_isSharedCheck_692_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_685_);
                        lean_dec(v___x_674_);
                        v___x_687_ = lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_692_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_678_ = lean_box((v___x_669_) as usize);
                v___x_679_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_679_, 0, v_setName_666_);
                lean_ctor_set(v___x_679_, 1, v___x_678_);
                if v_isShared_677_ == 0 {
                    lean_ctor_set(v___x_676_, 0, v___x_679_);
                    v___x_681_ = v___x_676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_681_;
            }
            3 => {
                if v_isShared_688_ == 0 {
                    v___x_690_ = v___x_687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
                    v___x_690_ = v_reuseFailAlloc_691_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_registerSet___boxed(
    mut v_setName_693_: *mut LeanObject,
    mut v_ref_694_: *mut LeanObject,
    mut v_a_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Linter_registerSet(v_setName_693_, v_ref_694_);
    return v_res_696_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = lean_box(0);
    v___x_756_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_757_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_757_, 0, v___x_756_);
    lean_ctor_set(v___x_757_, 1, v___x_755_);
    return v___x_757_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_759_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___closed__0);
    v___x_760_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_760_, 0, v___x_759_);
    return v___x_760_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg___boxed(
    mut v___y_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_762_: *mut LeanObject = core::ptr::null_mut();
    v_res_762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
    return v_res_762_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(
    mut v_00_u03b1_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
    return v___x_767_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___boxed(
    mut v_00_u03b1_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_772_: *mut LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0(v_00_u03b1_768_, v___y_769_, v___y_770_);
    lean_dec(v___y_770_);
    lean_dec_ref(v___y_769_);
    return v_res_772_;
}
pub unsafe fn l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(
    mut v_setName_773_: *mut LeanObject,
    mut v_linterNames_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_791_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_777_ = lean_st_ref_take(v___y_775_);
                v_env_778_ = lean_ctor_get(v___x_777_, 0);
                v_messages_779_ = lean_ctor_get(v___x_777_, 1);
                v_scopes_780_ = lean_ctor_get(v___x_777_, 2);
                v_usedQuotCtxts_781_ = lean_ctor_get(v___x_777_, 3);
                v_nextMacroScope_782_ = lean_ctor_get(v___x_777_, 4);
                v_maxRecDepth_783_ = lean_ctor_get(v___x_777_, 5);
                v_ngen_784_ = lean_ctor_get(v___x_777_, 6);
                v_auxDeclNGen_785_ = lean_ctor_get(v___x_777_, 7);
                v_infoState_786_ = lean_ctor_get(v___x_777_, 8);
                v_traceState_787_ = lean_ctor_get(v___x_777_, 9);
                v_snapshotTasks_788_ = lean_ctor_get(v___x_777_, 10);
                v_isSharedCheck_804_ = (!lean_is_exclusive(v___x_777_)) as u8;
                if v_isSharedCheck_804_ == 0 {
                    v___x_790_ = v___x_777_;
                    v_isShared_791_ = v_isSharedCheck_804_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_788_);
                    lean_inc(v_traceState_787_);
                    lean_inc(v_infoState_786_);
                    lean_inc(v_auxDeclNGen_785_);
                    lean_inc(v_ngen_784_);
                    lean_inc(v_maxRecDepth_783_);
                    lean_inc(v_nextMacroScope_782_);
                    lean_inc(v_usedQuotCtxts_781_);
                    lean_inc(v_scopes_780_);
                    lean_inc(v_messages_779_);
                    lean_inc(v_env_778_);
                    lean_dec(v___x_777_);
                    v___x_790_ = lean_box(0);
                    v_isShared_791_ = v_isSharedCheck_804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_792_ = l_Lean_Linter_linterSetsExt;
                v_toEnvExtension_793_ = lean_ctor_get(v___x_792_, 0);
                v_asyncMode_794_ = lean_ctor_get(v_toEnvExtension_793_, 2);
                v___x_795_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_795_, 0, v_setName_773_);
                lean_ctor_set(v___x_795_, 1, v_linterNames_774_);
                v___x_796_ = lean_box(0);
                v___x_797_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_792_,
                    v_env_778_,
                    v___x_795_,
                    v_asyncMode_794_,
                    v___x_796_,
                );
                if v_isShared_791_ == 0 {
                    lean_ctor_set(v___x_790_, 0, v___x_797_);
                    v___x_799_ = v___x_790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_797_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 1, v_messages_779_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 2, v_scopes_780_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 3, v_usedQuotCtxts_781_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 4, v_nextMacroScope_782_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 5, v_maxRecDepth_783_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 6, v_ngen_784_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 7, v_auxDeclNGen_785_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 8, v_infoState_786_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 9, v_traceState_787_);
                    lean_ctor_set(v_reuseFailAlloc_803_, 10, v_snapshotTasks_788_);
                    v___x_799_ = v_reuseFailAlloc_803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_800_ = lean_st_ref_set(v___y_775_, v___x_799_);
                v___x_801_ = lean_box(0);
                v___x_802_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_802_, 0, v___x_801_);
                return v___x_802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg___boxed(
    mut v_setName_805_: *mut LeanObject,
    mut v_linterNames_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_805_, v_linterNames_806_, v___y_807_);
    lean_dec(v___y_807_);
    return v_res_809_;
}
pub unsafe fn l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(
    mut v_setName_810_: *mut LeanObject,
    mut v_linterNames_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v_setName_810_, v_linterNames_811_, v___y_813_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___boxed(
    mut v_setName_816_: *mut LeanObject,
    mut v_linterNames_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
    mut v___y_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_821_: *mut LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1(v_setName_816_, v_linterNames_817_, v___y_818_, v___y_819_);
    lean_dec(v___y_819_);
    lean_dec_ref(v___y_818_);
    return v_res_821_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(
    mut v___y_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = lean_st_ref_get(v___y_822_);
    v_env_825_ = lean_ctor_get(v___x_824_, 0);
    lean_inc_ref(v_env_825_);
    lean_dec(v___x_824_);
    v___x_826_ = l_Lean_Environment_header(v_env_825_);
    lean_dec_ref(v_env_825_);
    v_mainModule_827_ = lean_ctor_get(v___x_826_, 0);
    lean_inc(v_mainModule_827_);
    lean_dec_ref(v___x_826_);
    v___x_828_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_828_, 0, v_mainModule_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg___boxed(
    mut v___y_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_831_: *mut LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_829_);
    lean_dec(v___y_829_);
    return v_res_831_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_835_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v___y_833_);
    return v___x_835_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___boxed(
    mut v___y_836_: *mut LeanObject,
    mut v___y_837_: *mut LeanObject,
    mut v___y_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_839_: *mut LeanObject = core::ptr::null_mut();
    v_res_839_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2(v___y_836_, v___y_837_);
    lean_dec(v___y_837_);
    lean_dec_ref(v___y_836_);
    return v_res_839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(
    mut v_as_840_: *mut LeanObject,
    mut v_i_841_: usize,
    mut v_stop_842_: usize,
    mut v_b_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: usize = 0;
    let mut v___x_849_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_844_ = lean_usize_dec_eq(v_i_841_, v_stop_842_);
                if v___x_844_ == 0 {
                    v___x_845_ = lean_array_uget_borrowed(v_as_840_, v_i_841_);
                    v___x_846_ = l_Lean_TSyntax_getId(v___x_845_);
                    v___x_847_ = l_Lean_NameSet_insert(v_b_843_, v___x_846_);
                    v___x_848_ = 1usize;
                    v___x_849_ = lean_usize_add(v_i_841_, v___x_848_);
                    v_i_841_ = v___x_849_;
                    v_b_843_ = v___x_847_;
                    state = 0;
                    continue;
                } else {
                    return v_b_843_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3___boxed(
    mut v_as_851_: *mut LeanObject,
    mut v_i_852_: *mut LeanObject,
    mut v_stop_853_: *mut LeanObject,
    mut v_b_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_855_: usize = 0;
    let mut v_stop_boxed_856_: usize = 0;
    let mut v_res_857_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
    lean_dec(v_i_852_);
    v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
    lean_dec(v_stop_853_);
    v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_as_851_, v_i_boxed_855_, v_stop_boxed_856_, v_b_854_);
    lean_dec_ref(v_as_851_);
    return v_res_857_;
}
pub unsafe fn _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6()
-> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__5;
    v___x_865_ = l_String_toRawSubstring_x27(v___x_864_);
    return v___x_865_;
}
pub unsafe fn _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14()
-> *mut LeanObject {
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    v___x_882_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__13;
    v___x_883_ = l_String_toRawSubstring_x27(v___x_882_);
    return v___x_883_;
}
pub unsafe fn _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25()
-> *mut LeanObject {
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    v___x_902_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__24;
    v___x_903_ = l_String_toRawSubstring_x27(v___x_902_);
    return v___x_903_;
}
pub unsafe fn _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38()
-> *mut LeanObject {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    v___x_931_ = l_Array_mkArray0(lean_box(0));
    return v___x_931_;
}
pub unsafe fn l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(
    mut v_x_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v_a_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_a_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: usize = 0;
    let mut v___x_1111_: usize = 0;
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: usize = 0;
    let mut v___x_1114_: usize = 0;
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1121_: u8 = 0;
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_969_ = l_Lean_Linter_registerSet___auto__1___closed__0;
                v___x_970_ = l_Lean_Linter_command__Register__linter__set___x3a_x3d___00__closed__2;
                lean_inc(v_x_932_);
                v___x_971_ = l_Lean_Syntax_isOfKind(v_x_932_, v___x_970_);
                if v___x_971_ == 0 {
                    lean_dec(v_x_932_);
                    v___x_972_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__0___redArg();
                    return v___x_972_;
                } else {
                    v___x_973_ = lean_unsigned_to_nat(0);
                    v___x_974_ = l_Lean_Syntax_getArg(v_x_932_, v___x_973_);
                    v___x_975_ = lean_unsigned_to_nat(2);
                    v_name_976_ = l_Lean_Syntax_getArg(v_x_932_, v___x_975_);
                    v___x_1100_ = lean_unsigned_to_nat(4);
                    v___x_1101_ = l_Lean_Syntax_getArg(v_x_932_, v___x_1100_);
                    lean_dec(v_x_932_);
                    v_decl_1102_ = l_Lean_Syntax_getArgs(v___x_1101_);
                    lean_dec(v___x_1101_);
                    v___x_1116_ = l_Lean_Syntax_getOptional_x3f(v___x_974_);
                    lean_dec(v___x_974_);
                    if lean_obj_tag(v___x_1116_) == 0 {
                        v___x_1117_ = lean_box(0);
                        v___y_1104_ = v___x_1117_;
                        state = 11;
                        continue;
                    } else {
                        v_val_1118_ = lean_ctor_get(v___x_1116_, 0);
                        v_isSharedCheck_1125_ = (!lean_is_exclusive(v___x_1116_)) as u8;
                        if v_isSharedCheck_1125_ == 0 {
                            v___x_1120_ = v___x_1116_;
                            v_isShared_1121_ = v_isSharedCheck_1125_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_val_1118_);
                            lean_dec(v___x_1116_);
                            v___x_1120_ = lean_box(0);
                            v_isShared_1121_ = v_isSharedCheck_1125_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v___y_946_);
                lean_inc_n(v___y_948_, 3);
                v___x_950_ = l_Lean_Syntax_node1(v___y_948_, v___y_946_, v___y_949_);
                v___x_951_ = l_Lean_Syntax_node2(v___y_948_, v___y_939_, v___y_938_, v___x_950_);
                v___x_952_ = l_Lean_Syntax_node1(v___y_948_, v___y_943_, v___x_951_);
                v___x_953_ = l_Lean_Elab_Command_getRef___redArg(v_a_933_);
                if lean_obj_tag(v___x_953_) == 0 {
                    v_a_954_ = lean_ctor_get(v___x_953_, 0);
                    lean_inc(v_a_954_);
                    lean_dec_ref_known(v___x_953_, 1);
                    lean_inc_n(v___y_948_, 3);
                    v___x_955_ =
                        l_Lean_Syntax_node2(v___y_948_, v___y_942_, v___x_952_, v___y_944_);
                    lean_inc(v___y_946_);
                    v___x_956_ = l_Lean_Syntax_node1(v___y_948_, v___y_946_, v___x_955_);
                    v___x_957_ = l_Lean_Syntax_node1(v___y_948_, v___y_940_, v___x_956_);
                    lean_inc(v___y_941_);
                    v___x_958_ = l_Lean_Syntax_node4(
                        v___y_948_, v___y_941_, v___y_945_, v___y_947_, v___y_937_, v___x_957_,
                    );
                    lean_inc(v___x_958_);
                    v___x_959_ = lean_alloc_closure(
                        l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    lean_closure_set(v___x_959_, 0, v___x_958_);
                    v___x_960_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                        v_a_954_, v___x_958_, v___x_959_, v_a_933_, v_a_934_,
                    );
                    return v___x_960_;
                } else {
                    lean_dec(v___x_952_);
                    lean_dec(v___y_948_);
                    lean_dec(v___y_947_);
                    lean_dec(v___y_945_);
                    lean_dec(v___y_944_);
                    lean_dec(v___y_942_);
                    lean_dec(v___y_940_);
                    lean_dec(v___y_937_);
                    v_a_961_ = lean_ctor_get(v___x_953_, 0);
                    v_isSharedCheck_968_ = (!lean_is_exclusive(v___x_953_)) as u8;
                    if v_isSharedCheck_968_ == 0 {
                        v___x_963_ = v___x_953_;
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_961_);
                        lean_dec(v___x_953_);
                        v___x_963_ = lean_box(0);
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_964_ == 0 {
                    v___x_966_ = v___x_963_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
                    v___x_966_ = v_reuseFailAlloc_967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_966_;
            }
            4 => {
                lean_inc_ref_n(v___y_980_, 2);
                v___x_990_ = l_Array_append___redArg(v___y_980_, v___y_989_);
                lean_dec_ref(v___y_989_);
                lean_inc_n(v___y_979_, 5);
                lean_inc_n(v___y_988_, 17);
                v___x_991_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_991_, 0, v___y_988_);
                lean_ctor_set(v___x_991_, 1, v___y_979_);
                lean_ctor_set(v___x_991_, 2, v___x_990_);
                v___x_992_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_992_, 0, v___y_988_);
                lean_ctor_set(v___x_992_, 1, v___y_979_);
                lean_ctor_set(v___x_992_, 2, v___y_980_);
                v___x_993_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__0;
                lean_inc_ref_n(v___y_984_, 2);
                lean_inc_ref_n(v___y_987_, 7);
                v___x_994_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___y_984_, v___x_993_);
                v___x_995_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_995_, 0, v___y_988_);
                lean_ctor_set(v___x_995_, 1, v___x_993_);
                v___x_996_ = l_Lean_Syntax_node1(v___y_988_, v___x_994_, v___x_995_);
                v___x_997_ = l_Lean_Syntax_node1(v___y_988_, v___y_979_, v___x_996_);
                lean_inc_ref_n(v___x_992_, 5);
                lean_inc(v___y_983_);
                v___x_998_ = l_Lean_Syntax_node7(
                    v___y_988_, v___y_983_, v___x_991_, v___x_992_, v___x_992_, v___x_992_,
                    v___x_997_, v___x_992_, v___x_992_,
                );
                v___x_999_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__1;
                v___x_1000_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___y_984_, v___x_999_);
                lean_inc_ref(v___y_978_);
                v___x_1001_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1001_, 0, v___y_988_);
                lean_ctor_set(v___x_1001_, 1, v___y_978_);
                v___x_1002_ = l_Lean_Syntax_node1(v___y_988_, v___x_1000_, v___x_1001_);
                v___x_1003_ = l_Lean_Linter_registerSet___auto__1___closed__14;
                v___x_1004_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__2;
                v___x_1005_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1004_);
                v___x_1006_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__3;
                v___x_1007_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1007_, 0, v___y_988_);
                lean_ctor_set(v___x_1007_, 1, v___x_1006_);
                v___x_1008_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__4;
                v___x_1009_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1008_);
                v___x_1010_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6), core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6_once), _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__6);
                v___x_1011_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__8;
                lean_inc_n(v___y_982_, 2);
                lean_inc_n(v___y_981_, 2);
                v___x_1012_ = l_Lean_addMacroScope(v___y_981_, v___x_1011_, v___y_982_);
                v___x_1013_ = lean_box(0);
                v___x_1014_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__12;
                v___x_1015_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1015_, 0, v___y_988_);
                lean_ctor_set(v___x_1015_, 1, v___x_1010_);
                lean_ctor_set(v___x_1015_, 2, v___x_1012_);
                lean_ctor_set(v___x_1015_, 3, v___x_1014_);
                v___x_1016_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14), core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14_once), _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__14);
                v___x_1017_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__15;
                v___x_1018_ = l_Lean_addMacroScope(v___y_981_, v___x_1017_, v___y_982_);
                v___x_1019_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__19;
                v___x_1020_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1020_, 0, v___y_988_);
                lean_ctor_set(v___x_1020_, 1, v___x_1016_);
                lean_ctor_set(v___x_1020_, 2, v___x_1018_);
                lean_ctor_set(v___x_1020_, 3, v___x_1019_);
                v___x_1021_ = l_Lean_Syntax_node1(v___y_988_, v___y_979_, v___x_1020_);
                lean_inc(v___x_1009_);
                v___x_1022_ =
                    l_Lean_Syntax_node2(v___y_988_, v___x_1009_, v___x_1015_, v___x_1021_);
                v___x_1023_ =
                    l_Lean_Syntax_node2(v___y_988_, v___x_1005_, v___x_1007_, v___x_1022_);
                v___x_1024_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__20;
                v___x_1025_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1025_, 0, v___y_988_);
                lean_ctor_set(v___x_1025_, 1, v___x_1024_);
                v___x_1026_ = l_Lean_Syntax_node3(
                    v___y_988_,
                    v___y_979_,
                    v_name_976_,
                    v___x_1023_,
                    v___x_1025_,
                );
                v___x_1027_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__21;
                v___x_1028_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1027_);
                v___x_1029_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__22;
                v___x_1030_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1029_);
                v___x_1031_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__23;
                v___x_1032_ = l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1031_);
                v___x_1033_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25), core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25_once), _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__25);
                v___x_1034_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__27;
                v___x_1035_ = l_Lean_addMacroScope(v___y_981_, v___x_1034_, v___y_982_);
                v___x_1036_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__29;
                v___x_1037_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1037_, 0, v___y_988_);
                lean_ctor_set(v___x_1037_, 1, v___x_1033_);
                lean_ctor_set(v___x_1037_, 2, v___x_1035_);
                lean_ctor_set(v___x_1037_, 3, v___x_1036_);
                lean_inc(v___y_986_);
                v___x_1038_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_1013_,
                    v___y_986_,
                );
                if lean_obj_tag(v___x_1038_) == 0 {
                    v___x_1039_ = l_Lean_quoteNameMk(v___y_986_);
                    v___y_937_ = v___x_1026_;
                    v___y_938_ = v___x_1037_;
                    v___y_939_ = v___x_1009_;
                    v___y_940_ = v___x_1028_;
                    v___y_941_ = v___y_985_;
                    v___y_942_ = v___x_1030_;
                    v___y_943_ = v___x_1032_;
                    v___y_944_ = v___x_992_;
                    v___y_945_ = v___x_998_;
                    v___y_946_ = v___y_979_;
                    v___y_947_ = v___x_1002_;
                    v___y_948_ = v___y_988_;
                    v___y_949_ = v___x_1039_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_986_);
                    v_val_1040_ = lean_ctor_get(v___x_1038_, 0);
                    lean_inc(v_val_1040_);
                    lean_dec_ref_known(v___x_1038_, 1);
                    v___x_1041_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__30;
                    lean_inc_ref(v___y_987_);
                    v___x_1042_ =
                        l_Lean_Name_mkStr4(v___x_969_, v___y_987_, v___x_1003_, v___x_1041_);
                    v___x_1043_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__31;
                    v___x_1044_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__32;
                    v___x_1045_ = lean_string_intercalate(v___x_1044_, v_val_1040_);
                    v___x_1046_ = lean_string_append(v___x_1043_, v___x_1045_);
                    lean_dec_ref(v___x_1045_);
                    v___x_1047_ = lean_box(2);
                    v___x_1048_ = l_Lean_Syntax_mkNameLit(v___x_1046_, v___x_1047_);
                    v___x_1049_ = lean_unsigned_to_nat(1);
                    v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
                    v___x_1051_ = lean_array_push(v___x_1050_, v___x_1048_);
                    v___x_1052_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1052_, 0, v___x_1047_);
                    lean_ctor_set(v___x_1052_, 1, v___x_1042_);
                    lean_ctor_set(v___x_1052_, 2, v___x_1051_);
                    v___y_937_ = v___x_1026_;
                    v___y_938_ = v___x_1037_;
                    v___y_939_ = v___x_1009_;
                    v___y_940_ = v___x_1028_;
                    v___y_941_ = v___y_985_;
                    v___y_942_ = v___x_1030_;
                    v___y_943_ = v___x_1032_;
                    v___y_944_ = v___x_992_;
                    v___y_945_ = v___x_998_;
                    v___y_946_ = v___y_979_;
                    v___y_947_ = v___x_1002_;
                    v___y_948_ = v___y_988_;
                    v___y_949_ = v___x_1052_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1059_ = l_Lean_Linter_registerSet___auto__1___closed__1;
                v___x_1060_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__33;
                v___x_1061_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__34;
                v___x_1062_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__35;
                v___x_1063_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__37;
                v___x_1064_ = l_Lean_Linter_registerSet___auto__1___closed__9;
                v___x_1065_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38), core::ptr::addr_of_mut!(l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38_once), _init_l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___closed__38);
                if lean_obj_tag(v___y_1055_) == 1 {
                    v_val_1066_ = lean_ctor_get(v___y_1055_, 0);
                    lean_inc(v_val_1066_);
                    lean_dec_ref_known(v___y_1055_, 1);
                    v___x_1067_ = l_Array_mkArray1___redArg(v_val_1066_);
                    v___y_978_ = v___x_1061_;
                    v___y_979_ = v___x_1064_;
                    v___y_980_ = v___x_1065_;
                    v___y_981_ = v_a_1058_;
                    v___y_982_ = v___y_1054_;
                    v___y_983_ = v___x_1063_;
                    v___y_984_ = v___x_1060_;
                    v___y_985_ = v___x_1062_;
                    v___y_986_ = v___y_1056_;
                    v___y_987_ = v___x_1059_;
                    v___y_988_ = v___y_1057_;
                    v___y_989_ = v___x_1067_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_1055_);
                    v___x_1068_ = l_Lean_Linter_registerSet___auto__1___closed__5;
                    v___y_978_ = v___x_1061_;
                    v___y_979_ = v___x_1064_;
                    v___y_980_ = v___x_1065_;
                    v___y_981_ = v_a_1058_;
                    v___y_982_ = v___y_1054_;
                    v___y_983_ = v___x_1063_;
                    v___y_984_ = v___x_1060_;
                    v___y_985_ = v___x_1062_;
                    v___y_986_ = v___y_1056_;
                    v___y_987_ = v___x_1059_;
                    v___y_988_ = v___y_1057_;
                    v___y_989_ = v___x_1068_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc(v___y_1071_);
                v___x_1073_ = l_Lean_Linter_insertLinterSet___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__1___redArg(v___y_1071_, v___y_1072_, v_a_934_);
                lean_dec_ref(v___x_1073_);
                v___x_1074_ = l_Lean_Elab_Command_getRef___redArg(v_a_933_);
                if lean_obj_tag(v___x_1074_) == 0 {
                    v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
                    lean_inc(v_a_1075_);
                    lean_dec_ref_known(v___x_1074_, 1);
                    v___x_1076_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_933_);
                    if lean_obj_tag(v___x_1076_) == 0 {
                        v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
                        lean_inc(v_a_1077_);
                        lean_dec_ref_known(v___x_1076_, 1);
                        v_quotContext_x3f_1078_ = lean_ctor_get(v_a_933_, 5);
                        v___x_1079_ = 0;
                        v___x_1080_ = l_Lean_SourceInfo_fromRef(v_a_1075_, v___x_1079_);
                        lean_dec(v_a_1075_);
                        if lean_obj_tag(v_quotContext_x3f_1078_) == 0 {
                            v___x_1081_ = l_Lean_getMainModule___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__2___redArg(v_a_934_);
                            v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
                            lean_inc(v_a_1082_);
                            lean_dec_ref(v___x_1081_);
                            v___y_1054_ = v_a_1077_;
                            v___y_1055_ = v___y_1070_;
                            v___y_1056_ = v___y_1071_;
                            v___y_1057_ = v___x_1080_;
                            v_a_1058_ = v_a_1082_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1083_ = lean_ctor_get(v_quotContext_x3f_1078_, 0);
                            lean_inc(v_val_1083_);
                            v___y_1054_ = v_a_1077_;
                            v___y_1055_ = v___y_1070_;
                            v___y_1056_ = v___y_1071_;
                            v___y_1057_ = v___x_1080_;
                            v_a_1058_ = v_val_1083_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1075_);
                        lean_dec(v___y_1071_);
                        lean_dec(v___y_1070_);
                        lean_dec(v_name_976_);
                        v_a_1084_ = lean_ctor_get(v___x_1076_, 0);
                        v_isSharedCheck_1091_ = (!lean_is_exclusive(v___x_1076_)) as u8;
                        if v_isSharedCheck_1091_ == 0 {
                            v___x_1086_ = v___x_1076_;
                            v_isShared_1087_ = v_isSharedCheck_1091_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1084_);
                            lean_dec(v___x_1076_);
                            v___x_1086_ = lean_box(0);
                            v_isShared_1087_ = v_isSharedCheck_1091_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_1071_);
                    lean_dec(v___y_1070_);
                    lean_dec(v_name_976_);
                    v_a_1092_ = lean_ctor_get(v___x_1074_, 0);
                    v_isSharedCheck_1099_ = (!lean_is_exclusive(v___x_1074_)) as u8;
                    if v_isSharedCheck_1099_ == 0 {
                        v___x_1094_ = v___x_1074_;
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1092_);
                        lean_dec(v___x_1074_);
                        v___x_1094_ = lean_box(0);
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1087_ == 0 {
                    v___x_1089_ = v___x_1086_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
                    v___x_1089_ = v_reuseFailAlloc_1090_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1089_;
            }
            9 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1097_;
            }
            11 => {
                v___x_1105_ = l_Lean_TSyntax_getId(v_name_976_);
                v___x_1106_ = l_Lean_NameSet_empty;
                v___x_1107_ = lean_array_get_size(v_decl_1102_);
                v___x_1108_ = lean_nat_dec_lt(v___x_973_, v___x_1107_);
                if v___x_1108_ == 0 {
                    lean_dec_ref(v_decl_1102_);
                    v___y_1070_ = v___y_1104_;
                    v___y_1071_ = v___x_1105_;
                    v___y_1072_ = v___x_1106_;
                    state = 6;
                    continue;
                } else {
                    v___x_1109_ = lean_nat_dec_le(v___x_1107_, v___x_1107_);
                    if v___x_1109_ == 0 {
                        if v___x_1108_ == 0 {
                            lean_dec_ref(v_decl_1102_);
                            v___y_1070_ = v___y_1104_;
                            v___y_1071_ = v___x_1105_;
                            v___y_1072_ = v___x_1106_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1110_ = 0usize;
                            v___x_1111_ = lean_usize_of_nat(v___x_1107_);
                            v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_1102_, v___x_1110_, v___x_1111_, v___x_1106_);
                            lean_dec_ref(v_decl_1102_);
                            v___y_1070_ = v___y_1104_;
                            v___y_1071_ = v___x_1105_;
                            v___y_1072_ = v___x_1112_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1113_ = 0usize;
                        v___x_1114_ = lean_usize_of_nat(v___x_1107_);
                        v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1_spec__3(v_decl_1102_, v___x_1113_, v___x_1114_, v___x_1106_);
                        lean_dec_ref(v_decl_1102_);
                        v___y_1070_ = v___y_1104_;
                        v___y_1071_ = v___x_1105_;
                        v___y_1072_ = v___x_1115_;
                        state = 6;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_1121_ == 0 {
                    v___x_1123_ = v___x_1120_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1118_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_1104_ = v___x_1123_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1___boxed(
    mut v_x_1126_: *mut LeanObject,
    mut v_a_1127_: *mut LeanObject,
    mut v_a_1128_: *mut LeanObject,
    mut v_a_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_Linter___aux__Lean__Linter__Sets______elabRules__Lean__Linter__command__Register__linter__set___x3a_x3d____1(v_x_1126_, v_a_1127_, v_a_1128_);
    lean_dec(v_a_1128_);
    lean_dec_ref(v_a_1127_);
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Sets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Sets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Linter_registerSet___auto__1 = _init_l_Lean_Linter_registerSet___auto__1();
    lean_mark_persistent(l_Lean_Linter_registerSet___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Sets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Sets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Sets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Sets(builtin);
}
