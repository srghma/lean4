// Lean compiler output
// Module: Lean.Language.Basic
// Imports: Lean.Parser.Types Lean.Util.Trace
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_set;
use crate::r#gen::Init::System::IO::{l_BaseIO_chainTask___redArg, l_instMonadBaseIO};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Message::{
    l_Lean_Message_toJson, l_Lean_Message_toString, l_Lean_MessageData_kind,
    l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add, l_Lean_MessageLog_empty,
    l_Lean_instInhabitedMessageLog_default,
};
use crate::r#gen::Lean::Parser::Types::{
    initialize_Lean_Parser_Types, runtime_initialize_Lean_Parser_Types,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::r#gen::Lean::Util::Trace::{
    initialize_Lean_Util_Trace, runtime_initialize_Lean_Util_Trace,
};
use crate::lean_imports_rs::Init::Core::{
    lean_mk_thunk, lean_task_get_own, lean_task_map, lean_task_pure, lean_thunk_get_own,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_get_stdout, lean_io_as_task, lean_io_bind_task, lean_io_exit, lean_io_get_task_state,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_Snapshot_instInhabitedDiagnostics_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_Snapshot_instInhabitedDiagnostics: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_Diagnostics_empty___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_Diagnostics_empty___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_Snapshot_Diagnostics_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__3_value: LeanStringObject<10> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__6_value: LeanStringObject<19> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__10_value: LeanStringObject<6> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__14_value: LeanStringObject<5> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__15_value: LeanStringObject<5> =
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
        m_data: [112, 114, 111, 106, 0],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__15_value)
        as *mut LeanObject;
static l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__16_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__15_value)
                as *mut LeanObject,
            5353940006376281447 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__17_value: LeanStringObject<9> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__17_value)
        as *mut LeanObject;
static l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__18_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__17_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__19_value: LeanStringObject<11> =
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
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__24_value: LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__24_value)
        as *mut LeanObject;
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__27_value: LeanStringObject<9> =
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
        m_data: [116, 111, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__27_value)
        as *mut LeanObject;
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__29: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Language_Snapshot_desc___autoParam___closed__30_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__27_value)
                as *mut LeanObject,
            16359081359533231919 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__30_value)
        as *mut LeanObject;
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__32_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__32: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__33_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__33: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__34: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__35_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__35: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__36_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__36: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__37_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__37: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__38_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__38: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__39_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__39: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__40_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__40: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__41_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_Snapshot_desc___autoParam___closed__41: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_Snapshot_desc___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_instInhabitedSnapshot___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_Lean_Language_instInhabitedSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instInhabitedSnapshot___closed__0_value) as *mut LeanObject;
static mut l_Lean_Language_instInhabitedSnapshot___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_instInhabitedSnapshot___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedSnapshot___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_instInhabitedSnapshot___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedSnapshot___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_instInhabitedSnapshot___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedSnapshot___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_instInhabitedSnapshot___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_instInhabitedSnapshot: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_SnapshotTask_instInhabitedReportingRange: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Language_instInhabitedSnapshotTree_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Language_instInhabitedSnapshotTree_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_instInhabitedSnapshotTree_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_instInhabitedSnapshotTree_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_instInhabitedSnapshotTree: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 97, 110, 103, 117, 97, 103, 101, 0]};
static mut l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject;
pub static l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 110, 97, 112, 115, 104, 111, 116, 84, 114, 101, 101, 0]};
static mut l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject;
static l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,3837182057242778601 as *mut LeanObject] };
static mut l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject;
pub static mut l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject;
pub static mut l_Lean_Language_instTypeNameSnapshotTree: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__2_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject;
pub static l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Language_instToSnapshotTreeSnapshotTree: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 110, 97, 112, 115, 104, 111, 116, 76, 101, 97, 102, 0]};
static mut l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value) as *mut LeanObject;
static l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value) as *mut LeanObject,15748072023678771857 as *mut LeanObject] };
static mut l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value) as *mut LeanObject;
pub static mut l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value) as *mut LeanObject;
pub static mut l_Lean_Language_instTypeNameSnapshotLeaf: *mut LeanObject = core::ptr::addr_of!(l_Lean_Language_instImpl___closed__1_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8__value) as *mut LeanObject;
pub static mut l_Lean_Language_instInhabitedSnapshotLeaf: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Language_instToSnapshotTreeSnapshotLeaf: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Language_instToSnapshotTreeDynamicSnapshot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instToSnapshotTreeDynamicSnapshot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            105, 110, 115, 116, 73, 110, 104, 97, 98, 105, 116, 101, 100, 68, 121, 110, 97, 109,
            105, 99, 83, 110, 97, 112, 115, 104, 111, 116, 0,
        ],
    };
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value)
        as *mut LeanObject;
static l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__0_value)
                as *mut LeanObject,
            1077705206801492438 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_instInhabitedDynamicSnapshot___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Language_instInhabitedDynamicSnapshot: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [112, 114, 105, 110, 116, 77, 101, 115, 115, 97, 103, 101, 69, 110, 100, 80, 111, 115, 0]};
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject,11988155218388915588 as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value: LeanStringObject<65> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [112, 114, 105, 110, 116, 32, 101, 110, 100, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 102, 32, 101, 97, 99, 104, 32, 109, 101, 115, 115, 97, 103, 101, 32, 105, 110, 32, 97, 100, 100, 105, 116, 105, 111, 110, 32, 116, 111, 32, 115, 116, 97, 114, 116, 32, 112, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject,839976593828347172 as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 120, 69, 114, 114, 111, 114, 115, 0]};
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject,2956820979458826725 as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 101, 114, 114, 111, 114, 115, 32, 116, 111, 32, 114, 101, 112, 111, 114, 116, 32, 40, 48, 32, 102, 111, 114, 32, 110, 111, 32, 108, 105, 109, 105, 116, 41, 0]};
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 100 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__2_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__0_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject,7318154112456167237 as *mut LeanObject] };
static mut l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 101, 114, 114, 111, 114, 115, 32, 40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1_value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [59, 32, 102, 114, 111, 109, 32, 111, 112, 116, 105, 111, 110, 32, 96, 109, 97, 120, 69, 114, 114, 111, 114, 115, 96, 41, 32, 114, 101, 97, 99, 104, 101, 100, 44, 32, 101, 120, 105, 116, 105, 110, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_SnapshotTree_getAll___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Language_SnapshotTree_getAll___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_SnapshotTree_getAll___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Language_instMonadLiftProcessingMProcessingTIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_instMonadLiftProcessingMProcessingTIO___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_diagnosticsOfHeaderError___closed__0_value: LeanStringObject<8> =
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
        m_data: [60, 105, 110, 112, 117, 116, 62, 0],
    };
static mut l_Lean_Language_diagnosticsOfHeaderError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_diagnosticsOfHeaderError___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Language_diagnosticsOfHeaderError___closed__1_value: LeanCtorObject<2> =
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
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_diagnosticsOfHeaderError___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_diagnosticsOfHeaderError___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Language_withHeaderExceptions___redArg___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            119, 105, 116, 104, 72, 101, 97, 100, 101, 114, 69, 120, 99, 101, 112, 116, 105, 111,
            110, 115, 0,
        ],
    };
static mut l_Lean_Language_withHeaderExceptions___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_withHeaderExceptions___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Language_Snapshot_desc___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Language_instImpl___closed__0_00___x40_Lean_Language_Basic_3470488393____hygCtx___hyg_29__value) as *mut LeanObject,6140912203723220827 as *mut LeanObject] };
pub static l_Lean_Language_withHeaderExceptions___redArg___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Language_withHeaderExceptions___redArg___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Language_withHeaderExceptions___redArg___closed__0_value)
                as *mut LeanObject,
            12827333135366695081 as *mut LeanObject,
        ],
    };
static mut l_Lean_Language_withHeaderExceptions___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Language_withHeaderExceptions___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Language_withHeaderExceptions___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Language_withHeaderExceptions___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0()
-> *mut LeanObject {
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = lean_box(0);
    v___x_1452_ = l_Lean_instInhabitedMessageLog_default;
    v___x_1453_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1453_, 0, v___x_1452_);
    lean_ctor_set(v___x_1453_, 1, v___x_1451_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default() -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0_once
        ),
        _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0,
    );
    return v___x_1454_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics() -> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
    return v___x_1455_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0() -> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1456_ = lean_box(0);
    v___x_1457_ = l_Lean_MessageLog_empty;
    v___x_1458_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_Diagnostics_empty() -> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_Diagnostics_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_Diagnostics_empty___closed__0_once),
        _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0,
    );
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12() -> *mut LeanObject {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    v___x_1486_ = l_Lean_Language_Snapshot_desc___autoParam___closed__10;
    v___x_1487_ = l_Lean_mkAtom(v___x_1486_);
    return v___x_1487_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13() -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    v___x_1488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__12_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12,
    );
    v___x_1489_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1490_ = lean_array_push(v___x_1489_, v___x_1488_);
    return v___x_1490_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20() -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1505_ = l_Lean_Language_Snapshot_desc___autoParam___closed__19;
    v___x_1506_ = l_Lean_mkAtom(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21() -> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    v___x_1507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__20_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20,
    );
    v___x_1508_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1509_ = lean_array_push(v___x_1508_, v___x_1507_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22() -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1510_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__21_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21,
    );
    v___x_1511_ = l_Lean_Language_Snapshot_desc___autoParam___closed__18;
    v___x_1512_ = lean_box(2);
    v___x_1513_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23() -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__22_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22,
    );
    v___x_1515_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1516_ = lean_array_push(v___x_1515_, v___x_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25() -> *mut LeanObject {
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    v___x_1518_ = l_Lean_Language_Snapshot_desc___autoParam___closed__24;
    v___x_1519_ = l_Lean_mkAtom(v___x_1518_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26() -> *mut LeanObject {
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    v___x_1520_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__25_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25,
    );
    v___x_1521_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__23_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23,
    );
    v___x_1522_ = lean_array_push(v___x_1521_, v___x_1520_);
    return v___x_1522_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28() -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lean_Language_Snapshot_desc___autoParam___closed__27;
    v___x_1525_ = lean_string_utf8_byte_size(v___x_1524_);
    return v___x_1525_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29() -> *mut LeanObject {
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    v___x_1526_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__28_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28,
    );
    v___x_1527_ = lean_unsigned_to_nat(0);
    v___x_1528_ = l_Lean_Language_Snapshot_desc___autoParam___closed__27;
    v___x_1529_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1529_, 0, v___x_1528_);
    lean_ctor_set(v___x_1529_, 1, v___x_1527_);
    lean_ctor_set(v___x_1529_, 2, v___x_1526_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31() -> *mut LeanObject {
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v___x_1532_ = lean_box(0);
    v___x_1533_ = l_Lean_Language_Snapshot_desc___autoParam___closed__30;
    v___x_1534_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__29_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29,
    );
    v___x_1535_ = lean_box(2);
    v___x_1536_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_1536_, 0, v___x_1535_);
    lean_ctor_set(v___x_1536_, 1, v___x_1534_);
    lean_ctor_set(v___x_1536_, 2, v___x_1533_);
    lean_ctor_set(v___x_1536_, 3, v___x_1532_);
    return v___x_1536_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32() -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__31_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31,
    );
    v___x_1538_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__26_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26,
    );
    v___x_1539_ = lean_array_push(v___x_1538_, v___x_1537_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33() -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__32_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32,
    );
    v___x_1541_ = l_Lean_Language_Snapshot_desc___autoParam___closed__16;
    v___x_1542_ = lean_box(2);
    v___x_1543_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1543_, 0, v___x_1542_);
    lean_ctor_set(v___x_1543_, 1, v___x_1541_);
    lean_ctor_set(v___x_1543_, 2, v___x_1540_);
    return v___x_1543_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34() -> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__33_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33,
    );
    v___x_1545_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__13_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13,
    );
    v___x_1546_ = lean_array_push(v___x_1545_, v___x_1544_);
    return v___x_1546_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35() -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__34_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34,
    );
    v___x_1548_ = l_Lean_Language_Snapshot_desc___autoParam___closed__11;
    v___x_1549_ = lean_box(2);
    v___x_1550_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1550_, 0, v___x_1549_);
    lean_ctor_set(v___x_1550_, 1, v___x_1548_);
    lean_ctor_set(v___x_1550_, 2, v___x_1547_);
    return v___x_1550_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36() -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__35_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35,
    );
    v___x_1552_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1553_ = lean_array_push(v___x_1552_, v___x_1551_);
    return v___x_1553_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37() -> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__36_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36,
    );
    v___x_1555_ = l_Lean_Language_Snapshot_desc___autoParam___closed__9;
    v___x_1556_ = lean_box(2);
    v___x_1557_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    lean_ctor_set(v___x_1557_, 1, v___x_1555_);
    lean_ctor_set(v___x_1557_, 2, v___x_1554_);
    return v___x_1557_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38() -> *mut LeanObject {
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    v___x_1558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__37_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37,
    );
    v___x_1559_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1560_ = lean_array_push(v___x_1559_, v___x_1558_);
    return v___x_1560_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39() -> *mut LeanObject {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    v___x_1561_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__38_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38,
    );
    v___x_1562_ = l_Lean_Language_Snapshot_desc___autoParam___closed__7;
    v___x_1563_ = lean_box(2);
    v___x_1564_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1564_, 0, v___x_1563_);
    lean_ctor_set(v___x_1564_, 1, v___x_1562_);
    lean_ctor_set(v___x_1564_, 2, v___x_1561_);
    return v___x_1564_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40() -> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1565_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__39_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39,
    );
    v___x_1566_ = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
    v___x_1567_ = lean_array_push(v___x_1566_, v___x_1565_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41() -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__40_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40,
    );
    v___x_1569_ = l_Lean_Language_Snapshot_desc___autoParam___closed__4;
    v___x_1570_ = lean_box(2);
    v___x_1571_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1571_, 0, v___x_1570_);
    lean_ctor_set(v___x_1571_, 1, v___x_1569_);
    lean_ctor_set(v___x_1571_, 2, v___x_1568_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Lean_Language_Snapshot_desc___autoParam() -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Language_Snapshot_desc___autoParam___closed__41_once),
        _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41,
    );
    return v___x_1572_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshot___closed__1() -> *mut LeanObject {
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1574_ = lean_unsigned_to_nat(32);
    v___x_1575_ = lean_mk_empty_array_with_capacity(v___x_1574_);
    v___x_1576_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1576_, 0, v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshot___closed__2() -> *mut LeanObject {
    let mut v___x_1577_: usize = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    v___x_1577_ = 5usize;
    v___x_1578_ = lean_unsigned_to_nat(0);
    v___x_1579_ = lean_unsigned_to_nat(32);
    v___x_1580_ = lean_mk_empty_array_with_capacity(v___x_1579_);
    v___x_1581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__1_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__1,
    );
    v___x_1582_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    lean_ctor_set(v___x_1582_, 1, v___x_1580_);
    lean_ctor_set(v___x_1582_, 2, v___x_1578_);
    lean_ctor_set(v___x_1582_, 3, v___x_1578_);
    lean_ctor_set_usize(v___x_1582_, 4, v___x_1577_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshot___closed__3() -> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u64 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__2_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__2,
    );
    v___x_1584_ = 0u64;
    v___x_1585_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_1585_, 0, v___x_1583_);
    lean_ctor_set_uint64(
        v___x_1585_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1584_,
    );
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshot___closed__4() -> *mut LeanObject {
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ = 0;
    v___x_1587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__3,
    );
    v___x_1588_ = lean_box(0);
    v___x_1589_ = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
    v___x_1590_ = l_Lean_Language_instInhabitedSnapshot___closed__0;
    v___x_1591_ = lean_alloc_ctor(0, 4, (1) as u32);
    lean_ctor_set(v___x_1591_, 0, v___x_1590_);
    lean_ctor_set(v___x_1591_, 1, v___x_1589_);
    lean_ctor_set(v___x_1591_, 2, v___x_1588_);
    lean_ctor_set(v___x_1591_, 3, v___x_1587_);
    lean_ctor_set_uint8(
        v___x_1591_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_1586_,
    );
    return v___x_1591_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshot() -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__4,
    );
    return v___x_1592_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(
    mut v_x_1593_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1593_) {
        0 => {
            let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
            v___x_1594_ = lean_unsigned_to_nat(0);
            return v___x_1594_;
        }
        1 => {
            let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
            v___x_1595_ = lean_unsigned_to_nat(1);
            return v___x_1595_;
        }
        _ => {
            let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
            v___x_1596_ = lean_unsigned_to_nat(2);
            return v___x_1596_;
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(
    mut v_x_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(v_x_1597_);
    lean_dec(v_x_1597_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(
    mut v_t_1599_: *mut LeanObject,
    mut v_k_1600_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1599_) == 1 {
        let mut v_range_1601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
        v_range_1601_ = lean_ctor_get(v_t_1599_, 0);
        lean_inc_ref(v_range_1601_);
        lean_dec_ref_known(v_t_1599_, 1);
        v___x_1602_ = lean_apply_1(v_k_1600_, v_range_1601_);
        return v___x_1602_;
    } else {
        lean_dec(v_t_1599_);
        return v_k_1600_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(
    mut v_motive_1603_: *mut LeanObject,
    mut v_ctorIdx_1604_: *mut LeanObject,
    mut v_t_1605_: *mut LeanObject,
    mut v_h_1606_: *mut LeanObject,
    mut v_k_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1605_, v_k_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(
    mut v_motive_1609_: *mut LeanObject,
    mut v_ctorIdx_1610_: *mut LeanObject,
    mut v_t_1611_: *mut LeanObject,
    mut v_h_1612_: *mut LeanObject,
    mut v_k_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1614_: *mut LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(
        v_motive_1609_,
        v_ctorIdx_1610_,
        v_t_1611_,
        v_h_1612_,
        v_k_1613_,
    );
    lean_dec(v_ctorIdx_1610_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(
    mut v_t_1615_: *mut LeanObject,
    mut v_inherit_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1615_, v_inherit_1616_);
    return v___x_1617_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(
    mut v_motive_1618_: *mut LeanObject,
    mut v_t_1619_: *mut LeanObject,
    mut v_h_1620_: *mut LeanObject,
    mut v_inherit_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1619_, v_inherit_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(
    mut v_t_1623_: *mut LeanObject,
    mut v_some_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1623_, v_some_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_some_elim(
    mut v_motive_1626_: *mut LeanObject,
    mut v_t_1627_: *mut LeanObject,
    mut v_h_1628_: *mut LeanObject,
    mut v_some_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    v___x_1630_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1627_, v_some_1629_);
    return v___x_1630_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(
    mut v_t_1631_: *mut LeanObject,
    mut v_skip_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1631_, v_skip_1632_);
    return v___x_1633_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(
    mut v_motive_1634_: *mut LeanObject,
    mut v_t_1635_: *mut LeanObject,
    mut v_h_1636_: *mut LeanObject,
    mut v_skip_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ =
        l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(v_t_1635_, v_skip_1637_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default()
-> *mut LeanObject {
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    v___x_1639_ = lean_box(0);
    return v___x_1639_;
}
pub unsafe fn _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange() -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = lean_box(0);
    return v___x_1640_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(
    mut v_x_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1641_) == 0 {
                    v___x_1642_ = lean_box(0);
                    return v___x_1642_;
                } else {
                    v_val_1643_ = lean_ctor_get(v_x_1641_, 0);
                    v_isSharedCheck_1650_ = (!lean_is_exclusive(v_x_1641_)) as u8;
                    if v_isSharedCheck_1650_ == 0 {
                        v___x_1645_ = v_x_1641_;
                        v_isShared_1646_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1643_);
                        lean_dec(v_x_1641_);
                        v___x_1645_ = lean_box(0);
                        v_isShared_1646_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1646_ == 0 {
                    v___x_1648_ = v___x_1645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1643_);
                    v___x_1648_ = v_reuseFailAlloc_1649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0()
-> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = lean_box(0);
    v___x_1652_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_defaultReportingRange(
    mut v_stx_x3f_1653_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_stx_x3f_1653_) == 0 {
        let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
        v___x_1654_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0_once
            ),
            _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0,
        );
        return v___x_1654_;
    } else {
        let mut v_val_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: u8 = 0;
        let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
        v_val_1655_ = lean_ctor_get(v_stx_x3f_1653_, 0);
        v___x_1656_ = 1;
        v___x_1657_ = l_Lean_Syntax_getRange_x3f(v_val_1655_, v___x_1656_);
        v___x_1658_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___x_1657_);
        return v___x_1658_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(
    mut v_stx_x3f_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1660_: *mut LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v_stx_x3f_1659_);
    lean_dec(v_stx_x3f_1659_);
    return v_res_1660_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = lean_box(0);
    v___x_1662_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Lean_Language_instInhabitedSnapshotTask_default___redArg(
    mut v_inst_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1664_ = lean_box(0);
    v___x_1665_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0_once
        ),
        _init_l_Lean_Language_instInhabitedSnapshotTask_default___redArg___closed__0,
    );
    v___x_1666_ = lean_task_pure(v_inst_1663_);
    v___x_1667_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1667_, 0, v___x_1664_);
    lean_ctor_set(v___x_1667_, 1, v___x_1665_);
    lean_ctor_set(v___x_1667_, 2, v___x_1664_);
    lean_ctor_set(v___x_1667_, 3, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_Language_instInhabitedSnapshotTask_default(
    mut v_00_u03b1_1668_: *mut LeanObject,
    mut v_inst_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Lean_Language_instInhabitedSnapshotTask___redArg(
    mut v_inst_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    v___x_1672_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_1671_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_Language_instInhabitedSnapshotTask(
    mut v_a_1673_: *mut LeanObject,
    mut v_inst_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v___x_1675_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v_inst_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ofIO___redArg(
    mut v_stx_x3f_1676_: *mut LeanObject,
    mut v_cancelTk_x3f_1677_: *mut LeanObject,
    mut v_reportingRange_1678_: *mut LeanObject,
    mut v_act_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1681_ = lean_unsigned_to_nat(0);
    v___x_1682_ = lean_io_as_task(v_act_1679_, v___x_1681_);
    v___x_1683_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1683_, 0, v_stx_x3f_1676_);
    lean_ctor_set(v___x_1683_, 1, v_reportingRange_1678_);
    lean_ctor_set(v___x_1683_, 2, v_cancelTk_x3f_1677_);
    lean_ctor_set(v___x_1683_, 3, v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ofIO___redArg___boxed(
    mut v_stx_x3f_1684_: *mut LeanObject,
    mut v_cancelTk_x3f_1685_: *mut LeanObject,
    mut v_reportingRange_1686_: *mut LeanObject,
    mut v_act_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1689_: *mut LeanObject = core::ptr::null_mut();
    v_res_1689_ = l_Lean_Language_SnapshotTask_ofIO___redArg(
        v_stx_x3f_1684_,
        v_cancelTk_x3f_1685_,
        v_reportingRange_1686_,
        v_act_1687_,
    );
    return v_res_1689_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ofIO(
    mut v_00_u03b1_1690_: *mut LeanObject,
    mut v_stx_x3f_1691_: *mut LeanObject,
    mut v_cancelTk_x3f_1692_: *mut LeanObject,
    mut v_reportingRange_1693_: *mut LeanObject,
    mut v_act_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v___x_1696_ = l_Lean_Language_SnapshotTask_ofIO___redArg(
        v_stx_x3f_1691_,
        v_cancelTk_x3f_1692_,
        v_reportingRange_1693_,
        v_act_1694_,
    );
    return v___x_1696_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_ofIO___boxed(
    mut v_00_u03b1_1697_: *mut LeanObject,
    mut v_stx_x3f_1698_: *mut LeanObject,
    mut v_cancelTk_x3f_1699_: *mut LeanObject,
    mut v_reportingRange_1700_: *mut LeanObject,
    mut v_act_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_Language_SnapshotTask_ofIO(
        v_00_u03b1_1697_,
        v_stx_x3f_1698_,
        v_cancelTk_x3f_1699_,
        v_reportingRange_1700_,
        v_act_1701_,
    );
    return v_res_1703_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_finished___redArg(
    mut v_stx_x3f_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_box(2);
    v___x_1707_ = lean_box(0);
    v___x_1708_ = lean_task_pure(v_a_1705_);
    v___x_1709_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1709_, 0, v_stx_x3f_1704_);
    lean_ctor_set(v___x_1709_, 1, v___x_1706_);
    lean_ctor_set(v___x_1709_, 2, v___x_1707_);
    lean_ctor_set(v___x_1709_, 3, v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_finished(
    mut v_00_u03b1_1710_: *mut LeanObject,
    mut v_stx_x3f_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lean_Language_SnapshotTask_finished___redArg(v_stx_x3f_1711_, v_a_1712_);
    return v___x_1713_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_map___redArg(
    mut v_t_1714_: *mut LeanObject,
    mut v_f_1715_: *mut LeanObject,
    mut v_stx_x3f_1716_: *mut LeanObject,
    mut v_reportingRange_1717_: *mut LeanObject,
    mut v_sync_1718_: u8,
) -> *mut LeanObject {
    let mut v_cancelTk_x3f_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_1719_ = lean_ctor_get(v_t_1714_, 2);
                v_task_1720_ = lean_ctor_get(v_t_1714_, 3);
                v_isSharedCheck_1729_ = (!lean_is_exclusive(v_t_1714_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v_unused_1730_ = lean_ctor_get(v_t_1714_, 1);
                    lean_dec(v_unused_1730_);
                    v_unused_1731_ = lean_ctor_get(v_t_1714_, 0);
                    lean_dec(v_unused_1731_);
                    v___x_1722_ = v_t_1714_;
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_task_1720_);
                    lean_inc(v_cancelTk_x3f_1719_);
                    lean_dec(v_t_1714_);
                    v___x_1722_ = lean_box(0);
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1724_ = lean_unsigned_to_nat(0);
                v___x_1725_ = lean_task_map(v_f_1715_, v_task_1720_, v___x_1724_, v_sync_1718_);
                if v_isShared_1723_ == 0 {
                    lean_ctor_set(v___x_1722_, 3, v___x_1725_);
                    lean_ctor_set(v___x_1722_, 1, v_reportingRange_1717_);
                    lean_ctor_set(v___x_1722_, 0, v_stx_x3f_1716_);
                    v___x_1727_ = v___x_1722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_stx_x3f_1716_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_reportingRange_1717_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_cancelTk_x3f_1719_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 3, v___x_1725_);
                    v___x_1727_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_map___redArg___boxed(
    mut v_t_1732_: *mut LeanObject,
    mut v_f_1733_: *mut LeanObject,
    mut v_stx_x3f_1734_: *mut LeanObject,
    mut v_reportingRange_1735_: *mut LeanObject,
    mut v_sync_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_1737_: u8 = 0;
    let mut v_res_1738_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_1737_ = (lean_unbox(v_sync_1736_) as u8);
    v_res_1738_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_t_1732_,
        v_f_1733_,
        v_stx_x3f_1734_,
        v_reportingRange_1735_,
        v_sync_boxed_1737_,
    );
    return v_res_1738_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_map(
    mut v_00_u03b1_1739_: *mut LeanObject,
    mut v_00_u03b2_1740_: *mut LeanObject,
    mut v_t_1741_: *mut LeanObject,
    mut v_f_1742_: *mut LeanObject,
    mut v_stx_x3f_1743_: *mut LeanObject,
    mut v_reportingRange_1744_: *mut LeanObject,
    mut v_sync_1745_: u8,
) -> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_t_1741_,
        v_f_1742_,
        v_stx_x3f_1743_,
        v_reportingRange_1744_,
        v_sync_1745_,
    );
    return v___x_1746_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_map___boxed(
    mut v_00_u03b1_1747_: *mut LeanObject,
    mut v_00_u03b2_1748_: *mut LeanObject,
    mut v_t_1749_: *mut LeanObject,
    mut v_f_1750_: *mut LeanObject,
    mut v_stx_x3f_1751_: *mut LeanObject,
    mut v_reportingRange_1752_: *mut LeanObject,
    mut v_sync_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_1754_: u8 = 0;
    let mut v_res_1755_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_1754_ = (lean_unbox(v_sync_1753_) as u8);
    v_res_1755_ = l_Lean_Language_SnapshotTask_map(
        v_00_u03b1_1747_,
        v_00_u03b2_1748_,
        v_t_1749_,
        v_f_1750_,
        v_stx_x3f_1751_,
        v_reportingRange_1752_,
        v_sync_boxed_1754_,
    );
    return v_res_1755_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(
    mut v_act_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = lean_apply_2(v_act_1756_, v_a_1757_, lean_box(0));
    v_task_1760_ = lean_ctor_get(v___x_1759_, 3);
    lean_inc_ref(v_task_1760_);
    lean_dec_ref(v___x_1759_);
    return v_task_1760_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed(
    mut v_act_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1764_: *mut LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(v_act_1761_, v_a_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO___redArg(
    mut v_t_1765_: *mut LeanObject,
    mut v_act_1766_: *mut LeanObject,
    mut v_stx_x3f_1767_: *mut LeanObject,
    mut v_reportingRange_1768_: *mut LeanObject,
    mut v_cancelTk_x3f_1769_: *mut LeanObject,
    mut v_sync_1770_: u8,
) -> *mut LeanObject {
    let mut v_task_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___f_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v_unused_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1772_ = lean_ctor_get(v_t_1765_, 3);
                v_isSharedCheck_1782_ = (!lean_is_exclusive(v_t_1765_)) as u8;
                if v_isSharedCheck_1782_ == 0 {
                    v_unused_1783_ = lean_ctor_get(v_t_1765_, 2);
                    lean_dec(v_unused_1783_);
                    v_unused_1784_ = lean_ctor_get(v_t_1765_, 1);
                    lean_dec(v_unused_1784_);
                    v_unused_1785_ = lean_ctor_get(v_t_1765_, 0);
                    lean_dec(v_unused_1785_);
                    v___x_1774_ = v_t_1765_;
                    v_isShared_1775_ = v_isSharedCheck_1782_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_task_1772_);
                    lean_dec(v_t_1765_);
                    v___x_1774_ = lean_box(0);
                    v_isShared_1775_ = v_isSharedCheck_1782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1776_ = lean_alloc_closure(
                    l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_1776_, 0, v_act_1766_);
                v___x_1777_ = lean_unsigned_to_nat(0);
                v___x_1778_ =
                    lean_io_bind_task(v_task_1772_, v___f_1776_, v___x_1777_, v_sync_1770_);
                if v_isShared_1775_ == 0 {
                    lean_ctor_set(v___x_1774_, 3, v___x_1778_);
                    lean_ctor_set(v___x_1774_, 2, v_cancelTk_x3f_1769_);
                    lean_ctor_set(v___x_1774_, 1, v_reportingRange_1768_);
                    lean_ctor_set(v___x_1774_, 0, v_stx_x3f_1767_);
                    v___x_1780_ = v___x_1774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_stx_x3f_1767_);
                    lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_reportingRange_1768_);
                    lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_cancelTk_x3f_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1781_, 3, v___x_1778_);
                    v___x_1780_ = v_reuseFailAlloc_1781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(
    mut v_t_1786_: *mut LeanObject,
    mut v_act_1787_: *mut LeanObject,
    mut v_stx_x3f_1788_: *mut LeanObject,
    mut v_reportingRange_1789_: *mut LeanObject,
    mut v_cancelTk_x3f_1790_: *mut LeanObject,
    mut v_sync_1791_: *mut LeanObject,
    mut v_a_1792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_1793_: u8 = 0;
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_1793_ = (lean_unbox(v_sync_1791_) as u8);
    v_res_1794_ = l_Lean_Language_SnapshotTask_bindIO___redArg(
        v_t_1786_,
        v_act_1787_,
        v_stx_x3f_1788_,
        v_reportingRange_1789_,
        v_cancelTk_x3f_1790_,
        v_sync_boxed_1793_,
    );
    return v_res_1794_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO(
    mut v_00_u03b1_1795_: *mut LeanObject,
    mut v_00_u03b2_1796_: *mut LeanObject,
    mut v_t_1797_: *mut LeanObject,
    mut v_act_1798_: *mut LeanObject,
    mut v_stx_x3f_1799_: *mut LeanObject,
    mut v_reportingRange_1800_: *mut LeanObject,
    mut v_cancelTk_x3f_1801_: *mut LeanObject,
    mut v_sync_1802_: u8,
) -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    v___x_1804_ = l_Lean_Language_SnapshotTask_bindIO___redArg(
        v_t_1797_,
        v_act_1798_,
        v_stx_x3f_1799_,
        v_reportingRange_1800_,
        v_cancelTk_x3f_1801_,
        v_sync_1802_,
    );
    return v___x_1804_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_bindIO___boxed(
    mut v_00_u03b1_1805_: *mut LeanObject,
    mut v_00_u03b2_1806_: *mut LeanObject,
    mut v_t_1807_: *mut LeanObject,
    mut v_act_1808_: *mut LeanObject,
    mut v_stx_x3f_1809_: *mut LeanObject,
    mut v_reportingRange_1810_: *mut LeanObject,
    mut v_cancelTk_x3f_1811_: *mut LeanObject,
    mut v_sync_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_1814_: u8 = 0;
    let mut v_res_1815_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_1814_ = (lean_unbox(v_sync_1812_) as u8);
    v_res_1815_ = l_Lean_Language_SnapshotTask_bindIO(
        v_00_u03b1_1805_,
        v_00_u03b2_1806_,
        v_t_1807_,
        v_act_1808_,
        v_stx_x3f_1809_,
        v_reportingRange_1810_,
        v_cancelTk_x3f_1811_,
        v_sync_boxed_1814_,
    );
    return v_res_1815_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_get___redArg(
    mut v_t_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_task_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v_task_1817_ = lean_ctor_get(v_t_1816_, 3);
    lean_inc_ref(v_task_1817_);
    lean_dec_ref(v_t_1816_);
    v___x_1818_ = lean_task_get_own(v_task_1817_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_get(
    mut v_00_u03b1_1819_: *mut LeanObject,
    mut v_t_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_Language_SnapshotTask_get___redArg(v_t_1820_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_get_x3f___redArg(
    mut v_t_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_task_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    v_task_1824_ = lean_ctor_get(v_t_1822_, 3);
    lean_inc_ref(v_task_1824_);
    lean_dec_ref(v_t_1822_);
    v___x_1825_ = lean_io_get_task_state(v_task_1824_);
    if v___x_1825_ == 2 {
        let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
        v___x_1826_ = lean_task_get_own(v_task_1824_);
        v___x_1827_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1827_, 0, v___x_1826_);
        return v___x_1827_;
    } else {
        let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_task_1824_);
        v___x_1828_ = lean_box(0);
        return v___x_1828_;
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_get_x3f___redArg___boxed(
    mut v_t_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1831_: *mut LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_1829_);
    return v_res_1831_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_get_x3f(
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_t_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_t_1833_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_get_x3f___boxed(
    mut v_00_u03b1_1836_: *mut LeanObject,
    mut v_t_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_Language_SnapshotTask_get_x3f(v_00_u03b1_1836_, v_t_1837_);
    return v_res_1839_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1()
-> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lean_Language_instInhabitedSnapshotTree_default___closed__0;
    v___x_1843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__4,
    );
    v___x_1844_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1844_, 0, v___x_1843_);
    lean_ctor_set(v___x_1844_, 1, v___x_1842_);
    return v___x_1844_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshotTree_default() -> *mut LeanObject {
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    v___x_1845_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshotTree_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshotTree_default___closed__1_once),
        _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1,
    );
    return v___x_1845_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshotTree() -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Lean_Language_instInhabitedSnapshotTree_default;
    return v___x_1846_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(
    mut v_s_1855_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_1855_);
    return v_s_1855_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(
    mut v_s_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(v_s_1856_);
    lean_dec_ref(v_s_1856_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(
    mut v_inst_1860_: *mut LeanObject,
    mut v_x_1861_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1861_) == 0 {
        let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1860_);
        v___x_1862_ = l_Lean_Language_instInhabitedSnapshotTree_default;
        return v___x_1862_;
    } else {
        let mut v_val_1863_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
        v_val_1863_ = lean_ctor_get(v_x_1861_, 0);
        lean_inc(v_val_1863_);
        lean_dec_ref_known(v_x_1861_, 1);
        v___x_1864_ = lean_apply_1(v_inst_1860_, v_val_1863_);
        return v___x_1864_;
    }
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeOption___redArg(
    mut v_inst_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1866_: *mut LeanObject = core::ptr::null_mut();
    v___f_1866_ = lean_alloc_closure(
        l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1866_, 0, v_inst_1865_);
    return v___f_1866_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeOption(
    mut v_00_u03b1_1867_: *mut LeanObject,
    mut v_inst_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1869_: *mut LeanObject = core::ptr::null_mut();
    v___f_1869_ = lean_alloc_closure(
        l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1869_, 0, v_inst_1868_);
    return v___f_1869_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(
    mut v_inst_1870_: *mut LeanObject,
    mut v___x_1871_: *mut LeanObject,
    mut v___f_1872_: *mut LeanObject,
    mut v_snap_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    v___x_1875_ = lean_apply_1(v_inst_1870_, v_snap_1873_);
    v_children_1876_ = lean_ctor_get(v___x_1875_, 1);
    lean_inc_ref(v_children_1876_);
    lean_dec_ref(v___x_1875_);
    v___x_1877_ = lean_unsigned_to_nat(0);
    v___x_1878_ = lean_array_get_size(v_children_1876_);
    v___x_1879_ = lean_box(0);
    v___x_1880_ = lean_nat_dec_lt(v___x_1877_, v___x_1878_);
    if v___x_1880_ == 0 {
        lean_dec_ref(v_children_1876_);
        lean_dec_ref(v___f_1872_);
        lean_dec_ref(v___x_1871_);
        return v___x_1879_;
    } else {
        let mut v___x_1881_: u8 = 0;
        v___x_1881_ = lean_nat_dec_le(v___x_1878_, v___x_1878_);
        if v___x_1881_ == 0 {
            if v___x_1880_ == 0 {
                lean_dec_ref(v_children_1876_);
                lean_dec_ref(v___f_1872_);
                lean_dec_ref(v___x_1871_);
                return v___x_1879_;
            } else {
                let mut v___x_1882_: usize = 0;
                let mut v___x_1883_: usize = 0;
                let mut v___x_219__overap_1884_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
                v___x_1882_ = 0usize;
                v___x_1883_ = lean_usize_of_nat(v___x_1878_);
                v___x_219__overap_1884_ =
                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1871_,
                        v___f_1872_,
                        v_children_1876_,
                        v___x_1882_,
                        v___x_1883_,
                        v___x_1879_,
                    );
                v___x_1885_ = lean_apply_1(v___x_219__overap_1884_, lean_box(0));
                return v___x_1885_;
            }
        } else {
            let mut v___x_1886_: usize = 0;
            let mut v___x_1887_: usize = 0;
            let mut v___x_222__overap_1888_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
            v___x_1886_ = 0usize;
            v___x_1887_ = lean_usize_of_nat(v___x_1878_);
            v___x_222__overap_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_1871_,
                v___f_1872_,
                v_children_1876_,
                v___x_1886_,
                v___x_1887_,
                v___x_1879_,
            );
            v___x_1889_ = lean_apply_1(v___x_222__overap_1888_, lean_box(0));
            return v___x_1889_;
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed(
    mut v_inst_1890_: *mut LeanObject,
    mut v___x_1891_: *mut LeanObject,
    mut v___f_1892_: *mut LeanObject,
    mut v_snap_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1895_: *mut LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(
        v_inst_1890_,
        v___x_1891_,
        v___f_1892_,
        v_snap_1893_,
    );
    return v_res_1895_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(
    mut v___f_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1900_: *mut LeanObject = core::ptr::null_mut();
    v_res_1900_ = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(
        v___f_1896_,
        v_x_1897_,
        v___y_1898_,
    );
    return v_res_1900_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg(
    mut v_inst_1901_: *mut LeanObject,
    mut v_t_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1904_ = l_instMonadBaseIO;
                v_cancelTk_x3f_1905_ = lean_ctor_get(v_t_1902_, 2);
                lean_inc(v_cancelTk_x3f_1905_);
                v_task_1906_ = lean_ctor_get(v_t_1902_, 3);
                lean_inc_ref(v_task_1906_);
                lean_dec_ref(v_t_1902_);
                v___f_1907_ = l_Lean_Language_instToSnapshotTreeSnapshotTree___closed__0;
                v___f_1908_ = lean_alloc_closure(
                    l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_1908_, 0, v___f_1907_);
                v___f_1909_ = lean_alloc_closure(
                    l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_1909_, 0, v_inst_1901_);
                lean_closure_set(v___f_1909_, 1, v___x_1904_);
                lean_closure_set(v___f_1909_, 2, v___f_1908_);
                if lean_obj_tag(v_cancelTk_x3f_1905_) == 1 {
                    v_val_1914_ = lean_ctor_get(v_cancelTk_x3f_1905_, 0);
                    lean_inc(v_val_1914_);
                    lean_dec_ref_known(v_cancelTk_x3f_1905_, 1);
                    v___x_1915_ = l_IO_CancelToken_set(v_val_1914_);
                    lean_dec(v_val_1914_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cancelTk_x3f_1905_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1911_ = lean_unsigned_to_nat(0);
                v___x_1912_ = 1;
                v___x_1913_ = l_BaseIO_chainTask___redArg(
                    v_task_1906_,
                    v___f_1909_,
                    v___x_1911_,
                    v___x_1912_,
                );
                return v___x_1913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(
    mut v___f_1916_: *mut LeanObject,
    mut v_x_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1916_, v___y_1918_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___redArg___boxed(
    mut v_inst_1921_: *mut LeanObject,
    mut v_t_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1924_: *mut LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_1921_, v_t_1922_);
    return v_res_1924_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec(
    mut v_00_u03b1_1925_: *mut LeanObject,
    mut v_inst_1926_: *mut LeanObject,
    mut v_t_1927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v_inst_1926_, v_t_1927_);
    return v___x_1929_;
}
pub unsafe fn l_Lean_Language_SnapshotTask_cancelRec___boxed(
    mut v_00_u03b1_1930_: *mut LeanObject,
    mut v_inst_1931_: *mut LeanObject,
    mut v_t_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean_Language_SnapshotTask_cancelRec(v_00_u03b1_1930_, v_inst_1931_, v_t_1932_);
    return v_res_1934_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedSnapshotLeaf() -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = lean_unsigned_to_nat(32);
    v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
    lean_dec_ref(v___x_1943_);
    v___x_1944_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__4_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__4,
    );
    return v___x_1944_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(
    mut v_s_1947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0;
    v___x_1949_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1949_, 0, v_s_1947_);
    lean_ctor_set(v___x_1949_, 1, v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(
    mut v_s_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tree_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    v_tree_1953_ = lean_ctor_get(v_s_1952_, 1);
    v___x_1954_ = lean_thunk_get_own(v_tree_1953_);
    return v___x_1954_;
}
pub unsafe fn l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(
    mut v_s_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1956_: *mut LeanObject = core::ptr::null_mut();
    v_res_1956_ = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(v_s_1955_);
    lean_dec_ref(v_s_1955_);
    return v_res_1956_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(
    mut v_inst_1959_: *mut LeanObject,
    mut v_val_1960_: *mut LeanObject,
    mut v_x_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v___x_1962_ = lean_apply_1(v_inst_1959_, v_val_1960_);
    return v___x_1962_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_ofTyped___redArg(
    mut v_inst_1963_: *mut LeanObject,
    mut v_inst_1964_: *mut LeanObject,
    mut v_val_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_val_1965_);
    v___f_1966_ = lean_alloc_closure(
        l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1966_, 0, v_inst_1964_);
    lean_closure_set(v___f_1966_, 1, v_val_1965_);
    v___x_1967_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1967_, 0, v_inst_1963_);
    lean_ctor_set(v___x_1967_, 1, v_val_1965_);
    v___x_1968_ = lean_mk_thunk(v___f_1966_);
    v___x_1969_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1969_, 0, v___x_1967_);
    lean_ctor_set(v___x_1969_, 1, v___x_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_ofTyped(
    mut v_00_u03b1_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
    mut v_val_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    v___x_1974_ =
        l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v_inst_1971_, v_inst_1972_, v_val_1973_);
    return v___x_1974_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(
    mut v_inst_1975_: *mut LeanObject,
    mut v_snap_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v_val_1977_ = lean_ctor_get(v_snap_1976_, 0);
    v___x_1978_ =
        l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_1977_, v_inst_1975_);
    return v___x_1978_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(
    mut v_inst_1979_: *mut LeanObject,
    mut v_snap_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1981_: *mut LeanObject = core::ptr::null_mut();
    v_res_1981_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_1979_, v_snap_1980_);
    lean_dec_ref(v_snap_1980_);
    lean_dec(v_inst_1979_);
    return v_res_1981_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_toTyped_x3f(
    mut v_00_u03b1_1982_: *mut LeanObject,
    mut v_inst_1983_: *mut LeanObject,
    mut v_snap_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_1985_ = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(v_inst_1983_, v_snap_1984_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(
    mut v_00_u03b1_1986_: *mut LeanObject,
    mut v_inst_1987_: *mut LeanObject,
    mut v_snap_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_res_1989_ =
        l_Lean_Language_DynamicSnapshot_toTyped_x3f(v_00_u03b1_1986_, v_inst_1987_, v_snap_1988_);
    lean_dec_ref(v_snap_1988_);
    lean_dec(v_inst_1987_);
    return v_res_1989_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2() -> *mut LeanObject {
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = 1;
    v___x_1996_ = l_Lean_Language_instInhabitedDynamicSnapshot___closed__1;
    v___x_1997_ = l_Lean_Name_toString(v___x_1996_, v___x_1995_);
    return v___x_1997_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3() -> *mut LeanObject {
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1998_ = 0;
    v___x_1999_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3_once),
        _init_l_Lean_Language_instInhabitedSnapshot___closed__3,
    );
    v___x_2000_ = lean_box(0);
    v___x_2001_ = l_Lean_Language_Snapshot_Diagnostics_empty;
    v___x_2002_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__2_once),
        _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2,
    );
    v___x_2003_ = lean_alloc_ctor(0, 4, (1) as u32);
    lean_ctor_set(v___x_2003_, 0, v___x_2002_);
    lean_ctor_set(v___x_2003_, 1, v___x_2001_);
    lean_ctor_set(v___x_2003_, 2, v___x_2000_);
    lean_ctor_set(v___x_2003_, 3, v___x_1999_);
    lean_ctor_set_uint8(
        v___x_2003_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_1998_,
    );
    return v___x_2003_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4() -> *mut LeanObject {
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    v___x_2004_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__3_once),
        _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3,
    );
    v___f_2005_ = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__0;
    v___x_2006_ =
        l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
    v___x_2007_ =
        l_Lean_Language_DynamicSnapshot_ofTyped___redArg(v___x_2006_, v___f_2005_, v___x_2004_);
    return v___x_2007_;
}
pub unsafe fn _init_l_Lean_Language_instInhabitedDynamicSnapshot() -> *mut LeanObject {
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    v___x_2008_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedDynamicSnapshot___closed__4_once),
        _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4,
    );
    return v___x_2008_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_forM___redArg___lam__1(
    mut v_children_2009_: *mut LeanObject,
    mut v_toApplicative_2010_: *mut LeanObject,
    mut v_inst_2011_: *mut LeanObject,
    mut v___f_2012_: *mut LeanObject,
    mut v_____r_2013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u8 = 0;
    v___x_2014_ = lean_unsigned_to_nat(0);
    v___x_2015_ = lean_array_get_size(v_children_2009_);
    v___x_2016_ = lean_box(0);
    v___x_2017_ = lean_nat_dec_lt(v___x_2014_, v___x_2015_);
    if v___x_2017_ == 0 {
        let mut v_toPure_2018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2012_);
        lean_dec_ref(v_inst_2011_);
        lean_dec_ref(v_children_2009_);
        v_toPure_2018_ = lean_ctor_get(v_toApplicative_2010_, 1);
        lean_inc(v_toPure_2018_);
        lean_dec_ref(v_toApplicative_2010_);
        v___x_2019_ = lean_apply_2(v_toPure_2018_, lean_box(0), v___x_2016_);
        return v___x_2019_;
    } else {
        let mut v___x_2020_: u8 = 0;
        v___x_2020_ = lean_nat_dec_le(v___x_2015_, v___x_2015_);
        if v___x_2020_ == 0 {
            if v___x_2017_ == 0 {
                let mut v_toPure_2021_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_2012_);
                lean_dec_ref(v_inst_2011_);
                lean_dec_ref(v_children_2009_);
                v_toPure_2021_ = lean_ctor_get(v_toApplicative_2010_, 1);
                lean_inc(v_toPure_2021_);
                lean_dec_ref(v_toApplicative_2010_);
                v___x_2022_ = lean_apply_2(v_toPure_2021_, lean_box(0), v___x_2016_);
                return v___x_2022_;
            } else {
                let mut v___x_2023_: usize = 0;
                let mut v___x_2024_: usize = 0;
                let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_2010_);
                v___x_2023_ = 0usize;
                v___x_2024_ = lean_usize_of_nat(v___x_2015_);
                v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2011_,
                    v___f_2012_,
                    v_children_2009_,
                    v___x_2023_,
                    v___x_2024_,
                    v___x_2016_,
                );
                return v___x_2025_;
            }
        } else {
            let mut v___x_2026_: usize = 0;
            let mut v___x_2027_: usize = 0;
            let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_2010_);
            v___x_2026_ = 0usize;
            v___x_2027_ = lean_usize_of_nat(v___x_2015_);
            v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2011_,
                v___f_2012_,
                v_children_2009_,
                v___x_2026_,
                v___x_2027_,
                v___x_2016_,
            );
            return v___x_2028_;
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_forM___redArg(
    mut v_inst_2029_: *mut LeanObject,
    mut v_s_2030_: *mut LeanObject,
    mut v_f_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_element_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2032_ = lean_ctor_get(v_inst_2029_, 0);
    lean_inc_ref(v_toApplicative_2032_);
    v_toBind_2033_ = lean_ctor_get(v_inst_2029_, 1);
    lean_inc(v_toBind_2033_);
    v_element_2034_ = lean_ctor_get(v_s_2030_, 0);
    lean_inc_ref(v_element_2034_);
    v_children_2035_ = lean_ctor_get(v_s_2030_, 1);
    lean_inc_ref(v_children_2035_);
    lean_dec_ref(v_s_2030_);
    lean_inc(v_f_2031_);
    lean_inc_ref(v_inst_2029_);
    v___f_2036_ = lean_alloc_closure(
        l_Lean_Language_SnapshotTree_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2036_, 0, v_inst_2029_);
    lean_closure_set(v___f_2036_, 1, v_f_2031_);
    v___f_2037_ = lean_alloc_closure(
        l_Lean_Language_SnapshotTree_forM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2037_, 0, v_children_2035_);
    lean_closure_set(v___f_2037_, 1, v_toApplicative_2032_);
    lean_closure_set(v___f_2037_, 2, v_inst_2029_);
    lean_closure_set(v___f_2037_, 3, v___f_2036_);
    v___x_2038_ = lean_apply_1(v_f_2031_, v_element_2034_);
    v___x_2039_ = lean_apply_4(
        v_toBind_2033_,
        lean_box(0),
        lean_box(0),
        v___x_2038_,
        v___f_2037_,
    );
    return v___x_2039_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_forM___redArg___lam__0(
    mut v_inst_2040_: *mut LeanObject,
    mut v_f_2041_: *mut LeanObject,
    mut v_x_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Lean_Language_SnapshotTask_get___redArg(v___y_2043_);
    v___x_2045_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_2040_, v___x_2044_, v_f_2041_);
    return v___x_2045_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_forM(
    mut v_m_2046_: *mut LeanObject,
    mut v_inst_2047_: *mut LeanObject,
    mut v_s_2048_: *mut LeanObject,
    mut v_f_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Lean_Language_SnapshotTree_forM___redArg(v_inst_2047_, v_s_2048_, v_f_2049_);
    return v___x_2050_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(
    mut v_children_2051_: *mut LeanObject,
    mut v_toApplicative_2052_: *mut LeanObject,
    mut v_inst_2053_: *mut LeanObject,
    mut v___f_2054_: *mut LeanObject,
    mut v_a_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    v___x_2056_ = lean_unsigned_to_nat(0);
    v___x_2057_ = lean_array_get_size(v_children_2051_);
    v___x_2058_ = lean_nat_dec_lt(v___x_2056_, v___x_2057_);
    if v___x_2058_ == 0 {
        let mut v_toPure_2059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2054_);
        lean_dec_ref(v_inst_2053_);
        lean_dec_ref(v_children_2051_);
        v_toPure_2059_ = lean_ctor_get(v_toApplicative_2052_, 1);
        lean_inc(v_toPure_2059_);
        lean_dec_ref(v_toApplicative_2052_);
        v___x_2060_ = lean_apply_2(v_toPure_2059_, lean_box(0), v_a_2055_);
        return v___x_2060_;
    } else {
        let mut v___x_2061_: u8 = 0;
        v___x_2061_ = lean_nat_dec_le(v___x_2057_, v___x_2057_);
        if v___x_2061_ == 0 {
            if v___x_2058_ == 0 {
                let mut v_toPure_2062_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_2054_);
                lean_dec_ref(v_inst_2053_);
                lean_dec_ref(v_children_2051_);
                v_toPure_2062_ = lean_ctor_get(v_toApplicative_2052_, 1);
                lean_inc(v_toPure_2062_);
                lean_dec_ref(v_toApplicative_2052_);
                v___x_2063_ = lean_apply_2(v_toPure_2062_, lean_box(0), v_a_2055_);
                return v___x_2063_;
            } else {
                let mut v___x_2064_: usize = 0;
                let mut v___x_2065_: usize = 0;
                let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_2052_);
                v___x_2064_ = 0usize;
                v___x_2065_ = lean_usize_of_nat(v___x_2057_);
                v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2053_,
                    v___f_2054_,
                    v_children_2051_,
                    v___x_2064_,
                    v___x_2065_,
                    v_a_2055_,
                );
                return v___x_2066_;
            }
        } else {
            let mut v___x_2067_: usize = 0;
            let mut v___x_2068_: usize = 0;
            let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_2052_);
            v___x_2067_ = 0usize;
            v___x_2068_ = lean_usize_of_nat(v___x_2057_);
            v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2053_,
                v___f_2054_,
                v_children_2051_,
                v___x_2067_,
                v___x_2068_,
                v_a_2055_,
            );
            return v___x_2069_;
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___redArg(
    mut v_inst_2070_: *mut LeanObject,
    mut v_s_2071_: *mut LeanObject,
    mut v_f_2072_: *mut LeanObject,
    mut v_init_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_element_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2074_ = lean_ctor_get(v_inst_2070_, 0);
    lean_inc_ref(v_toApplicative_2074_);
    v_toBind_2075_ = lean_ctor_get(v_inst_2070_, 1);
    lean_inc(v_toBind_2075_);
    v_element_2076_ = lean_ctor_get(v_s_2071_, 0);
    lean_inc_ref(v_element_2076_);
    v_children_2077_ = lean_ctor_get(v_s_2071_, 1);
    lean_inc_ref(v_children_2077_);
    lean_dec_ref(v_s_2071_);
    lean_inc(v_f_2072_);
    lean_inc_ref(v_inst_2070_);
    v___f_2078_ = lean_alloc_closure(
        l_Lean_Language_SnapshotTree_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2078_, 0, v_inst_2070_);
    lean_closure_set(v___f_2078_, 1, v_f_2072_);
    v___f_2079_ = lean_alloc_closure(
        l_Lean_Language_SnapshotTree_foldM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2079_, 0, v_children_2077_);
    lean_closure_set(v___f_2079_, 1, v_toApplicative_2074_);
    lean_closure_set(v___f_2079_, 2, v_inst_2070_);
    lean_closure_set(v___f_2079_, 3, v___f_2078_);
    v___x_2080_ = lean_apply_2(v_f_2072_, v_init_2073_, v_element_2076_);
    v___x_2081_ = lean_apply_4(
        v_toBind_2075_,
        lean_box(0),
        lean_box(0),
        v___x_2080_,
        v___f_2079_,
    );
    return v___x_2081_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(
    mut v_inst_2082_: *mut LeanObject,
    mut v_f_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_snap_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    v___x_2086_ = l_Lean_Language_SnapshotTask_get___redArg(v_snap_2085_);
    v___x_2087_ = l_Lean_Language_SnapshotTree_foldM___redArg(
        v_inst_2082_,
        v___x_2086_,
        v_f_2083_,
        v_a_2084_,
    );
    return v___x_2087_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM(
    mut v_m_2088_: *mut LeanObject,
    mut v_00_u03b1_2089_: *mut LeanObject,
    mut v_inst_2090_: *mut LeanObject,
    mut v_s_2091_: *mut LeanObject,
    mut v_f_2092_: *mut LeanObject,
    mut v_init_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Lean_Language_SnapshotTree_foldM___redArg(
        v_inst_2090_,
        v_s_2091_,
        v_f_2092_,
        v_init_2093_,
    );
    return v___x_2094_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(
    mut v_name_2095_: *mut LeanObject,
    mut v_decl_2096_: *mut LeanObject,
    mut v_ref_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2108_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut v_unused_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2118_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2099_ = lean_ctor_get(v_decl_2096_, 0);
                v_descr_2100_ = lean_ctor_get(v_decl_2096_, 1);
                v_deprecation_x3f_2101_ = lean_ctor_get(v_decl_2096_, 2);
                v___x_2102_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2103_ = (lean_unbox(v_defValue_2099_) as u8);
                lean_ctor_set_uint8(v___x_2102_, 0 as u32, v___x_2103_);
                lean_inc(v_deprecation_x3f_2101_);
                lean_inc_ref(v_descr_2100_);
                lean_inc_n(v_name_2095_, 2);
                v___x_2104_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v_name_2095_);
                lean_ctor_set(v___x_2104_, 1, v_ref_2097_);
                lean_ctor_set(v___x_2104_, 2, v___x_2102_);
                lean_ctor_set(v___x_2104_, 3, v_descr_2100_);
                lean_ctor_set(v___x_2104_, 4, v_deprecation_x3f_2101_);
                v___x_2105_ = lean_register_option(v_name_2095_, v___x_2104_);
                if lean_obj_tag(v___x_2105_) == 0 {
                    v_isSharedCheck_2113_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2113_ == 0 {
                        v_unused_2114_ = lean_ctor_get(v___x_2105_, 0);
                        lean_dec(v_unused_2114_);
                        v___x_2107_ = v___x_2105_;
                        v_isShared_2108_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2105_);
                        v___x_2107_ = lean_box(0);
                        v_isShared_2108_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_2095_);
                    v_a_2115_ = lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2122_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2122_ == 0 {
                        v___x_2117_ = v___x_2105_;
                        v_isShared_2118_ = v_isSharedCheck_2122_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2115_);
                        lean_dec(v___x_2105_);
                        v___x_2117_ = lean_box(0);
                        v_isShared_2118_ = v_isSharedCheck_2122_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_2099_);
                v___x_2109_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2109_, 0, v_name_2095_);
                lean_ctor_set(v___x_2109_, 1, v_defValue_2099_);
                if v_isShared_2108_ == 0 {
                    lean_ctor_set(v___x_2107_, 0, v___x_2109_);
                    v___x_2111_ = v___x_2107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2111_;
            }
            3 => {
                if v_isShared_2118_ == 0 {
                    v___x_2120_ = v___x_2117_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
                    v___x_2120_ = v_reuseFailAlloc_2121_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2123_: *mut LeanObject,
    mut v_decl_2124_: *mut LeanObject,
    mut v_ref_2125_: *mut LeanObject,
    mut v_a_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2127_: *mut LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v_name_2123_, v_decl_2124_, v_ref_2125_);
    lean_dec_ref(v_decl_2124_);
    return v_res_2127_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___x_2142_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
    v___x_2143_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
    v___x_2144_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
    v___x_2145_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(v___x_2142_, v___x_2143_, v___x_2144_);
    return v___x_2145_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4____boxed(
    mut v_a_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_res_2147_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
    return v_res_2147_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(
    mut v_name_2148_: *mut LeanObject,
    mut v_decl_2149_: *mut LeanObject,
    mut v_ref_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2160_: u8 = 0;
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v_unused_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2152_ = lean_ctor_get(v_decl_2149_, 0);
                v_descr_2153_ = lean_ctor_get(v_decl_2149_, 1);
                v_deprecation_x3f_2154_ = lean_ctor_get(v_decl_2149_, 2);
                lean_inc(v_defValue_2152_);
                v___x_2155_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2155_, 0, v_defValue_2152_);
                lean_inc(v_deprecation_x3f_2154_);
                lean_inc_ref(v_descr_2153_);
                lean_inc_n(v_name_2148_, 2);
                v___x_2156_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2156_, 0, v_name_2148_);
                lean_ctor_set(v___x_2156_, 1, v_ref_2150_);
                lean_ctor_set(v___x_2156_, 2, v___x_2155_);
                lean_ctor_set(v___x_2156_, 3, v_descr_2153_);
                lean_ctor_set(v___x_2156_, 4, v_deprecation_x3f_2154_);
                v___x_2157_ = lean_register_option(v_name_2148_, v___x_2156_);
                if lean_obj_tag(v___x_2157_) == 0 {
                    v_isSharedCheck_2165_ = (!lean_is_exclusive(v___x_2157_)) as u8;
                    if v_isSharedCheck_2165_ == 0 {
                        v_unused_2166_ = lean_ctor_get(v___x_2157_, 0);
                        lean_dec(v_unused_2166_);
                        v___x_2159_ = v___x_2157_;
                        v_isShared_2160_ = v_isSharedCheck_2165_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2157_);
                        v___x_2159_ = lean_box(0);
                        v_isShared_2160_ = v_isSharedCheck_2165_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_2148_);
                    v_a_2167_ = lean_ctor_get(v___x_2157_, 0);
                    v_isSharedCheck_2174_ = (!lean_is_exclusive(v___x_2157_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v___x_2169_ = v___x_2157_;
                        v_isShared_2170_ = v_isSharedCheck_2174_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2167_);
                        lean_dec(v___x_2157_);
                        v___x_2169_ = lean_box(0);
                        v_isShared_2170_ = v_isSharedCheck_2174_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_2152_);
                v___x_2161_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2161_, 0, v_name_2148_);
                lean_ctor_set(v___x_2161_, 1, v_defValue_2152_);
                if v_isShared_2160_ == 0 {
                    lean_ctor_set(v___x_2159_, 0, v___x_2161_);
                    v___x_2163_ = v___x_2159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
                    v___x_2163_ = v_reuseFailAlloc_2164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2163_;
            }
            3 => {
                if v_isShared_2170_ == 0 {
                    v___x_2172_ = v___x_2169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
                    v___x_2172_ = v_reuseFailAlloc_2173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2175_: *mut LeanObject,
    mut v_decl_2176_: *mut LeanObject,
    mut v_ref_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2179_: *mut LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v_name_2175_, v_decl_2176_, v_ref_2177_);
    lean_dec_ref(v_decl_2176_);
    return v_res_2179_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__1_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
    v___x_2194_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__3_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
    v___x_2195_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn___closed__4_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
    v___x_2196_ = l_Lean_Option_register___at___00__private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(v___x_2193_, v___x_2194_, v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4____boxed(
    mut v_a_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2198_: *mut LeanObject = core::ptr::null_mut();
    v_res_2198_ = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
    return v_res_2198_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(
    mut v_opts_2199_: *mut LeanObject,
    mut v_opt_2200_: *mut LeanObject,
) -> u8 {
    let mut v_name_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    v_name_2201_ = lean_ctor_get(v_opt_2200_, 0);
    v_defValue_2202_ = lean_ctor_get(v_opt_2200_, 1);
    v_map_2203_ = lean_ctor_get(v_opts_2199_, 0);
    v___x_2204_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2203_,
            v_name_2201_,
        );
    if lean_obj_tag(v___x_2204_) == 0 {
        let mut v___x_2205_: u8 = 0;
        v___x_2205_ = (lean_unbox(v_defValue_2202_) as u8);
        return v___x_2205_;
    } else {
        let mut v_val_2206_: *mut LeanObject = core::ptr::null_mut();
        v_val_2206_ = lean_ctor_get(v___x_2204_, 0);
        lean_inc(v_val_2206_);
        lean_dec_ref_known(v___x_2204_, 1);
        if lean_obj_tag(v_val_2206_) == 1 {
            let mut v_v_2207_: u8 = 0;
            v_v_2207_ = lean_ctor_get_uint8(v_val_2206_, 0 as u32);
            lean_dec_ref_known(v_val_2206_, 0);
            return v_v_2207_;
        } else {
            let mut v___x_2208_: u8 = 0;
            lean_dec(v_val_2206_);
            v___x_2208_ = (lean_unbox(v_defValue_2202_) as u8);
            return v___x_2208_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(
    mut v_opts_2209_: *mut LeanObject,
    mut v_opt_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2211_: u8 = 0;
    let mut v_r_2212_: *mut LeanObject = core::ptr::null_mut();
    v_res_2211_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_2209_, v_opt_2210_);
    lean_dec_ref(v_opt_2210_);
    lean_dec_ref(v_opts_2209_);
    v_r_2212_ = lean_box((v_res_2211_) as usize);
    return v_r_2212_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(
    mut v_opts_2213_: *mut LeanObject,
    mut v_opt_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    v_name_2215_ = lean_ctor_get(v_opt_2214_, 0);
    v_defValue_2216_ = lean_ctor_get(v_opt_2214_, 1);
    v_map_2217_ = lean_ctor_get(v_opts_2213_, 0);
    v___x_2218_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2217_,
            v_name_2215_,
        );
    if lean_obj_tag(v___x_2218_) == 0 {
        lean_inc(v_defValue_2216_);
        return v_defValue_2216_;
    } else {
        let mut v_val_2219_: *mut LeanObject = core::ptr::null_mut();
        v_val_2219_ = lean_ctor_get(v___x_2218_, 0);
        lean_inc(v_val_2219_);
        lean_dec_ref_known(v___x_2218_, 1);
        if lean_obj_tag(v_val_2219_) == 3 {
            let mut v_v_2220_: *mut LeanObject = core::ptr::null_mut();
            v_v_2220_ = lean_ctor_get(v_val_2219_, 0);
            lean_inc(v_v_2220_);
            lean_dec_ref_known(v_val_2219_, 1);
            return v_v_2220_;
        } else {
            lean_dec(v_val_2219_);
            lean_inc(v_defValue_2216_);
            return v_defValue_2216_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(
    mut v_opts_2221_: *mut LeanObject,
    mut v_opt_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2223_: *mut LeanObject = core::ptr::null_mut();
    v_res_2223_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_2221_, v_opt_2222_);
    lean_dec_ref(v_opt_2222_);
    lean_dec_ref(v_opts_2221_);
    return v_res_2223_;
}
pub unsafe fn l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(
    mut v_s_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    v___x_2226_ = lean_get_stdout();
    v_putStr_2227_ = lean_ctor_get(v___x_2226_, 4);
    lean_inc_ref(v_putStr_2227_);
    lean_dec_ref(v___x_2226_);
    v___x_2228_ = lean_apply_2(v_putStr_2227_, v_s_2224_, lean_box(0));
    return v___x_2228_;
}
pub unsafe fn l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2___boxed(
    mut v_s_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ =
        l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(
            v_s_2229_,
        );
    return v_res_2231_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(
    mut v_s_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: u32 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = 10;
    v___x_2235_ = lean_string_push(v_s_2232_, v___x_2234_);
    v___x_2236_ =
        l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(
            v___x_2235_,
        );
    return v___x_2236_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3___boxed(
    mut v_s_2237_: *mut LeanObject,
    mut v_a_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2239_: *mut LeanObject = core::ptr::null_mut();
    v_res_2239_ =
        l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(
            v_s_2237_,
        );
    return v_res_2239_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(
    mut v_opts_2242_: *mut LeanObject,
    mut v_json_2243_: u8,
    mut v_includeEndPos_2244_: u8,
    mut v_severityOverrides_2245_: *mut LeanObject,
    mut v_as_2246_: *mut LeanObject,
    mut v_i_2247_: usize,
    mut v_stop_2248_: usize,
    mut v_b_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: usize = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___y_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: u8 = 0;
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v___y_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: u8 = 0;
    let mut v___y_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSilent_2273_: u8 = 0;
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2294_: u8 = 0;
    let mut v___y_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: u8 = 0;
    let mut v_isSilent_2300_: u8 = 0;
    let mut v_fileName_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_2304_: u8 = 0;
    let mut v_isSilent_2305_: u8 = 0;
    let mut v_caption_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_unused_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numErrors_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: u8 = 0;
    let mut v___y_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_2335_: u8 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_2342_: u8 = 0;
    let mut v_isSilent_2343_: u8 = 0;
    let mut v_caption_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2350_: u8 = 0;
    let mut v_val_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v_reuseFailAlloc_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_unused_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_2363_: u8 = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2323_ = lean_usize_dec_eq(v_i_2247_, v_stop_2248_);
                if v___x_2323_ == 0 {
                    v___x_2338_ = lean_array_uget(v_as_2246_, v_i_2247_);
                    v_fileName_2339_ = lean_ctor_get(v___x_2338_, 0);
                    v_pos_2340_ = lean_ctor_get(v___x_2338_, 1);
                    v_endPos_2341_ = lean_ctor_get(v___x_2338_, 2);
                    v_keepFullRange_2342_ = lean_ctor_get_uint8(
                        v___x_2338_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_isSilent_2343_ = lean_ctor_get_uint8(
                        v___x_2338_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    );
                    v_caption_2344_ = lean_ctor_get(v___x_2338_, 3);
                    v_data_2345_ = lean_ctor_get(v___x_2338_, 4);
                    v___x_2346_ = l_Lean_MessageData_kind(v_data_2345_);
                    v___x_2347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_severityOverrides_2245_, v___x_2346_);
                    lean_dec(v___x_2346_);
                    if lean_obj_tag(v___x_2347_) == 1 {
                        lean_inc(v_data_2345_);
                        lean_inc_ref(v_caption_2344_);
                        lean_inc(v_endPos_2341_);
                        lean_inc_ref(v_pos_2340_);
                        lean_inc_ref(v_fileName_2339_);
                        v_isSharedCheck_2357_ = (!lean_is_exclusive(v___x_2338_)) as u8;
                        if v_isSharedCheck_2357_ == 0 {
                            v_unused_2358_ = lean_ctor_get(v___x_2338_, 4);
                            lean_dec(v_unused_2358_);
                            v_unused_2359_ = lean_ctor_get(v___x_2338_, 3);
                            lean_dec(v_unused_2359_);
                            v_unused_2360_ = lean_ctor_get(v___x_2338_, 2);
                            lean_dec(v_unused_2360_);
                            v_unused_2361_ = lean_ctor_get(v___x_2338_, 1);
                            lean_dec(v_unused_2361_);
                            v_unused_2362_ = lean_ctor_get(v___x_2338_, 0);
                            lean_dec(v_unused_2362_);
                            v___x_2349_ = v___x_2338_;
                            v_isShared_2350_ = v_isSharedCheck_2357_;
                            state = 15;
                            continue;
                        } else {
                            lean_dec(v___x_2338_);
                            v___x_2349_ = lean_box(0);
                            v_isShared_2350_ = v_isSharedCheck_2357_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2347_);
                        v_severity_2363_ = lean_ctor_get_uint8(
                            v___x_2338_,
                            (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        );
                        v___y_2334_ = v___x_2338_;
                        v_severity_2335_ = v_severity_2363_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_2364_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2364_, 0, v_b_2249_);
                    return v___x_2364_;
                }
            }
            1 => {
                v___x_2253_ = 1usize;
                v___x_2254_ = lean_usize_add(v_i_2247_, v___x_2253_);
                v_i_2247_ = v___x_2254_;
                v_b_2249_ = v_a_2252_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2258_ == 0 {
                    v_a_2252_ = v___y_2257_;
                    state = 1;
                    continue;
                } else {
                    v___x_2259_ = 1;
                    v___x_2260_ = lean_io_exit(v___x_2259_);
                    if lean_obj_tag(v___x_2260_) == 0 {
                        lean_dec_ref_known(v___x_2260_, 1);
                        v_a_2252_ = v___y_2257_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_2257_);
                        v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
                        v_isSharedCheck_2268_ = (!lean_is_exclusive(v___x_2260_)) as u8;
                        if v_isSharedCheck_2268_ == 0 {
                            v___x_2263_ = v___x_2260_;
                            v_isShared_2264_ = v_isSharedCheck_2268_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2261_);
                            lean_dec(v___x_2260_);
                            v___x_2263_ = lean_box(0);
                            v_isShared_2264_ = v_isSharedCheck_2268_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2264_ == 0 {
                    v___x_2266_ = v___x_2263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2266_;
            }
            5 => {
                if v_isSilent_2273_ == 0 {
                    if v_json_2243_ == 0 {
                        v___x_2274_ = l_Lean_Message_toString(v___y_2272_, v_includeEndPos_2244_);
                        v___x_2275_ = l_IO_print___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(v___x_2274_);
                        if lean_obj_tag(v___x_2275_) == 0 {
                            lean_dec_ref_known(v___x_2275_, 1);
                            v___y_2257_ = v___y_2270_;
                            v___y_2258_ = v___y_2271_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___y_2270_);
                            v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
                            v_isSharedCheck_2283_ = (!lean_is_exclusive(v___x_2275_)) as u8;
                            if v_isSharedCheck_2283_ == 0 {
                                v___x_2278_ = v___x_2275_;
                                v_isShared_2279_ = v_isSharedCheck_2283_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2276_);
                                lean_dec(v___x_2275_);
                                v___x_2278_ = lean_box(0);
                                v_isShared_2279_ = v_isSharedCheck_2283_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_2284_ = l_Lean_Message_toJson(v___y_2272_);
                        v___x_2285_ = l_Lean_Json_compress(v___x_2284_);
                        v___x_2286_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_2285_);
                        if lean_obj_tag(v___x_2286_) == 0 {
                            lean_dec_ref_known(v___x_2286_, 1);
                            v___y_2257_ = v___y_2270_;
                            v___y_2258_ = v___y_2271_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___y_2270_);
                            v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
                            v_isSharedCheck_2294_ = (!lean_is_exclusive(v___x_2286_)) as u8;
                            if v_isSharedCheck_2294_ == 0 {
                                v___x_2289_ = v___x_2286_;
                                v_isShared_2290_ = v_isSharedCheck_2294_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2287_);
                                lean_dec(v___x_2286_);
                                v___x_2289_ = lean_box(0);
                                v_isShared_2290_ = v_isSharedCheck_2294_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2272_);
                    v___y_2257_ = v___y_2270_;
                    v___y_2258_ = v___y_2271_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_2279_ == 0 {
                    v___x_2281_ = v___x_2278_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2281_;
            }
            8 => {
                if v_isShared_2290_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2292_;
            }
            10 => {
                if v___y_2299_ == 0 {
                    lean_dec(v___y_2296_);
                    v_isSilent_2300_ = lean_ctor_get_uint8(
                        v___y_2298_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    );
                    v___y_2270_ = v___y_2297_;
                    v___y_2271_ = v___y_2299_;
                    v___y_2272_ = v___y_2298_;
                    v_isSilent_2273_ = v_isSilent_2300_;
                    state = 5;
                    continue;
                } else {
                    v_fileName_2301_ = lean_ctor_get(v___y_2298_, 0);
                    v_pos_2302_ = lean_ctor_get(v___y_2298_, 1);
                    v_endPos_2303_ = lean_ctor_get(v___y_2298_, 2);
                    v_keepFullRange_2304_ = lean_ctor_get_uint8(
                        v___y_2298_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_isSilent_2305_ = lean_ctor_get_uint8(
                        v___y_2298_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    );
                    v_caption_2306_ = lean_ctor_get(v___y_2298_, 3);
                    v_isSharedCheck_2321_ = (!lean_is_exclusive(v___y_2298_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v_unused_2322_ = lean_ctor_get(v___y_2298_, 4);
                        lean_dec(v_unused_2322_);
                        v___x_2308_ = v___y_2298_;
                        v_isShared_2309_ = v_isSharedCheck_2321_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_caption_2306_);
                        lean_inc(v_endPos_2303_);
                        lean_inc(v_pos_2302_);
                        lean_inc(v_fileName_2301_);
                        lean_dec(v___y_2298_);
                        v___x_2308_ = lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2321_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v___x_2310_ = 2;
                v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__0;
                v___x_2312_ = l_Nat_reprFast(v___y_2296_);
                v___x_2313_ = lean_string_append(v___x_2311_, v___x_2312_);
                lean_dec_ref(v___x_2312_);
                v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___closed__1;
                v___x_2315_ = lean_string_append(v___x_2313_, v___x_2314_);
                v___x_2316_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2316_, 0, v___x_2315_);
                v___x_2317_ = l_Lean_MessageData_ofFormat(v___x_2316_);
                if v_isShared_2309_ == 0 {
                    lean_ctor_set(v___x_2308_, 4, v___x_2317_);
                    v___x_2319_ = v___x_2308_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_fileName_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_pos_2302_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_endPos_2303_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_caption_2306_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 4, v___x_2317_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2320_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_keepFullRange_2304_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2320_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                        v_isSilent_2305_,
                    );
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_ctor_set_uint8(
                    v___x_2319_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2310_,
                );
                v___y_2270_ = v___y_2297_;
                v___y_2271_ = v___y_2299_;
                v___y_2272_ = v___x_2319_;
                v_isSilent_2273_ = v_isSilent_2305_;
                state = 5;
                continue;
            }
            13 => {
                v_numErrors_2327_ = lean_nat_add(v_b_2249_, v___y_2326_);
                lean_dec(v_b_2249_);
                v___x_2328_ = l_Lean_Language_maxErrors;
                v___x_2329_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(v_opts_2242_, v___x_2328_);
                v___x_2330_ = lean_unsigned_to_nat(0);
                v___x_2331_ = lean_nat_dec_eq(v___x_2329_, v___x_2330_);
                if v___x_2331_ == 0 {
                    v___x_2332_ = lean_nat_dec_lt(v___x_2329_, v_numErrors_2327_);
                    if v___x_2332_ == 0 {
                        v___y_2296_ = v___x_2329_;
                        v___y_2297_ = v_numErrors_2327_;
                        v___y_2298_ = v___y_2325_;
                        v___y_2299_ = v___x_2323_;
                        state = 10;
                        continue;
                    } else {
                        v___y_2296_ = v___x_2329_;
                        v___y_2297_ = v_numErrors_2327_;
                        v___y_2298_ = v___y_2325_;
                        v___y_2299_ = v___x_2332_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___y_2296_ = v___x_2329_;
                    v___y_2297_ = v_numErrors_2327_;
                    v___y_2298_ = v___y_2325_;
                    v___y_2299_ = v___x_2323_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                if v_severity_2335_ == 2 {
                    v___x_2336_ = lean_unsigned_to_nat(1);
                    v___y_2325_ = v___y_2334_;
                    v___y_2326_ = v___x_2336_;
                    state = 13;
                    continue;
                } else {
                    v___x_2337_ = lean_unsigned_to_nat(0);
                    v___y_2325_ = v___y_2334_;
                    v___y_2326_ = v___x_2337_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v_val_2351_ = lean_ctor_get(v___x_2347_, 0);
                lean_inc(v_val_2351_);
                lean_dec_ref_known(v___x_2347_, 1);
                if v_isShared_2350_ == 0 {
                    v___x_2353_ = v___x_2349_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 5, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_fileName_2339_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_pos_2340_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_endPos_2341_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_caption_2344_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 4, v_data_2345_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2356_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_keepFullRange_2342_,
                    );
                    v___x_2353_ = v_reuseFailAlloc_2356_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2354_ = (lean_unbox(v_val_2351_) as u8);
                lean_ctor_set_uint8(
                    v___x_2353_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2354_,
                );
                lean_ctor_set_uint8(
                    v___x_2353_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2343_,
                );
                v___x_2355_ = (lean_unbox(v_val_2351_) as u8);
                lean_dec(v_val_2351_);
                v___y_2334_ = v___x_2353_;
                v_severity_2335_ = v___x_2355_;
                state = 14;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5___boxed(
    mut v_opts_2365_: *mut LeanObject,
    mut v_json_2366_: *mut LeanObject,
    mut v_includeEndPos_2367_: *mut LeanObject,
    mut v_severityOverrides_2368_: *mut LeanObject,
    mut v_as_2369_: *mut LeanObject,
    mut v_i_2370_: *mut LeanObject,
    mut v_stop_2371_: *mut LeanObject,
    mut v_b_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2374_: u8 = 0;
    let mut v_includeEndPos_boxed_2375_: u8 = 0;
    let mut v_i_boxed_2376_: usize = 0;
    let mut v_stop_boxed_2377_: usize = 0;
    let mut v_res_2378_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2374_ = (lean_unbox(v_json_2366_) as u8);
    v_includeEndPos_boxed_2375_ = (lean_unbox(v_includeEndPos_2367_) as u8);
    v_i_boxed_2376_ = lean_unbox_usize(v_i_2370_);
    lean_dec(v_i_2370_);
    v_stop_boxed_2377_ = lean_unbox_usize(v_stop_2371_);
    lean_dec(v_stop_2371_);
    v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2365_, v_json_boxed_2374_, v_includeEndPos_boxed_2375_, v_severityOverrides_2368_, v_as_2369_, v_i_boxed_2376_, v_stop_boxed_2377_, v_b_2372_);
    lean_dec_ref(v_as_2369_);
    lean_dec(v_severityOverrides_2368_);
    lean_dec_ref(v_opts_2365_);
    return v_res_2378_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(
    mut v_opts_2379_: *mut LeanObject,
    mut v_json_2380_: u8,
    mut v_includeEndPos_2381_: u8,
    mut v_severityOverrides_2382_: *mut LeanObject,
    mut v_x_2383_: *mut LeanObject,
    mut v_x_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2389_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: usize = 0;
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v_vs_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: usize = 0;
    let mut v___x_2422_: usize = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: usize = 0;
    let mut v___x_2425_: usize = 0;
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2383_) == 0 {
                    v_cs_2386_ = lean_ctor_get(v_x_2383_, 0);
                    v_isSharedCheck_2406_ = (!lean_is_exclusive(v_x_2383_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2388_ = v_x_2383_;
                        v_isShared_2389_ = v_isSharedCheck_2406_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_2386_);
                        lean_dec(v_x_2383_);
                        v___x_2388_ = lean_box(0);
                        v_isShared_2389_ = v_isSharedCheck_2406_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2407_ = lean_ctor_get(v_x_2383_, 0);
                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v_x_2383_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2409_ = v_x_2383_;
                        v_isShared_2410_ = v_isSharedCheck_2427_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_2407_);
                        lean_dec(v_x_2383_);
                        v___x_2409_ = lean_box(0);
                        v_isShared_2410_ = v_isSharedCheck_2427_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2390_ = lean_unsigned_to_nat(0);
                v___x_2391_ = lean_array_get_size(v_cs_2386_);
                v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
                if v___x_2392_ == 0 {
                    lean_dec_ref(v_cs_2386_);
                    if v_isShared_2389_ == 0 {
                        lean_ctor_set(v___x_2388_, 0, v_x_2384_);
                        v___x_2394_ = v___x_2388_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_x_2384_);
                        v___x_2394_ = v_reuseFailAlloc_2395_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2396_ = lean_nat_dec_le(v___x_2391_, v___x_2391_);
                    if v___x_2396_ == 0 {
                        if v___x_2392_ == 0 {
                            lean_dec_ref(v_cs_2386_);
                            if v_isShared_2389_ == 0 {
                                lean_ctor_set(v___x_2388_, 0, v_x_2384_);
                                v___x_2398_ = v___x_2388_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_x_2384_);
                                v___x_2398_ = v_reuseFailAlloc_2399_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2388_);
                            v___x_2400_ = 0usize;
                            v___x_2401_ = lean_usize_of_nat(v___x_2391_);
                            v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_2379_, v_json_2380_, v_includeEndPos_2381_, v_severityOverrides_2382_, v_cs_2386_, v___x_2400_, v___x_2401_, v_x_2384_);
                            lean_dec_ref(v_cs_2386_);
                            return v___x_2402_;
                        }
                    } else {
                        lean_del_object(v___x_2388_);
                        v___x_2403_ = 0usize;
                        v___x_2404_ = lean_usize_of_nat(v___x_2391_);
                        v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_2379_, v_json_2380_, v_includeEndPos_2381_, v_severityOverrides_2382_, v_cs_2386_, v___x_2403_, v___x_2404_, v_x_2384_);
                        lean_dec_ref(v_cs_2386_);
                        return v___x_2405_;
                    }
                }
            }
            2 => {
                return v___x_2394_;
            }
            3 => {
                return v___x_2398_;
            }
            4 => {
                v___x_2411_ = lean_unsigned_to_nat(0);
                v___x_2412_ = lean_array_get_size(v_vs_2407_);
                v___x_2413_ = lean_nat_dec_lt(v___x_2411_, v___x_2412_);
                if v___x_2413_ == 0 {
                    lean_dec_ref(v_vs_2407_);
                    if v_isShared_2410_ == 0 {
                        lean_ctor_set_tag(v___x_2409_, 0);
                        lean_ctor_set(v___x_2409_, 0, v_x_2384_);
                        v___x_2415_ = v___x_2409_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_x_2384_);
                        v___x_2415_ = v_reuseFailAlloc_2416_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2417_ = lean_nat_dec_le(v___x_2412_, v___x_2412_);
                    if v___x_2417_ == 0 {
                        if v___x_2413_ == 0 {
                            lean_dec_ref(v_vs_2407_);
                            if v_isShared_2410_ == 0 {
                                lean_ctor_set_tag(v___x_2409_, 0);
                                lean_ctor_set(v___x_2409_, 0, v_x_2384_);
                                v___x_2419_ = v___x_2409_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_x_2384_);
                                v___x_2419_ = v_reuseFailAlloc_2420_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2409_);
                            v___x_2421_ = 0usize;
                            v___x_2422_ = lean_usize_of_nat(v___x_2412_);
                            v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2379_, v_json_2380_, v_includeEndPos_2381_, v_severityOverrides_2382_, v_vs_2407_, v___x_2421_, v___x_2422_, v_x_2384_);
                            lean_dec_ref(v_vs_2407_);
                            return v___x_2423_;
                        }
                    } else {
                        lean_del_object(v___x_2409_);
                        v___x_2424_ = 0usize;
                        v___x_2425_ = lean_usize_of_nat(v___x_2412_);
                        v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2379_, v_json_2380_, v_includeEndPos_2381_, v_severityOverrides_2382_, v_vs_2407_, v___x_2424_, v___x_2425_, v_x_2384_);
                        lean_dec_ref(v_vs_2407_);
                        return v___x_2426_;
                    }
                }
            }
            5 => {
                return v___x_2415_;
            }
            6 => {
                return v___x_2419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(
    mut v_opts_2428_: *mut LeanObject,
    mut v_json_2429_: u8,
    mut v_includeEndPos_2430_: u8,
    mut v_severityOverrides_2431_: *mut LeanObject,
    mut v_as_2432_: *mut LeanObject,
    mut v_i_2433_: usize,
    mut v_stop_2434_: usize,
    mut v_b_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2437_ = lean_usize_dec_eq(v_i_2433_, v_stop_2434_);
                if v___x_2437_ == 0 {
                    v___x_2438_ = lean_array_uget_borrowed(v_as_2432_, v_i_2433_);
                    lean_inc(v___x_2438_);
                    v___x_2439_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_2428_, v_json_2429_, v_includeEndPos_2430_, v_severityOverrides_2431_, v___x_2438_, v_b_2435_);
                    if lean_obj_tag(v___x_2439_) == 0 {
                        v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
                        lean_inc(v_a_2440_);
                        lean_dec_ref_known(v___x_2439_, 1);
                        v___x_2441_ = 1usize;
                        v___x_2442_ = lean_usize_add(v_i_2433_, v___x_2441_);
                        v_i_2433_ = v___x_2442_;
                        v_b_2435_ = v_a_2440_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2439_;
                    }
                } else {
                    v___x_2444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2444_, 0, v_b_2435_);
                    return v___x_2444_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5___boxed(
    mut v_opts_2445_: *mut LeanObject,
    mut v_json_2446_: *mut LeanObject,
    mut v_includeEndPos_2447_: *mut LeanObject,
    mut v_severityOverrides_2448_: *mut LeanObject,
    mut v_as_2449_: *mut LeanObject,
    mut v_i_2450_: *mut LeanObject,
    mut v_stop_2451_: *mut LeanObject,
    mut v_b_2452_: *mut LeanObject,
    mut v___y_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2454_: u8 = 0;
    let mut v_includeEndPos_boxed_2455_: u8 = 0;
    let mut v_i_boxed_2456_: usize = 0;
    let mut v_stop_boxed_2457_: usize = 0;
    let mut v_res_2458_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2454_ = (lean_unbox(v_json_2446_) as u8);
    v_includeEndPos_boxed_2455_ = (lean_unbox(v_includeEndPos_2447_) as u8);
    v_i_boxed_2456_ = lean_unbox_usize(v_i_2450_);
    lean_dec(v_i_2450_);
    v_stop_boxed_2457_ = lean_unbox_usize(v_stop_2451_);
    lean_dec(v_stop_2451_);
    v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_2445_, v_json_boxed_2454_, v_includeEndPos_boxed_2455_, v_severityOverrides_2448_, v_as_2449_, v_i_boxed_2456_, v_stop_boxed_2457_, v_b_2452_);
    lean_dec_ref(v_as_2449_);
    lean_dec(v_severityOverrides_2448_);
    lean_dec_ref(v_opts_2445_);
    return v_res_2458_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6___boxed(
    mut v_opts_2459_: *mut LeanObject,
    mut v_json_2460_: *mut LeanObject,
    mut v_includeEndPos_2461_: *mut LeanObject,
    mut v_severityOverrides_2462_: *mut LeanObject,
    mut v_x_2463_: *mut LeanObject,
    mut v_x_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2466_: u8 = 0;
    let mut v_includeEndPos_boxed_2467_: u8 = 0;
    let mut v_res_2468_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2466_ = (lean_unbox(v_json_2460_) as u8);
    v_includeEndPos_boxed_2467_ = (lean_unbox(v_includeEndPos_2461_) as u8);
    v_res_2468_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_2459_, v_json_boxed_2466_, v_includeEndPos_boxed_2467_, v_severityOverrides_2462_, v_x_2463_, v_x_2464_);
    lean_dec(v_severityOverrides_2462_);
    lean_dec_ref(v_opts_2459_);
    return v_res_2468_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_2469_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(
    mut v_opts_2470_: *mut LeanObject,
    mut v_json_2471_: u8,
    mut v_includeEndPos_2472_: u8,
    mut v_severityOverrides_2473_: *mut LeanObject,
    mut v_x_2474_: *mut LeanObject,
    mut v_x_2475_: usize,
    mut v_x_2476_: usize,
    mut v_x_2477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: usize = 0;
    let mut v_j_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: usize = 0;
    let mut v___x_2486_: usize = 0;
    let mut v___x_2487_: usize = 0;
    let mut v___x_2488_: usize = 0;
    let mut v___x_2489_: usize = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: usize = 0;
    let mut v___x_2498_: usize = 0;
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: usize = 0;
    let mut v___x_2501_: usize = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2506_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: usize = 0;
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: usize = 0;
    let mut v___x_2521_: usize = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2474_) == 0 {
                    v_cs_2479_ = lean_ctor_get(v_x_2474_, 0);
                    lean_inc_ref(v_cs_2479_);
                    lean_dec_ref_known(v_x_2474_, 1);
                    v___x_2480_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
                    v___x_2481_ = lean_usize_shift_right(v_x_2475_, v_x_2476_);
                    v_j_2482_ = lean_usize_to_nat(v___x_2481_);
                    v___x_2483_ = lean_array_get_borrowed(v___x_2480_, v_cs_2479_, v_j_2482_);
                    v___x_2484_ = 1usize;
                    v___x_2485_ = lean_usize_shift_left(v___x_2484_, v_x_2476_);
                    v___x_2486_ = lean_usize_sub(v___x_2485_, v___x_2484_);
                    v___x_2487_ = lean_usize_land(v_x_2475_, v___x_2486_);
                    v___x_2488_ = 5usize;
                    v___x_2489_ = lean_usize_sub(v_x_2476_, v___x_2488_);
                    lean_inc(v___x_2483_);
                    v___x_2490_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_2470_, v_json_2471_, v_includeEndPos_2472_, v_severityOverrides_2473_, v___x_2483_, v___x_2487_, v___x_2489_, v_x_2477_);
                    if lean_obj_tag(v___x_2490_) == 0 {
                        v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
                        lean_inc(v_a_2491_);
                        v___x_2492_ = lean_unsigned_to_nat(1);
                        v___x_2493_ = lean_nat_add(v_j_2482_, v___x_2492_);
                        lean_dec(v_j_2482_);
                        v___x_2494_ = lean_array_get_size(v_cs_2479_);
                        v___x_2495_ = lean_nat_dec_lt(v___x_2493_, v___x_2494_);
                        if v___x_2495_ == 0 {
                            lean_dec(v___x_2493_);
                            lean_dec(v_a_2491_);
                            lean_dec_ref(v_cs_2479_);
                            return v___x_2490_;
                        } else {
                            v___x_2496_ = lean_nat_dec_le(v___x_2494_, v___x_2494_);
                            if v___x_2496_ == 0 {
                                if v___x_2495_ == 0 {
                                    lean_dec(v___x_2493_);
                                    lean_dec(v_a_2491_);
                                    lean_dec_ref(v_cs_2479_);
                                    return v___x_2490_;
                                } else {
                                    lean_dec_ref_known(v___x_2490_, 1);
                                    v___x_2497_ = lean_usize_of_nat(v___x_2493_);
                                    lean_dec(v___x_2493_);
                                    v___x_2498_ = lean_usize_of_nat(v___x_2494_);
                                    v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_2470_, v_json_2471_, v_includeEndPos_2472_, v_severityOverrides_2473_, v_cs_2479_, v___x_2497_, v___x_2498_, v_a_2491_);
                                    lean_dec_ref(v_cs_2479_);
                                    return v___x_2499_;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2490_, 1);
                                v___x_2500_ = lean_usize_of_nat(v___x_2493_);
                                lean_dec(v___x_2493_);
                                v___x_2501_ = lean_usize_of_nat(v___x_2494_);
                                v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__5(v_opts_2470_, v_json_2471_, v_includeEndPos_2472_, v_severityOverrides_2473_, v_cs_2479_, v___x_2500_, v___x_2501_, v_a_2491_);
                                lean_dec_ref(v_cs_2479_);
                                return v___x_2502_;
                            }
                        }
                    } else {
                        lean_dec(v_j_2482_);
                        lean_dec_ref(v_cs_2479_);
                        return v___x_2490_;
                    }
                } else {
                    v_vs_2503_ = lean_ctor_get(v_x_2474_, 0);
                    v_isSharedCheck_2523_ = (!lean_is_exclusive(v_x_2474_)) as u8;
                    if v_isSharedCheck_2523_ == 0 {
                        v___x_2505_ = v_x_2474_;
                        v_isShared_2506_ = v_isSharedCheck_2523_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vs_2503_);
                        lean_dec(v_x_2474_);
                        v___x_2505_ = lean_box(0);
                        v_isShared_2506_ = v_isSharedCheck_2523_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2507_ = lean_usize_to_nat(v_x_2475_);
                v___x_2508_ = lean_array_get_size(v_vs_2503_);
                v___x_2509_ = lean_nat_dec_lt(v___x_2507_, v___x_2508_);
                if v___x_2509_ == 0 {
                    lean_dec(v___x_2507_);
                    lean_dec_ref(v_vs_2503_);
                    if v_isShared_2506_ == 0 {
                        lean_ctor_set_tag(v___x_2505_, 0);
                        lean_ctor_set(v___x_2505_, 0, v_x_2477_);
                        v___x_2511_ = v___x_2505_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_x_2477_);
                        v___x_2511_ = v_reuseFailAlloc_2512_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2513_ = lean_nat_dec_le(v___x_2508_, v___x_2508_);
                    if v___x_2513_ == 0 {
                        if v___x_2509_ == 0 {
                            lean_dec(v___x_2507_);
                            lean_dec_ref(v_vs_2503_);
                            if v_isShared_2506_ == 0 {
                                lean_ctor_set_tag(v___x_2505_, 0);
                                lean_ctor_set(v___x_2505_, 0, v_x_2477_);
                                v___x_2515_ = v___x_2505_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_x_2477_);
                                v___x_2515_ = v_reuseFailAlloc_2516_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2505_);
                            v___x_2517_ = lean_usize_of_nat(v___x_2507_);
                            lean_dec(v___x_2507_);
                            v___x_2518_ = lean_usize_of_nat(v___x_2508_);
                            v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2470_, v_json_2471_, v_includeEndPos_2472_, v_severityOverrides_2473_, v_vs_2503_, v___x_2517_, v___x_2518_, v_x_2477_);
                            lean_dec_ref(v_vs_2503_);
                            return v___x_2519_;
                        }
                    } else {
                        lean_del_object(v___x_2505_);
                        v___x_2520_ = lean_usize_of_nat(v___x_2507_);
                        lean_dec(v___x_2507_);
                        v___x_2521_ = lean_usize_of_nat(v___x_2508_);
                        v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2470_, v_json_2471_, v_includeEndPos_2472_, v_severityOverrides_2473_, v_vs_2503_, v___x_2520_, v___x_2521_, v_x_2477_);
                        lean_dec_ref(v_vs_2503_);
                        return v___x_2522_;
                    }
                }
            }
            2 => {
                return v___x_2511_;
            }
            3 => {
                return v___x_2515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(
    mut v_opts_2524_: *mut LeanObject,
    mut v_json_2525_: *mut LeanObject,
    mut v_includeEndPos_2526_: *mut LeanObject,
    mut v_severityOverrides_2527_: *mut LeanObject,
    mut v_x_2528_: *mut LeanObject,
    mut v_x_2529_: *mut LeanObject,
    mut v_x_2530_: *mut LeanObject,
    mut v_x_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2533_: u8 = 0;
    let mut v_includeEndPos_boxed_2534_: u8 = 0;
    let mut v_x_2643__boxed_2535_: usize = 0;
    let mut v_x_2644__boxed_2536_: usize = 0;
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2533_ = (lean_unbox(v_json_2525_) as u8);
    v_includeEndPos_boxed_2534_ = (lean_unbox(v_includeEndPos_2526_) as u8);
    v_x_2643__boxed_2535_ = lean_unbox_usize(v_x_2529_);
    lean_dec(v_x_2529_);
    v_x_2644__boxed_2536_ = lean_unbox_usize(v_x_2530_);
    lean_dec(v_x_2530_);
    v_res_2537_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_2524_, v_json_boxed_2533_, v_includeEndPos_boxed_2534_, v_severityOverrides_2527_, v_x_2528_, v_x_2643__boxed_2535_, v_x_2644__boxed_2536_, v_x_2531_);
    lean_dec(v_severityOverrides_2527_);
    lean_dec_ref(v_opts_2524_);
    return v_res_2537_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(
    mut v_opts_2538_: *mut LeanObject,
    mut v_json_2539_: u8,
    mut v_includeEndPos_2540_: u8,
    mut v_severityOverrides_2541_: *mut LeanObject,
    mut v_t_2542_: *mut LeanObject,
    mut v_init_2543_: *mut LeanObject,
    mut v_start_2544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    v___x_2546_ = lean_unsigned_to_nat(0);
    v___x_2547_ = lean_nat_dec_eq(v_start_2544_, v___x_2546_);
    if v___x_2547_ == 0 {
        let mut v_root_2548_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2549_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_2550_: usize = 0;
        let mut v_tailOff_2551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: u8 = 0;
        v_root_2548_ = lean_ctor_get(v_t_2542_, 0);
        lean_inc_ref(v_root_2548_);
        v_tail_2549_ = lean_ctor_get(v_t_2542_, 1);
        lean_inc_ref(v_tail_2549_);
        v_shift_2550_ = lean_ctor_get_usize(v_t_2542_, 4);
        v_tailOff_2551_ = lean_ctor_get(v_t_2542_, 3);
        lean_inc(v_tailOff_2551_);
        lean_dec_ref(v_t_2542_);
        v___x_2552_ = lean_nat_dec_le(v_tailOff_2551_, v_start_2544_);
        if v___x_2552_ == 0 {
            let mut v___x_2553_: usize = 0;
            let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_2551_);
            v___x_2553_ = lean_usize_of_nat(v_start_2544_);
            v___x_2554_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_root_2548_, v___x_2553_, v_shift_2550_, v_init_2543_);
            if lean_obj_tag(v___x_2554_) == 0 {
                let mut v_a_2555_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2557_: u8 = 0;
                v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
                lean_inc(v_a_2555_);
                v___x_2556_ = lean_array_get_size(v_tail_2549_);
                v___x_2557_ = lean_nat_dec_lt(v___x_2546_, v___x_2556_);
                if v___x_2557_ == 0 {
                    lean_dec(v_a_2555_);
                    lean_dec_ref(v_tail_2549_);
                    return v___x_2554_;
                } else {
                    let mut v___x_2558_: u8 = 0;
                    v___x_2558_ = lean_nat_dec_le(v___x_2556_, v___x_2556_);
                    if v___x_2558_ == 0 {
                        if v___x_2557_ == 0 {
                            lean_dec(v_a_2555_);
                            lean_dec_ref(v_tail_2549_);
                            return v___x_2554_;
                        } else {
                            let mut v___x_2559_: usize = 0;
                            let mut v___x_2560_: usize = 0;
                            let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_2554_, 1);
                            v___x_2559_ = 0usize;
                            v___x_2560_ = lean_usize_of_nat(v___x_2556_);
                            v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2549_, v___x_2559_, v___x_2560_, v_a_2555_);
                            lean_dec_ref(v_tail_2549_);
                            return v___x_2561_;
                        }
                    } else {
                        let mut v___x_2562_: usize = 0;
                        let mut v___x_2563_: usize = 0;
                        let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2554_, 1);
                        v___x_2562_ = 0usize;
                        v___x_2563_ = lean_usize_of_nat(v___x_2556_);
                        v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2549_, v___x_2562_, v___x_2563_, v_a_2555_);
                        lean_dec_ref(v_tail_2549_);
                        return v___x_2564_;
                    }
                }
            } else {
                lean_dec_ref(v_tail_2549_);
                return v___x_2554_;
            }
        } else {
            let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: u8 = 0;
            lean_dec_ref(v_root_2548_);
            v___x_2565_ = lean_nat_sub(v_start_2544_, v_tailOff_2551_);
            lean_dec(v_tailOff_2551_);
            v___x_2566_ = lean_array_get_size(v_tail_2549_);
            v___x_2567_ = lean_nat_dec_lt(v___x_2565_, v___x_2566_);
            if v___x_2567_ == 0 {
                let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2565_);
                lean_dec_ref(v_tail_2549_);
                v___x_2568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2568_, 0, v_init_2543_);
                return v___x_2568_;
            } else {
                let mut v___x_2569_: u8 = 0;
                v___x_2569_ = lean_nat_dec_le(v___x_2566_, v___x_2566_);
                if v___x_2569_ == 0 {
                    if v___x_2567_ == 0 {
                        let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_2565_);
                        lean_dec_ref(v_tail_2549_);
                        v___x_2570_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2570_, 0, v_init_2543_);
                        return v___x_2570_;
                    } else {
                        let mut v___x_2571_: usize = 0;
                        let mut v___x_2572_: usize = 0;
                        let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2571_ = lean_usize_of_nat(v___x_2565_);
                        lean_dec(v___x_2565_);
                        v___x_2572_ = lean_usize_of_nat(v___x_2566_);
                        v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2549_, v___x_2571_, v___x_2572_, v_init_2543_);
                        lean_dec_ref(v_tail_2549_);
                        return v___x_2573_;
                    }
                } else {
                    let mut v___x_2574_: usize = 0;
                    let mut v___x_2575_: usize = 0;
                    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2574_ = lean_usize_of_nat(v___x_2565_);
                    lean_dec(v___x_2565_);
                    v___x_2575_ = lean_usize_of_nat(v___x_2566_);
                    v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2549_, v___x_2574_, v___x_2575_, v_init_2543_);
                    lean_dec_ref(v_tail_2549_);
                    return v___x_2576_;
                }
            }
        }
    } else {
        let mut v_root_2577_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
        v_root_2577_ = lean_ctor_get(v_t_2542_, 0);
        lean_inc_ref(v_root_2577_);
        v_tail_2578_ = lean_ctor_get(v_t_2542_, 1);
        lean_inc_ref(v_tail_2578_);
        lean_dec_ref(v_t_2542_);
        v___x_2579_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__6(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_root_2577_, v_init_2543_);
        if lean_obj_tag(v___x_2579_) == 0 {
            let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2582_: u8 = 0;
            v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
            lean_inc(v_a_2580_);
            v___x_2581_ = lean_array_get_size(v_tail_2578_);
            v___x_2582_ = lean_nat_dec_lt(v___x_2546_, v___x_2581_);
            if v___x_2582_ == 0 {
                lean_dec(v_a_2580_);
                lean_dec_ref(v_tail_2578_);
                return v___x_2579_;
            } else {
                let mut v___x_2583_: u8 = 0;
                v___x_2583_ = lean_nat_dec_le(v___x_2581_, v___x_2581_);
                if v___x_2583_ == 0 {
                    if v___x_2582_ == 0 {
                        lean_dec(v_a_2580_);
                        lean_dec_ref(v_tail_2578_);
                        return v___x_2579_;
                    } else {
                        let mut v___x_2584_: usize = 0;
                        let mut v___x_2585_: usize = 0;
                        let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2584_ = 0usize;
                        v___x_2585_ = lean_usize_of_nat(v___x_2581_);
                        v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2578_, v___x_2584_, v___x_2585_, v_a_2580_);
                        lean_dec_ref(v_tail_2578_);
                        return v___x_2586_;
                    }
                } else {
                    let mut v___x_2587_: usize = 0;
                    let mut v___x_2588_: usize = 0;
                    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_2579_, 1);
                    v___x_2587_ = 0usize;
                    v___x_2588_ = lean_usize_of_nat(v___x_2581_);
                    v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__5(v_opts_2538_, v_json_2539_, v_includeEndPos_2540_, v_severityOverrides_2541_, v_tail_2578_, v___x_2587_, v___x_2588_, v_a_2580_);
                    lean_dec_ref(v_tail_2578_);
                    return v___x_2589_;
                }
            }
        } else {
            lean_dec_ref(v_tail_2578_);
            return v___x_2579_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(
    mut v_opts_2590_: *mut LeanObject,
    mut v_json_2591_: *mut LeanObject,
    mut v_includeEndPos_2592_: *mut LeanObject,
    mut v_severityOverrides_2593_: *mut LeanObject,
    mut v_t_2594_: *mut LeanObject,
    mut v_init_2595_: *mut LeanObject,
    mut v_start_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2598_: u8 = 0;
    let mut v_includeEndPos_boxed_2599_: u8 = 0;
    let mut v_res_2600_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2598_ = (lean_unbox(v_json_2591_) as u8);
    v_includeEndPos_boxed_2599_ = (lean_unbox(v_includeEndPos_2592_) as u8);
    v_res_2600_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_2590_, v_json_boxed_2598_, v_includeEndPos_boxed_2599_, v_severityOverrides_2593_, v_t_2594_, v_init_2595_, v_start_2596_);
    lean_dec(v_start_2596_);
    lean_dec(v_severityOverrides_2593_);
    lean_dec_ref(v_opts_2590_);
    return v_res_2600_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(
    mut v_msgLog_2601_: *mut LeanObject,
    mut v_opts_2602_: *mut LeanObject,
    mut v_json_2603_: u8,
    mut v_severityOverrides_2604_: *mut LeanObject,
    mut v_numErrors_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_unreported_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeEndPos_2609_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    v_unreported_2607_ = lean_ctor_get(v_msgLog_2601_, 1);
    lean_inc_ref(v_unreported_2607_);
    lean_dec_ref(v_msgLog_2601_);
    v___x_2608_ = l_Lean_Language_printMessageEndPos;
    v_includeEndPos_2609_ = l_Lean_Option_get___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(v_opts_2602_, v___x_2608_);
    v___x_2610_ = lean_unsigned_to_nat(0);
    v___x_2611_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(v_opts_2602_, v_json_2603_, v_includeEndPos_2609_, v_severityOverrides_2604_, v_unreported_2607_, v_numErrors_2605_, v___x_2610_);
    return v___x_2611_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(
    mut v_msgLog_2612_: *mut LeanObject,
    mut v_opts_2613_: *mut LeanObject,
    mut v_json_2614_: *mut LeanObject,
    mut v_severityOverrides_2615_: *mut LeanObject,
    mut v_numErrors_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2618_: u8 = 0;
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2618_ = (lean_unbox(v_json_2614_) as u8);
    v_res_2619_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(
        v_msgLog_2612_,
        v_opts_2613_,
        v_json_boxed_2618_,
        v_severityOverrides_2615_,
        v_numErrors_2616_,
    );
    lean_dec(v_severityOverrides_2615_);
    lean_dec_ref(v_opts_2613_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(
    mut v_opts_2620_: *mut LeanObject,
    mut v_json_2621_: u8,
    mut v_severityOverrides_2622_: *mut LeanObject,
    mut v_s_2623_: *mut LeanObject,
    mut v_init_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_element_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgLog_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    v_element_2626_ = lean_ctor_get(v_s_2623_, 0);
    v_diagnostics_2627_ = lean_ctor_get(v_element_2626_, 1);
    lean_inc_ref(v_diagnostics_2627_);
    v_children_2628_ = lean_ctor_get(v_s_2623_, 1);
    lean_inc_ref(v_children_2628_);
    lean_dec_ref(v_s_2623_);
    v_msgLog_2629_ = lean_ctor_get(v_diagnostics_2627_, 0);
    lean_inc_ref(v_msgLog_2629_);
    lean_dec_ref(v_diagnostics_2627_);
    v___x_2630_ = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(
        v_msgLog_2629_,
        v_opts_2620_,
        v_json_2621_,
        v_severityOverrides_2622_,
        v_init_2624_,
    );
    if lean_obj_tag(v___x_2630_) == 0 {
        let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2634_: u8 = 0;
        v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
        lean_inc(v_a_2631_);
        v___x_2632_ = lean_unsigned_to_nat(0);
        v___x_2633_ = lean_array_get_size(v_children_2628_);
        v___x_2634_ = lean_nat_dec_lt(v___x_2632_, v___x_2633_);
        if v___x_2634_ == 0 {
            lean_dec(v_a_2631_);
            lean_dec_ref(v_children_2628_);
            return v___x_2630_;
        } else {
            let mut v___x_2635_: u8 = 0;
            v___x_2635_ = lean_nat_dec_le(v___x_2633_, v___x_2633_);
            if v___x_2635_ == 0 {
                if v___x_2634_ == 0 {
                    lean_dec(v_a_2631_);
                    lean_dec_ref(v_children_2628_);
                    return v___x_2630_;
                } else {
                    let mut v___x_2636_: usize = 0;
                    let mut v___x_2637_: usize = 0;
                    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_2630_, 1);
                    v___x_2636_ = 0usize;
                    v___x_2637_ = lean_usize_of_nat(v___x_2633_);
                    v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_2620_, v_json_2621_, v_severityOverrides_2622_, v_children_2628_, v___x_2636_, v___x_2637_, v_a_2631_);
                    lean_dec_ref(v_children_2628_);
                    return v___x_2638_;
                }
            } else {
                let mut v___x_2639_: usize = 0;
                let mut v___x_2640_: usize = 0;
                let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_2630_, 1);
                v___x_2639_ = 0usize;
                v___x_2640_ = lean_usize_of_nat(v___x_2633_);
                v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_2620_, v_json_2621_, v_severityOverrides_2622_, v_children_2628_, v___x_2639_, v___x_2640_, v_a_2631_);
                lean_dec_ref(v_children_2628_);
                return v___x_2641_;
            }
        }
    } else {
        lean_dec_ref(v_children_2628_);
        return v___x_2630_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(
    mut v_opts_2642_: *mut LeanObject,
    mut v_json_2643_: u8,
    mut v_severityOverrides_2644_: *mut LeanObject,
    mut v_as_2645_: *mut LeanObject,
    mut v_i_2646_: usize,
    mut v_stop_2647_: usize,
    mut v_b_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2650_ = lean_usize_dec_eq(v_i_2646_, v_stop_2647_);
                if v___x_2650_ == 0 {
                    v___x_2651_ = lean_array_uget_borrowed(v_as_2645_, v_i_2646_);
                    lean_inc(v___x_2651_);
                    v___x_2652_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2651_);
                    v___x_2653_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_2642_, v_json_2643_, v_severityOverrides_2644_, v___x_2652_, v_b_2648_);
                    if lean_obj_tag(v___x_2653_) == 0 {
                        v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
                        lean_inc(v_a_2654_);
                        lean_dec_ref_known(v___x_2653_, 1);
                        v___x_2655_ = 1usize;
                        v___x_2656_ = lean_usize_add(v_i_2646_, v___x_2655_);
                        v_i_2646_ = v___x_2656_;
                        v_b_2648_ = v_a_2654_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2653_;
                    }
                } else {
                    v___x_2658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2658_, 0, v_b_2648_);
                    return v___x_2658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(
    mut v_opts_2659_: *mut LeanObject,
    mut v_json_2660_: *mut LeanObject,
    mut v_severityOverrides_2661_: *mut LeanObject,
    mut v_as_2662_: *mut LeanObject,
    mut v_i_2663_: *mut LeanObject,
    mut v_stop_2664_: *mut LeanObject,
    mut v_b_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2667_: u8 = 0;
    let mut v_i_boxed_2668_: usize = 0;
    let mut v_stop_boxed_2669_: usize = 0;
    let mut v_res_2670_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2667_ = (lean_unbox(v_json_2660_) as u8);
    v_i_boxed_2668_ = lean_unbox_usize(v_i_2663_);
    lean_dec(v_i_2663_);
    v_stop_boxed_2669_ = lean_unbox_usize(v_stop_2664_);
    lean_dec(v_stop_2664_);
    v_res_2670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(v_opts_2659_, v_json_boxed_2667_, v_severityOverrides_2661_, v_as_2662_, v_i_boxed_2668_, v_stop_boxed_2669_, v_b_2665_);
    lean_dec_ref(v_as_2662_);
    lean_dec(v_severityOverrides_2661_);
    lean_dec_ref(v_opts_2659_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(
    mut v_opts_2671_: *mut LeanObject,
    mut v_json_2672_: *mut LeanObject,
    mut v_severityOverrides_2673_: *mut LeanObject,
    mut v_s_2674_: *mut LeanObject,
    mut v_init_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2677_: u8 = 0;
    let mut v_res_2678_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2677_ = (lean_unbox(v_json_2672_) as u8);
    v_res_2678_ =
        l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(
            v_opts_2671_,
            v_json_boxed_2677_,
            v_severityOverrides_2673_,
            v_s_2674_,
            v_init_2675_,
        );
    lean_dec(v_severityOverrides_2673_);
    lean_dec_ref(v_opts_2671_);
    return v_res_2678_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_runAndReport(
    mut v_s_2679_: *mut LeanObject,
    mut v_opts_2680_: *mut LeanObject,
    mut v_json_2681_: u8,
    mut v_severityOverrides_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2690_: u8 = 0;
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = lean_unsigned_to_nat(0);
                v___x_2685_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_runAndReport_spec__0(v_opts_2680_, v_json_2681_, v_severityOverrides_2682_, v_s_2679_, v___x_2684_);
                if lean_obj_tag(v___x_2685_) == 0 {
                    v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
                    v_isSharedCheck_2695_ = (!lean_is_exclusive(v___x_2685_)) as u8;
                    if v_isSharedCheck_2695_ == 0 {
                        v___x_2688_ = v___x_2685_;
                        v_isShared_2689_ = v_isSharedCheck_2695_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2686_);
                        lean_dec(v___x_2685_);
                        v___x_2688_ = lean_box(0);
                        v_isShared_2689_ = v_isSharedCheck_2695_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2696_ = lean_ctor_get(v___x_2685_, 0);
                    v_isSharedCheck_2703_ = (!lean_is_exclusive(v___x_2685_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2698_ = v___x_2685_;
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2696_);
                        lean_dec(v___x_2685_);
                        v___x_2698_ = lean_box(0);
                        v_isShared_2699_ = v_isSharedCheck_2703_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2690_ = lean_nat_dec_lt(v___x_2684_, v_a_2686_);
                lean_dec(v_a_2686_);
                v___x_2691_ = lean_box((v___x_2690_) as usize);
                if v_isShared_2689_ == 0 {
                    lean_ctor_set(v___x_2688_, 0, v___x_2691_);
                    v___x_2693_ = v___x_2688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2693_;
            }
            3 => {
                if v_isShared_2699_ == 0 {
                    v___x_2701_ = v___x_2698_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Language_SnapshotTree_runAndReport___boxed(
    mut v_s_2704_: *mut LeanObject,
    mut v_opts_2705_: *mut LeanObject,
    mut v_json_2706_: *mut LeanObject,
    mut v_severityOverrides_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_json_boxed_2709_: u8 = 0;
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
    v_json_boxed_2709_ = (lean_unbox(v_json_2706_) as u8);
    v_res_2710_ = l_Lean_Language_SnapshotTree_runAndReport(
        v_s_2704_,
        v_opts_2705_,
        v_json_boxed_2709_,
        v_severityOverrides_2707_,
    );
    lean_dec(v_severityOverrides_2707_);
    lean_dec_ref(v_opts_2705_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(
    mut v_s_2711_: *mut LeanObject,
    mut v_init_2712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_element_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    v_element_2713_ = lean_ctor_get(v_s_2711_, 0);
    lean_inc_ref(v_element_2713_);
    v_children_2714_ = lean_ctor_get(v_s_2711_, 1);
    lean_inc_ref(v_children_2714_);
    lean_dec_ref(v_s_2711_);
    v___x_2715_ = lean_array_push(v_init_2712_, v_element_2713_);
    v___x_2716_ = lean_unsigned_to_nat(0);
    v___x_2717_ = lean_array_get_size(v_children_2714_);
    v___x_2718_ = lean_nat_dec_lt(v___x_2716_, v___x_2717_);
    if v___x_2718_ == 0 {
        lean_dec_ref(v_children_2714_);
        return v___x_2715_;
    } else {
        let mut v___x_2719_: u8 = 0;
        v___x_2719_ = lean_nat_dec_le(v___x_2717_, v___x_2717_);
        if v___x_2719_ == 0 {
            if v___x_2718_ == 0 {
                lean_dec_ref(v_children_2714_);
                return v___x_2715_;
            } else {
                let mut v___x_2720_: usize = 0;
                let mut v___x_2721_: usize = 0;
                let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
                v___x_2720_ = 0usize;
                v___x_2721_ = lean_usize_of_nat(v___x_2717_);
                v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_2714_, v___x_2720_, v___x_2721_, v___x_2715_);
                lean_dec_ref(v_children_2714_);
                return v___x_2722_;
            }
        } else {
            let mut v___x_2723_: usize = 0;
            let mut v___x_2724_: usize = 0;
            let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
            v___x_2723_ = 0usize;
            v___x_2724_ = lean_usize_of_nat(v___x_2717_);
            v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_children_2714_, v___x_2723_, v___x_2724_, v___x_2715_);
            lean_dec_ref(v_children_2714_);
            return v___x_2725_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(
    mut v_as_2726_: *mut LeanObject,
    mut v_i_2727_: usize,
    mut v_stop_2728_: usize,
    mut v_b_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: usize = 0;
    let mut v___x_2735_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2730_ = lean_usize_dec_eq(v_i_2727_, v_stop_2728_);
                if v___x_2730_ == 0 {
                    v___x_2731_ = lean_array_uget_borrowed(v_as_2726_, v_i_2727_);
                    lean_inc(v___x_2731_);
                    v___x_2732_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2731_);
                    v___x_2733_ = l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(v___x_2732_, v_b_2729_);
                    v___x_2734_ = 1usize;
                    v___x_2735_ = lean_usize_add(v_i_2727_, v___x_2734_);
                    v_i_2727_ = v___x_2735_;
                    v_b_2729_ = v___x_2733_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2729_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(
    mut v_as_2737_: *mut LeanObject,
    mut v_i_2738_: *mut LeanObject,
    mut v_stop_2739_: *mut LeanObject,
    mut v_b_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2741_: usize = 0;
    let mut v_stop_boxed_2742_: usize = 0;
    let mut v_res_2743_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2741_ = lean_unbox_usize(v_i_2738_);
    lean_dec(v_i_2738_);
    v_stop_boxed_2742_ = lean_unbox_usize(v_stop_2739_);
    lean_dec(v_stop_2739_);
    v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0_spec__0(v_as_2737_, v_i_boxed_2741_, v_stop_boxed_2742_, v_b_2740_);
    lean_dec_ref(v_as_2737_);
    return v_res_2743_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_getAll(
    mut v_s_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    v___x_2747_ = l_Lean_Language_SnapshotTree_getAll___closed__0;
    v___x_2748_ =
        l_Lean_Language_SnapshotTree_foldM___at___00Lean_Language_SnapshotTree_getAll_spec__0(
            v_s_2746_,
            v___x_2747_,
        );
    return v___x_2748_;
}
pub unsafe fn _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0()
-> *mut LeanObject {
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    v___x_2749_ = lean_box(0);
    v___x_2750_ = lean_task_pure(v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(
    mut v_tail_2751_: *mut LeanObject,
    mut v_t_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(
        v_tail_2751_,
        v_t_2752_,
    );
    return v_res_2754_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(
    mut v_a_2755_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_2755_) == 0 {
        let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
        v___x_2757_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0_once), _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
        return v___x_2757_;
    } else {
        let mut v_head_2758_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2759_: *mut LeanObject = core::ptr::null_mut();
        let mut v_task_2760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2763_: u8 = 0;
        let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
        v_head_2758_ = lean_ctor_get(v_a_2755_, 0);
        lean_inc(v_head_2758_);
        v_tail_2759_ = lean_ctor_get(v_a_2755_, 1);
        lean_inc(v_tail_2759_);
        lean_dec_ref_known(v_a_2755_, 2);
        v_task_2760_ = lean_ctor_get(v_head_2758_, 3);
        lean_inc_ref(v_task_2760_);
        lean_dec(v_head_2758_);
        v___f_2761_ = lean_alloc_closure(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_2761_, 0, v_tail_2759_);
        v___x_2762_ = lean_unsigned_to_nat(0);
        v___x_2763_ = 1;
        v___x_2764_ = lean_io_bind_task(v_task_2760_, v___f_2761_, v___x_2762_, v___x_2763_);
        return v___x_2764_;
    }
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(
    mut v_tail_2765_: *mut LeanObject,
    mut v_t_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_children_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v_children_2768_ = lean_ctor_get(v_t_2766_, 1);
    lean_inc_ref(v_children_2768_);
    lean_dec_ref(v_t_2766_);
    v___x_2769_ = lean_array_to_list(v_children_2768_);
    v___x_2770_ = l_List_appendTR___redArg(v___x_2769_, v_tail_2765_);
    v___x_2771_ =
        l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___boxed(
    mut v_a_2772_: *mut LeanObject,
    mut v_a_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ =
        l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v_a_2772_);
    return v_res_2774_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_waitAll(
    mut v_x_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_children_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v_children_2777_ = lean_ctor_get(v_x_2775_, 1);
    lean_inc_ref(v_children_2777_);
    lean_dec_ref(v_x_2775_);
    v___x_2778_ = lean_array_to_list(v_children_2777_);
    v___x_2779_ =
        l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(v___x_2778_);
    return v___x_2779_;
}
pub unsafe fn l_Lean_Language_SnapshotTree_waitAll___boxed(
    mut v_x_2780_: *mut LeanObject,
    mut v_a_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2782_: *mut LeanObject = core::ptr::null_mut();
    v_res_2782_ = l_Lean_Language_SnapshotTree_waitAll(v_x_2780_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(
    mut v_00_u03b1_2783_: *mut LeanObject,
    mut v_act_2784_: *mut LeanObject,
    mut v_ctx_2785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = lean_apply_2(v_act_2784_, v_ctx_2785_, lean_box(0));
    v___x_2788_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2788_, 0, v___x_2787_);
    return v___x_2788_;
}
pub unsafe fn l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0___boxed(
    mut v_00_u03b1_2789_: *mut LeanObject,
    mut v_act_2790_: *mut LeanObject,
    mut v_ctx_2791_: *mut LeanObject,
    mut v___y_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2793_: *mut LeanObject = core::ptr::null_mut();
    v_res_2793_ = l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(
        v_00_u03b1_2789_,
        v_act_2790_,
        v_ctx_2791_,
    );
    return v_res_2793_;
}
pub unsafe fn l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(
    mut v_msgLog_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    v___x_2798_ = lean_box(0);
    v___x_2799_ = lean_st_mk_ref(v___x_2798_);
    v___x_2800_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2800_, 0, v___x_2799_);
    v___x_2801_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2801_, 0, v_msgLog_2796_);
    lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    return v___x_2801_;
}
pub unsafe fn l_Lean_Language_Snapshot_Diagnostics_ofMessageLog___boxed(
    mut v_msgLog_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2804_: *mut LeanObject = core::ptr::null_mut();
    v_res_2804_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_2802_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_Language_diagnosticsOfHeaderError(
    mut v_msg_2809_: *mut LeanObject,
    mut v_a_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileMap_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    v_fileMap_2812_ = lean_ctor_get(v_a_2810_, 2);
    v_source_2813_ = lean_ctor_get(v_fileMap_2812_, 0);
    v___x_2814_ = l_Lean_Language_diagnosticsOfHeaderError___closed__0;
    v___x_2815_ = l_Lean_Language_diagnosticsOfHeaderError___closed__1;
    v___x_2816_ = lean_string_utf8_byte_size(v_source_2813_);
    lean_inc_ref(v_fileMap_2812_);
    v___x_2817_ = l_Lean_FileMap_toPosition(v_fileMap_2812_, v___x_2816_);
    v___x_2818_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2818_, 0, v___x_2817_);
    v___x_2819_ = 0;
    v___x_2820_ = 2;
    v___x_2821_ = l_Lean_Language_instInhabitedSnapshot___closed__0;
    v___x_2822_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2822_, 0, v_msg_2809_);
    v___x_2823_ = l_Lean_MessageData_ofFormat(v___x_2822_);
    v___x_2824_ = lean_alloc_ctor(0, 5, (3) as u32);
    lean_ctor_set(v___x_2824_, 0, v___x_2814_);
    lean_ctor_set(v___x_2824_, 1, v___x_2815_);
    lean_ctor_set(v___x_2824_, 2, v___x_2818_);
    lean_ctor_set(v___x_2824_, 3, v___x_2821_);
    lean_ctor_set(v___x_2824_, 4, v___x_2823_);
    lean_ctor_set_uint8(
        v___x_2824_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_2819_,
    );
    lean_ctor_set_uint8(
        v___x_2824_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_2820_,
    );
    lean_ctor_set_uint8(
        v___x_2824_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
        v___x_2819_,
    );
    v___x_2825_ = l_Lean_MessageLog_empty;
    v___x_2826_ = l_Lean_MessageLog_add(v___x_2824_, v___x_2825_);
    v___x_2827_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_2826_);
    return v___x_2827_;
}
pub unsafe fn l_Lean_Language_diagnosticsOfHeaderError___boxed(
    mut v_msg_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_Language_diagnosticsOfHeaderError(v_msg_2828_, v_a_2829_);
    lean_dec_ref(v_a_2829_);
    return v_res_2831_;
}
pub unsafe fn _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    v___x_2837_ = 1;
    v___x_2838_ = l_Lean_Language_withHeaderExceptions___redArg___closed__1;
    v___x_2839_ = l_Lean_Name_toString(v___x_2838_, v___x_2837_);
    return v___x_2839_;
}
pub unsafe fn l_Lean_Language_withHeaderExceptions___redArg(
    mut v_ex_2840_: *mut LeanObject,
    mut v_act_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2842_);
    v___x_2844_ = lean_apply_2(v_act_2841_, v_a_2842_, lean_box(0));
    if lean_obj_tag(v___x_2844_) == 0 {
        let mut v_a_2845_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ex_2840_);
        v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
        lean_inc(v_a_2845_);
        lean_dec_ref_known(v___x_2844_, 1);
        return v_a_2845_;
    } else {
        let mut v_a_2846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2852_: u8 = 0;
        let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
        v_a_2846_ = lean_ctor_get(v___x_2844_, 0);
        lean_inc(v_a_2846_);
        lean_dec_ref_known(v___x_2844_, 1);
        v___x_2847_ = lean_io_error_to_string(v_a_2846_);
        v___x_2848_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_2847_, v_a_2842_);
        v___x_2849_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Language_withHeaderExceptions___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Language_withHeaderExceptions___redArg___closed__2_once),
            _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2,
        );
        v___x_2850_ = lean_box(0);
        v___x_2851_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Language_instInhabitedSnapshot___closed__3_once),
            _init_l_Lean_Language_instInhabitedSnapshot___closed__3,
        );
        v___x_2852_ = 0;
        v___x_2853_ = lean_alloc_ctor(0, 4, (1) as u32);
        lean_ctor_set(v___x_2853_, 0, v___x_2849_);
        lean_ctor_set(v___x_2853_, 1, v___x_2848_);
        lean_ctor_set(v___x_2853_, 2, v___x_2850_);
        lean_ctor_set(v___x_2853_, 3, v___x_2851_);
        lean_ctor_set_uint8(
            v___x_2853_,
            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
            v___x_2852_,
        );
        v___x_2854_ = lean_apply_1(v_ex_2840_, v___x_2853_);
        return v___x_2854_;
    }
}
pub unsafe fn l_Lean_Language_withHeaderExceptions___redArg___boxed(
    mut v_ex_2855_: *mut LeanObject,
    mut v_act_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2859_: *mut LeanObject = core::ptr::null_mut();
    v_res_2859_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_2855_, v_act_2856_, v_a_2857_);
    lean_dec_ref(v_a_2857_);
    return v_res_2859_;
}
pub unsafe fn l_Lean_Language_withHeaderExceptions(
    mut v_00_u03b1_2860_: *mut LeanObject,
    mut v_ex_2861_: *mut LeanObject,
    mut v_act_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Lean_Language_withHeaderExceptions___redArg(v_ex_2861_, v_act_2862_, v_a_2863_);
    return v___x_2865_;
}
pub unsafe fn l_Lean_Language_withHeaderExceptions___boxed(
    mut v_00_u03b1_2866_: *mut LeanObject,
    mut v_ex_2867_: *mut LeanObject,
    mut v_act_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v_res_2871_ =
        l_Lean_Language_withHeaderExceptions(v_00_u03b1_2866_, v_ex_2867_, v_act_2868_, v_a_2869_);
    lean_dec_ref(v_a_2869_);
    return v_res_2871_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(
    mut v_val_2872_: *mut LeanObject,
    mut v_process_2873_: *mut LeanObject,
    mut v_ictx_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2876_ = lean_st_ref_get(v_val_2872_);
    v___x_2877_ = lean_apply_3(v_process_2873_, v___x_2876_, v_ictx_2874_, lean_box(0));
    lean_inc(v___x_2877_);
    v___x_2878_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2878_, 0, v___x_2877_);
    v___x_2879_ = lean_st_ref_set(v_val_2872_, v___x_2878_);
    return v___x_2877_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(
    mut v_val_2880_: *mut LeanObject,
    mut v_process_2881_: *mut LeanObject,
    mut v_ictx_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2884_: *mut LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(
        v_val_2880_,
        v_process_2881_,
        v_ictx_2882_,
    );
    lean_dec(v_val_2880_);
    return v_res_2884_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor___redArg(
    mut v_process_2885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2887_ = lean_box(0);
    v___x_2888_ = lean_st_mk_ref(v___x_2887_);
    v___f_2889_ = lean_alloc_closure(
        l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2889_, 0, v___x_2888_);
    lean_closure_set(v___f_2889_, 1, v_process_2885_);
    return v___f_2889_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor___redArg___boxed(
    mut v_process_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2892_: *mut LeanObject = core::ptr::null_mut();
    v_res_2892_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_2890_);
    return v_res_2892_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor(
    mut v_InitSnap_2893_: *mut LeanObject,
    mut v_process_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Language_mkIncrementalProcessor___redArg(v_process_2894_);
    return v___x_2896_;
}
pub unsafe fn l_Lean_Language_mkIncrementalProcessor___boxed(
    mut v_InitSnap_2897_: *mut LeanObject,
    mut v_process_2898_: *mut LeanObject,
    mut v_a_2899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2900_: *mut LeanObject = core::ptr::null_mut();
    v_res_2900_ = l_Lean_Language_mkIncrementalProcessor(v_InitSnap_2897_, v_process_2898_);
    return v_res_2900_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Language_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Language_Snapshot_instInhabitedDiagnostics_default =
        _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default();
    lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics_default);
    l_Lean_Language_Snapshot_instInhabitedDiagnostics =
        _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics();
    lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics);
    l_Lean_Language_Snapshot_Diagnostics_empty = _init_l_Lean_Language_Snapshot_Diagnostics_empty();
    lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty);
    l_Lean_Language_instInhabitedSnapshot = _init_l_Lean_Language_instInhabitedSnapshot();
    lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot);
    l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default =
        _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default();
    lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default);
    l_Lean_Language_SnapshotTask_instInhabitedReportingRange =
        _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange();
    lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange);
    l_Lean_Language_instInhabitedSnapshotTree_default =
        _init_l_Lean_Language_instInhabitedSnapshotTree_default();
    lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree_default);
    l_Lean_Language_instInhabitedSnapshotTree = _init_l_Lean_Language_instInhabitedSnapshotTree();
    lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree);
    l_Lean_Language_instInhabitedSnapshotLeaf = _init_l_Lean_Language_instInhabitedSnapshotLeaf();
    lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf);
    l_Lean_Language_instInhabitedDynamicSnapshot =
        _init_l_Lean_Language_instInhabitedDynamicSnapshot();
    lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot);
    res = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Language_printMessageEndPos);
    lean_dec_ref(res);
    res = l___private_Lean_Language_Basic_0__Lean_Language_initFn_00___x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Language_maxErrors = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Language_maxErrors);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Language_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Language_Snapshot_desc___autoParam = _init_l_Lean_Language_Snapshot_desc___autoParam();
    lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Language_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Language_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Language_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Language_Basic(builtin);
}
