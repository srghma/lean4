// Lean compiler output
// Module: Std.Time.Zoned.Database.TZdb
// Imports: Std.Time.Zoned.Database.Basic Init.Data.String.TakeDrop
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::System::FilePath::{l_System_FilePath_components, l_System_FilePath_join};
use crate::r#gen::Init::System::IO::{l_IO_FS_readBinFile, l_System_FilePath_pathExists};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Std::Internal::Parsec::ByteArray::l_Std_Internal_Parsec_ByteArray_Parser_run___redArg;
use crate::r#gen::Std::Time::Zoned::Database::Basic::{
    initialize_Std_Time_Zoned_Database_Basic, l_Std_Time_TimeZone_convertTZif,
    runtime_initialize_Std_Time_Zoned_Database_Basic,
};
use crate::r#gen::Std::Time::Zoned::Database::TzIf::l_Std_Time_TimeZone_TZif_parse;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_getenv, lean_io_realpath};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Std_Time_Database_TZdb_parseTZif___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_parse as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_TZdb_parseTZif___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_parseTZif___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            117, 110, 97, 98, 108, 101, 32, 116, 111, 32, 108, 111, 99, 97, 116, 101, 32, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            32, 105, 110, 32, 116, 104, 101, 32, 108, 111, 99, 97, 108, 32, 116, 105, 109, 101,
            122, 111, 110, 101, 32, 100, 97, 116, 97, 98, 97, 115, 101, 32, 97, 116, 32, 39, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value: LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_idFromPath___closed__0_value: LeanStringObject<9> =
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
        m_data: [122, 111, 110, 101, 105, 110, 102, 111, 0],
    };
static mut l_Std_Time_Database_TZdb_idFromPath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_idFromPath___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_idFromPath___closed__1_value: LeanStringObject<2> =
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
        m_data: [47, 0],
    };
static mut l_Std_Time_Database_TZdb_idFromPath___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_idFromPath___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_localRules___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
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
            99, 97, 110, 110, 111, 116, 32, 114, 101, 97, 100, 32, 116, 104, 101, 32, 105, 100, 32,
            111, 102, 32, 116, 104, 101, 32, 112, 97, 116, 104, 46, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_localRules___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_localRules___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Database_TZdb_localRules___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_TZdb_localRules___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 90,
            100, 98, 46, 84, 90, 83, 112, 101, 99, 46, 102, 105, 108, 101, 80, 97, 116, 104, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2_value)
        as *mut LeanObject;
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 90,
            100, 98, 46, 84, 90, 83, 112, 101, 99, 46, 122, 111, 110, 101, 73, 100, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__6_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_TZdb_instReprTZSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Database_TZdb_instReprTZSpec: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instReprTZSpec___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Database_TZdb_instBEqTZSpec: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_instBEqTZSpec___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_parseTZValue___closed__0_value: LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Std_Time_Database_TZdb_parseTZValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_parseTZValue___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Database_TZdb_parseTZValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_TZdb_parseTZValue___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [84, 90, 0],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__1_value: LeanStringObject<5> =
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
        m_data: [84, 90, 61, 39, 0],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__2_value: LeanStringObject<10> =
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
        m_data: [39, 58, 32, 112, 97, 116, 104, 32, 39, 0],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__3_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 97, 110, 121, 32,
            122, 111, 110, 101, 105, 110, 102, 111, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121,
            0,
        ],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            39, 58, 32, 116, 105, 109, 101, 122, 111, 110, 101, 32, 110, 111, 116, 32, 102, 111,
            117, 110, 100, 32, 105, 110, 32, 97, 110, 121, 32, 122, 111, 110, 101, 105, 110, 102,
            111, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveLocalPath___closed__6_value: LeanStringObject<15> =
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
            47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_resolveLocalPath___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_default___closed__0_value: LeanStringObject<20> =
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
            47, 117, 115, 114, 47, 115, 104, 97, 114, 101, 47, 122, 111, 110, 101, 105, 110, 102,
            111, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_default___closed__1_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            47, 115, 104, 97, 114, 101, 47, 122, 111, 110, 101, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_default___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            47, 101, 116, 99, 47, 122, 111, 110, 101, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_default___closed__3_value: LeanStringObject<24> =
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
            47, 117, 115, 114, 47, 115, 104, 97, 114, 101, 47, 108, 105, 98, 47, 122, 111, 110,
            101, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_default___closed__4_value: LeanArrayObject<4> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_TZdb_default___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__4_value) as *mut LeanObject;
pub static mut l_Std_Time_Database_TZdb_default: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_default___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0_value: LeanStringObject<6> =
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
        m_data: [84, 90, 68, 73, 82, 0],
    };
static mut l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1_value: LeanStringObject<1> =
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
static mut l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_getZoneRules___closed__0_value: LeanStringObject<13> =
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
        m_data: [99, 97, 110, 110, 111, 116, 32, 102, 105, 110, 100, 32, 0],
    };
static mut l_Std_Time_Database_TZdb_getZoneRules___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_getZoneRules___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_getZoneRules___closed__1_value: LeanStringObject<32> =
    LeanStringObject {
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
            32, 105, 110, 32, 116, 104, 101, 32, 108, 111, 99, 97, 108, 32, 116, 105, 109, 101,
            122, 111, 110, 101, 32, 100, 97, 116, 97, 98, 97, 115, 101, 0,
        ],
    };
static mut l_Std_Time_Database_TZdb_getZoneRules___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_getZoneRules___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_inst___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Database_TZdb_getZoneRules___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_TZdb_inst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_inst___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Database_TZdb_getLocalZoneRules___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_TZdb_inst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Database_TZdb_inst___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_Database_TZdb_inst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__2_value) as *mut LeanObject;
pub static mut l_Std_Time_Database_TZdb_inst: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_TZdb_inst___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Std_Time_Database_TZdb_parseTZif(
    mut v_bin_642_: *mut LeanObject,
    mut v_id_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut v_a_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = l_Std_Time_Database_TZdb_parseTZif___closed__0;
                v___x_645_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_644_, v_bin_642_);
                if lean_obj_tag(v___x_645_) == 0 {
                    lean_dec_ref(v_id_643_);
                    v_a_646_ = lean_ctor_get(v___x_645_, 0);
                    v_isSharedCheck_653_ = (!lean_is_exclusive(v___x_645_)) as u8;
                    if v_isSharedCheck_653_ == 0 {
                        v___x_648_ = v___x_645_;
                        v_isShared_649_ = v_isSharedCheck_653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_646_);
                        lean_dec(v___x_645_);
                        v___x_648_ = lean_box(0);
                        v_isShared_649_ = v_isSharedCheck_653_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_654_ = lean_ctor_get(v___x_645_, 0);
                    lean_inc(v_a_654_);
                    lean_dec_ref_known(v___x_645_, 1);
                    v___x_655_ = l_Std_Time_TimeZone_convertTZif(v_a_654_, v_id_643_);
                    lean_dec(v_a_654_);
                    return v___x_655_;
                }
            }
            1 => {
                if v_isShared_649_ == 0 {
                    v___x_651_ = v___x_648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
                    v___x_651_ = v_reuseFailAlloc_652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(
    mut v_e_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_a_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_656_) == 0 {
                    v_a_658_ = lean_ctor_get(v_e_656_, 0);
                    v_isSharedCheck_666_ = (!lean_is_exclusive(v_e_656_)) as u8;
                    if v_isSharedCheck_666_ == 0 {
                        v___x_660_ = v_e_656_;
                        v_isShared_661_ = v_isSharedCheck_666_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_658_);
                        lean_dec(v_e_656_);
                        v___x_660_ = lean_box(0);
                        v_isShared_661_ = v_isSharedCheck_666_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_667_ = lean_ctor_get(v_e_656_, 0);
                    v_isSharedCheck_674_ = (!lean_is_exclusive(v_e_656_)) as u8;
                    if v_isSharedCheck_674_ == 0 {
                        v___x_669_ = v_e_656_;
                        v_isShared_670_ = v_isSharedCheck_674_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_667_);
                        lean_dec(v_e_656_);
                        v___x_669_ = lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_674_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_662_ = lean_mk_io_user_error(v_a_658_);
                if v_isShared_661_ == 0 {
                    lean_ctor_set_tag(v___x_660_, 1);
                    lean_ctor_set(v___x_660_, 0, v___x_662_);
                    v___x_664_ = v___x_660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
                    v___x_664_ = v_reuseFailAlloc_665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_664_;
            }
            3 => {
                if v_isShared_670_ == 0 {
                    lean_ctor_set_tag(v___x_669_, 0);
                    v___x_672_ = v___x_669_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
                    v___x_672_ = v_reuseFailAlloc_673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg___boxed(
    mut v_e_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_677_: *mut LeanObject = core::ptr::null_mut();
    v_res_677_ =
        l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_675_);
    return v_res_677_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(
    mut v_00_u03b1_678_: *mut LeanObject,
    mut v_e_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v___x_681_ =
        l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v_e_679_);
    return v___x_681_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___boxed(
    mut v_00_u03b1_682_: *mut LeanObject,
    mut v_e_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_685_: *mut LeanObject = core::ptr::null_mut();
    v_res_685_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0(
        v_00_u03b1_682_,
        v_e_683_,
    );
    return v_res_685_;
}
pub unsafe fn l_Std_Time_Database_TZdb_parseTZIfFromDisk(
    mut v_path_689_: *mut LeanObject,
    mut v_id_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_699_: u8 = 0;
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_706_: u8 = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_unused_719_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_692_ = l_IO_FS_readBinFile(v_path_689_);
                if lean_obj_tag(v___x_692_) == 0 {
                    if lean_obj_tag(v___x_692_) == 0 {
                        v_a_693_ = lean_ctor_get(v___x_692_, 0);
                        lean_inc(v_a_693_);
                        lean_dec_ref_known(v___x_692_, 1);
                        v___x_694_ = l_Std_Time_Database_TZdb_parseTZif(v_a_693_, v_id_690_);
                        v___x_695_ = l_IO_ofExcept___at___00Std_Time_Database_TZdb_parseTZIfFromDisk_spec__0___redArg(v___x_694_);
                        return v___x_695_;
                    } else {
                        lean_dec_ref(v_id_690_);
                        v_a_696_ = lean_ctor_get(v___x_692_, 0);
                        v_isSharedCheck_703_ = (!lean_is_exclusive(v___x_692_)) as u8;
                        if v_isSharedCheck_703_ == 0 {
                            v___x_698_ = v___x_692_;
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_696_);
                            lean_dec(v___x_692_);
                            v___x_698_ = lean_box(0);
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_isSharedCheck_718_ = (!lean_is_exclusive(v___x_692_)) as u8;
                    if v_isSharedCheck_718_ == 0 {
                        v_unused_719_ = lean_ctor_get(v___x_692_, 0);
                        lean_dec(v_unused_719_);
                        v___x_705_ = v___x_692_;
                        v_isShared_706_ = v_isSharedCheck_718_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_692_);
                        v___x_705_ = lean_box(0);
                        v_isShared_706_ = v_isSharedCheck_718_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_699_ == 0 {
                    lean_ctor_set_tag(v___x_698_, 1);
                    v___x_701_ = v___x_698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
                    v___x_701_ = v_reuseFailAlloc_702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_701_;
            }
            3 => {
                v___x_707_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__0;
                v___x_708_ = lean_string_append(v___x_707_, v_id_690_);
                lean_dec_ref(v_id_690_);
                v___x_709_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__1;
                v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
                v___x_711_ = lean_string_append(v___x_710_, v_path_689_);
                v___x_712_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk___closed__2;
                v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
                v___x_714_ = lean_mk_io_user_error(v___x_713_);
                if v_isShared_706_ == 0 {
                    lean_ctor_set(v___x_705_, 0, v___x_714_);
                    v___x_716_ = v___x_705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                    v___x_716_ = v_reuseFailAlloc_717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_parseTZIfFromDisk___boxed(
    mut v_path_720_: *mut LeanObject,
    mut v_id_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_723_: *mut LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_720_, v_id_721_);
    lean_dec_ref(v_path_720_);
    return v_res_723_;
}
pub unsafe fn l_Std_Time_Database_TZdb_idFromPath(
    mut v_path_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: u8 = 0;
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_727_ = l_System_FilePath_components(v_path_726_);
                v_res_728_ = lean_array_mk(v___x_727_);
                v___x_729_ = lean_array_get_size(v_res_728_);
                v___x_730_ = lean_unsigned_to_nat(1);
                v___x_731_ = lean_nat_sub(v___x_729_, v___x_730_);
                v___x_732_ = lean_nat_dec_lt(v___x_731_, v___x_729_);
                if v___x_732_ == 0 {
                    lean_dec(v___x_731_);
                    lean_dec_ref(v_res_728_);
                    v___x_733_ = lean_box(0);
                    return v___x_733_;
                } else {
                    v___x_734_ = lean_unsigned_to_nat(2);
                    v___x_735_ = lean_nat_sub(v___x_729_, v___x_734_);
                    v___x_736_ = lean_nat_dec_lt(v___x_735_, v___x_729_);
                    if v___x_736_ == 0 {
                        lean_dec(v___x_735_);
                        lean_dec(v___x_731_);
                        lean_dec_ref(v_res_728_);
                        v___x_737_ = lean_box(0);
                        return v___x_737_;
                    } else {
                        v___x_738_ = lean_array_fget(v_res_728_, v___x_731_);
                        lean_dec(v___x_731_);
                        v___x_739_ = lean_array_fget(v_res_728_, v___x_735_);
                        lean_dec(v___x_735_);
                        lean_dec_ref(v_res_728_);
                        v___x_740_ = l_Std_Time_Database_TZdb_idFromPath___closed__0;
                        v___x_741_ = lean_string_dec_eq(v___x_739_, v___x_740_);
                        if v___x_741_ == 0 {
                            v___x_742_ = lean_unsigned_to_nat(0);
                            v___x_743_ = lean_string_utf8_byte_size(v___x_739_);
                            v___x_744_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_744_, 0, v___x_739_);
                            lean_ctor_set(v___x_744_, 1, v___x_742_);
                            lean_ctor_set(v___x_744_, 2, v___x_743_);
                            v___x_745_ = l_String_Slice_trimAscii(v___x_744_);
                            v_str_746_ = lean_ctor_get(v___x_745_, 0);
                            v_startInclusive_747_ = lean_ctor_get(v___x_745_, 1);
                            v_endExclusive_748_ = lean_ctor_get(v___x_745_, 2);
                            v_isSharedCheck_766_ = (!lean_is_exclusive(v___x_745_)) as u8;
                            if v_isSharedCheck_766_ == 0 {
                                v___x_750_ = v___x_745_;
                                v_isShared_751_ = v_isSharedCheck_766_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_endExclusive_748_);
                                lean_inc(v_startInclusive_747_);
                                lean_inc(v_str_746_);
                                lean_dec(v___x_745_);
                                v___x_750_ = lean_box(0);
                                v_isShared_751_ = v_isSharedCheck_766_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_739_);
                            v___x_767_ = lean_unsigned_to_nat(0);
                            v___x_768_ = lean_string_utf8_byte_size(v___x_738_);
                            v___x_769_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_769_, 0, v___x_738_);
                            lean_ctor_set(v___x_769_, 1, v___x_767_);
                            lean_ctor_set(v___x_769_, 2, v___x_768_);
                            v___x_770_ = l_String_Slice_trimAscii(v___x_769_);
                            v_str_771_ = lean_ctor_get(v___x_770_, 0);
                            lean_inc_ref(v_str_771_);
                            v_startInclusive_772_ = lean_ctor_get(v___x_770_, 1);
                            lean_inc(v_startInclusive_772_);
                            v_endExclusive_773_ = lean_ctor_get(v___x_770_, 2);
                            lean_inc(v_endExclusive_773_);
                            lean_dec_ref(v___x_770_);
                            v___x_774_ = lean_string_utf8_extract(
                                v_str_771_,
                                v_startInclusive_772_,
                                v_endExclusive_773_,
                            );
                            lean_dec(v_endExclusive_773_);
                            lean_dec(v_startInclusive_772_);
                            lean_dec_ref(v_str_771_);
                            v___x_775_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_775_, 0, v___x_774_);
                            return v___x_775_;
                        }
                    }
                }
            }
            1 => {
                v___x_752_ = lean_string_utf8_byte_size(v___x_738_);
                if v_isShared_751_ == 0 {
                    lean_ctor_set(v___x_750_, 2, v___x_752_);
                    lean_ctor_set(v___x_750_, 1, v___x_742_);
                    lean_ctor_set(v___x_750_, 0, v___x_738_);
                    v___x_754_ = v___x_750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_738_);
                    lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_742_);
                    lean_ctor_set(v_reuseFailAlloc_765_, 2, v___x_752_);
                    v___x_754_ = v_reuseFailAlloc_765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_755_ = l_String_Slice_trimAscii(v___x_754_);
                v_str_756_ = lean_ctor_get(v___x_755_, 0);
                lean_inc_ref(v_str_756_);
                v_startInclusive_757_ = lean_ctor_get(v___x_755_, 1);
                lean_inc(v_startInclusive_757_);
                v_endExclusive_758_ = lean_ctor_get(v___x_755_, 2);
                lean_inc(v_endExclusive_758_);
                lean_dec_ref(v___x_755_);
                v___x_759_ = lean_string_utf8_extract(
                    v_str_746_,
                    v_startInclusive_747_,
                    v_endExclusive_748_,
                );
                lean_dec(v_endExclusive_748_);
                lean_dec(v_startInclusive_747_);
                lean_dec_ref(v_str_746_);
                v___x_760_ = l_Std_Time_Database_TZdb_idFromPath___closed__1;
                v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
                v___x_762_ = lean_string_utf8_extract(
                    v_str_756_,
                    v_startInclusive_757_,
                    v_endExclusive_758_,
                );
                lean_dec(v_endExclusive_758_);
                lean_dec(v_startInclusive_757_);
                lean_dec_ref(v_str_756_);
                v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
                lean_dec_ref(v___x_762_);
                v___x_764_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_764_, 0, v___x_763_);
                return v___x_764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_Database_TZdb_localRules___closed__1() -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = l_Std_Time_Database_TZdb_localRules___closed__0;
    v___x_778_ = lean_mk_io_user_error(v___x_777_);
    return v___x_778_;
}
pub unsafe fn l_Std_Time_Database_TZdb_localRules(
    mut v_path_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_793_: u8 = 0;
    let mut v_a_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_797_: u8 = 0;
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_path_779_);
                v___x_781_ = lean_io_realpath(v_path_779_);
                if lean_obj_tag(v___x_781_) == 0 {
                    v_a_782_ = lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_793_ = (!lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_793_ == 0 {
                        v___x_784_ = v___x_781_;
                        v_isShared_785_ = v_isSharedCheck_793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_782_);
                        lean_dec(v___x_781_);
                        v___x_784_ = lean_box(0);
                        v_isShared_785_ = v_isSharedCheck_793_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_path_779_);
                    v_a_794_ = lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_801_ = (!lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_801_ == 0 {
                        v___x_796_ = v___x_781_;
                        v_isShared_797_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_794_);
                        lean_dec(v___x_781_);
                        v___x_796_ = lean_box(0);
                        v_isShared_797_ = v_isSharedCheck_801_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_786_ = l_Std_Time_Database_TZdb_idFromPath(v_a_782_);
                if lean_obj_tag(v___x_786_) == 1 {
                    lean_del_object(v___x_784_);
                    v_val_787_ = lean_ctor_get(v___x_786_, 0);
                    lean_inc(v_val_787_);
                    lean_dec_ref_known(v___x_786_, 1);
                    v___x_788_ =
                        l_Std_Time_Database_TZdb_parseTZIfFromDisk(v_path_779_, v_val_787_);
                    lean_dec_ref(v_path_779_);
                    return v___x_788_;
                } else {
                    lean_dec(v___x_786_);
                    lean_dec_ref(v_path_779_);
                    v___x_789_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_Database_TZdb_localRules___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_localRules___closed__1_once
                        ),
                        _init_l_Std_Time_Database_TZdb_localRules___closed__1,
                    );
                    if v_isShared_785_ == 0 {
                        lean_ctor_set_tag(v___x_784_, 1);
                        lean_ctor_set(v___x_784_, 0, v___x_789_);
                        v___x_791_ = v___x_784_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
                        v___x_791_ = v_reuseFailAlloc_792_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_791_;
            }
            3 => {
                if v_isShared_797_ == 0 {
                    v___x_799_ = v___x_796_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
                    v___x_799_ = v_reuseFailAlloc_800_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_localRules___boxed(
    mut v_path_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Std_Time_Database_TZdb_localRules(v_path_802_);
    return v_res_804_;
}
pub unsafe fn l_Std_Time_Database_TZdb_readRulesFromDisk(
    mut v_path_805_: *mut LeanObject,
    mut v_id_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_id_806_);
    v___x_808_ = l_System_FilePath_join(v_path_805_, v_id_806_);
    v___x_809_ = l_Std_Time_Database_TZdb_parseTZIfFromDisk(v___x_808_, v_id_806_);
    lean_dec_ref(v___x_808_);
    return v___x_809_;
}
pub unsafe fn l_Std_Time_Database_TZdb_readRulesFromDisk___boxed(
    mut v_path_810_: *mut LeanObject,
    mut v_id_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Std_Time_Database_TZdb_readRulesFromDisk(v_path_810_, v_id_811_);
    return v_res_813_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_ctorIdx(
    mut v_x_814_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_814_) == 0 {
        let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
        v___x_815_ = lean_unsigned_to_nat(0);
        return v___x_815_;
    } else {
        let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
        v___x_816_ = lean_unsigned_to_nat(1);
        return v___x_816_;
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_ctorIdx___boxed(
    mut v_x_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_818_: *mut LeanObject = core::ptr::null_mut();
    v_res_818_ = l_Std_Time_Database_TZdb_TZSpec_ctorIdx(v_x_817_);
    lean_dec_ref(v_x_817_);
    return v_res_818_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(
    mut v_t_819_: *mut LeanObject,
    mut v_k_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    v_p_821_ = lean_ctor_get(v_t_819_, 0);
    lean_inc_ref(v_p_821_);
    lean_dec_ref(v_t_819_);
    v___x_822_ = lean_apply_1(v_k_820_, v_p_821_);
    return v___x_822_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_ctorElim(
    mut v_motive_823_: *mut LeanObject,
    mut v_ctorIdx_824_: *mut LeanObject,
    mut v_t_825_: *mut LeanObject,
    mut v_h_826_: *mut LeanObject,
    mut v_k_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_825_, v_k_827_);
    return v___x_828_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_ctorElim___boxed(
    mut v_motive_829_: *mut LeanObject,
    mut v_ctorIdx_830_: *mut LeanObject,
    mut v_t_831_: *mut LeanObject,
    mut v_h_832_: *mut LeanObject,
    mut v_k_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_834_: *mut LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim(
        v_motive_829_,
        v_ctorIdx_830_,
        v_t_831_,
        v_h_832_,
        v_k_833_,
    );
    lean_dec(v_ctorIdx_830_);
    return v_res_834_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_filePath_elim___redArg(
    mut v_t_835_: *mut LeanObject,
    mut v_filePath_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_835_, v_filePath_836_);
    return v___x_837_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_filePath_elim(
    mut v_motive_838_: *mut LeanObject,
    mut v_t_839_: *mut LeanObject,
    mut v_h_840_: *mut LeanObject,
    mut v_filePath_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v___x_842_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_839_, v_filePath_841_);
    return v___x_842_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_zoneId_elim___redArg(
    mut v_t_843_: *mut LeanObject,
    mut v_zoneId_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_843_, v_zoneId_844_);
    return v___x_845_;
}
pub unsafe fn l_Std_Time_Database_TZdb_TZSpec_zoneId_elim(
    mut v_motive_846_: *mut LeanObject,
    mut v_t_847_: *mut LeanObject,
    mut v_h_848_: *mut LeanObject,
    mut v_zoneId_849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Std_Time_Database_TZdb_TZSpec_ctorElim___redArg(v_t_847_, v_zoneId_849_);
    return v___x_850_;
}
pub unsafe fn _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3() -> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = lean_unsigned_to_nat(2);
    v___x_858_ = lean_nat_to_int(v___x_857_);
    return v___x_858_;
}
pub unsafe fn _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4() -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = lean_unsigned_to_nat(1);
    v___x_860_ = lean_nat_to_int(v___x_859_);
    return v___x_860_;
}
pub unsafe fn l_Std_Time_Database_TZdb_instReprTZSpec_repr(
    mut v_x_867_: *mut LeanObject,
    mut v_prec_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___y_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_889_: u8 = 0;
    let mut v_id_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___y_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_867_) == 0 {
                    v_p_869_ = lean_ctor_get(v_x_867_, 0);
                    v_isSharedCheck_889_ = (!lean_is_exclusive(v_x_867_)) as u8;
                    if v_isSharedCheck_889_ == 0 {
                        v___x_871_ = v_x_867_;
                        v_isShared_872_ = v_isSharedCheck_889_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_869_);
                        lean_dec(v_x_867_);
                        v___x_871_ = lean_box(0);
                        v_isShared_872_ = v_isSharedCheck_889_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_id_890_ = lean_ctor_get(v_x_867_, 0);
                    v_isSharedCheck_910_ = (!lean_is_exclusive(v_x_867_)) as u8;
                    if v_isSharedCheck_910_ == 0 {
                        v___x_892_ = v_x_867_;
                        v_isShared_893_ = v_isSharedCheck_910_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_id_890_);
                        lean_dec(v_x_867_);
                        v___x_892_ = lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_910_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_885_ = lean_unsigned_to_nat(1024);
                v___x_886_ = lean_nat_dec_le(v___x_885_, v_prec_868_);
                if v___x_886_ == 0 {
                    v___x_887_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once
                        ),
                        _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3,
                    );
                    v___y_874_ = v___x_887_;
                    state = 2;
                    continue;
                } else {
                    v___x_888_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once
                        ),
                        _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4,
                    );
                    v___y_874_ = v___x_888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_875_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__2;
                v___x_876_ = l_String_quote(v_p_869_);
                if v_isShared_872_ == 0 {
                    lean_ctor_set_tag(v___x_871_, 3);
                    lean_ctor_set(v___x_871_, 0, v___x_876_);
                    v___x_878_ = v___x_871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_876_);
                    v___x_878_ = v_reuseFailAlloc_884_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_879_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_879_, 0, v___x_875_);
                lean_ctor_set(v___x_879_, 1, v___x_878_);
                lean_inc(v___y_874_);
                v___x_880_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_880_, 0, v___y_874_);
                lean_ctor_set(v___x_880_, 1, v___x_879_);
                v___x_881_ = 0;
                v___x_882_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_882_, 0, v___x_880_);
                lean_ctor_set_uint8(
                    v___x_882_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_881_,
                );
                v___x_883_ = l_Repr_addAppParen(v___x_882_, v_prec_868_);
                return v___x_883_;
            }
            4 => {
                v___x_906_ = lean_unsigned_to_nat(1024);
                v___x_907_ = lean_nat_dec_le(v___x_906_, v_prec_868_);
                if v___x_907_ == 0 {
                    v___x_908_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3_once
                        ),
                        _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__3,
                    );
                    v___y_895_ = v___x_908_;
                    state = 5;
                    continue;
                } else {
                    v___x_909_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4_once
                        ),
                        _init_l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__4,
                    );
                    v___y_895_ = v___x_909_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_896_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr___closed__7;
                v___x_897_ = l_String_quote(v_id_890_);
                if v_isShared_893_ == 0 {
                    lean_ctor_set_tag(v___x_892_, 3);
                    lean_ctor_set(v___x_892_, 0, v___x_897_);
                    v___x_899_ = v___x_892_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_905_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_897_);
                    v___x_899_ = v_reuseFailAlloc_905_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_900_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_900_, 0, v___x_896_);
                lean_ctor_set(v___x_900_, 1, v___x_899_);
                lean_inc(v___y_895_);
                v___x_901_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_901_, 0, v___y_895_);
                lean_ctor_set(v___x_901_, 1, v___x_900_);
                v___x_902_ = 0;
                v___x_903_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_903_, 0, v___x_901_);
                lean_ctor_set_uint8(
                    v___x_903_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_902_,
                );
                v___x_904_ = l_Repr_addAppParen(v___x_903_, v_prec_868_);
                return v___x_904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_instReprTZSpec_repr___boxed(
    mut v_x_911_: *mut LeanObject,
    mut v_prec_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_913_: *mut LeanObject = core::ptr::null_mut();
    v_res_913_ = l_Std_Time_Database_TZdb_instReprTZSpec_repr(v_x_911_, v_prec_912_);
    lean_dec(v_prec_912_);
    return v_res_913_;
}
pub unsafe fn l_Std_Time_Database_TZdb_instBEqTZSpec_beq(
    mut v_x_916_: *mut LeanObject,
    mut v_x_917_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_916_) == 0 {
        if lean_obj_tag(v_x_917_) == 0 {
            let mut v_p_918_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_919_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_920_: u8 = 0;
            v_p_918_ = lean_ctor_get(v_x_916_, 0);
            v_p_919_ = lean_ctor_get(v_x_917_, 0);
            v___x_920_ = lean_string_dec_eq(v_p_918_, v_p_919_);
            return v___x_920_;
        } else {
            let mut v___x_921_: u8 = 0;
            v___x_921_ = 0;
            return v___x_921_;
        }
    } else {
        if lean_obj_tag(v_x_917_) == 1 {
            let mut v_id_922_: *mut LeanObject = core::ptr::null_mut();
            let mut v_id_923_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_924_: u8 = 0;
            v_id_922_ = lean_ctor_get(v_x_916_, 0);
            v_id_923_ = lean_ctor_get(v_x_917_, 0);
            v___x_924_ = lean_string_dec_eq(v_id_922_, v_id_923_);
            return v___x_924_;
        } else {
            let mut v___x_925_: u8 = 0;
            v___x_925_ = 0;
            return v___x_925_;
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_instBEqTZSpec_beq___boxed(
    mut v_x_926_: *mut LeanObject,
    mut v_x_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_928_: u8 = 0;
    let mut v_r_929_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Std_Time_Database_TZdb_instBEqTZSpec_beq(v_x_926_, v_x_927_);
    lean_dec_ref(v_x_927_);
    lean_dec_ref(v_x_926_);
    v_r_929_ = lean_box((v_res_928_) as usize);
    return v_r_929_;
}
pub unsafe fn _init_l_Std_Time_Database_TZdb_parseTZValue___closed__1() -> *mut LeanObject {
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v___x_933_ = l_Std_Time_Database_TZdb_parseTZValue___closed__0;
    v___x_934_ = lean_string_utf8_byte_size(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_Std_Time_Database_TZdb_parseTZValue(
    mut v_tz_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_943_ = l_Std_Time_Database_TZdb_parseTZValue___closed__0;
                v___x_944_ = lean_string_utf8_byte_size(v_tz_935_);
                v___x_945_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Database_TZdb_parseTZValue___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_Database_TZdb_parseTZValue___closed__1_once),
                    _init_l_Std_Time_Database_TZdb_parseTZValue___closed__1,
                );
                v___x_946_ = lean_nat_dec_le(v___x_945_, v___x_944_);
                if v___x_946_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_947_ = lean_unsigned_to_nat(0);
                    v___x_948_ = lean_string_memcmp(
                        v_tz_935_, v___x_943_, v___x_947_, v___x_947_, v___x_945_,
                    );
                    if v___x_948_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_949_ = lean_unsigned_to_nat(1);
                        lean_inc_ref(v_tz_935_);
                        v___x_950_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_950_, 0, v_tz_935_);
                        lean_ctor_set(v___x_950_, 1, v___x_947_);
                        lean_ctor_set(v___x_950_, 2, v___x_944_);
                        v___x_951_ = l_String_Slice_Pos_nextn(v___x_950_, v___x_947_, v___x_949_);
                        lean_dec_ref_known(v___x_950_, 3);
                        v___x_952_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_952_, 0, v_tz_935_);
                        lean_ctor_set(v___x_952_, 1, v___x_951_);
                        lean_ctor_set(v___x_952_, 2, v___x_944_);
                        v_p_953_ = l_String_Slice_toString(v___x_952_);
                        lean_dec_ref_known(v___x_952_, 3);
                        v___x_954_ = lean_string_utf8_byte_size(v_p_953_);
                        v___x_955_ = lean_nat_dec_eq(v___x_954_, v___x_947_);
                        if v___x_955_ == 0 {
                            v___x_956_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_956_, 0, v_p_953_);
                            v___x_957_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_957_, 0, v___x_956_);
                            return v___x_957_;
                        } else {
                            lean_dec_ref(v_p_953_);
                            v___x_958_ = lean_box(0);
                            return v___x_958_;
                        }
                    }
                }
            }
            1 => {
                v___x_937_ = lean_string_utf8_byte_size(v_tz_935_);
                v___x_938_ = lean_unsigned_to_nat(0);
                v___x_939_ = lean_nat_dec_eq(v___x_937_, v___x_938_);
                if v___x_939_ == 0 {
                    v___x_940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_940_, 0, v_tz_935_);
                    v___x_941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_941_, 0, v___x_940_);
                    return v___x_941_;
                } else {
                    lean_dec_ref(v_tz_935_);
                    v___x_942_ = lean_box(0);
                    return v___x_942_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(
    mut v_rel_962_: *mut LeanObject,
    mut v_as_963_: *mut LeanObject,
    mut v_sz_964_: usize,
    mut v_i_965_: usize,
    mut v_b_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_968_: u8 = 0;
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: usize = 0;
    let mut v___x_976_: usize = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_968_ = lean_usize_dec_lt(v_i_965_, v_sz_964_);
                if v___x_968_ == 0 {
                    lean_dec_ref(v_rel_962_);
                    v___x_969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_969_, 0, v_b_966_);
                    return v___x_969_;
                } else {
                    lean_dec_ref(v_b_966_);
                    v_a_970_ = lean_array_uget_borrowed(v_as_963_, v_i_965_);
                    lean_inc_ref(v_rel_962_);
                    lean_inc(v_a_970_);
                    v___x_971_ = l_System_FilePath_join(v_a_970_, v_rel_962_);
                    v___x_972_ = l_System_FilePath_pathExists(v___x_971_);
                    v___x_973_ = lean_box(0);
                    if v___x_972_ == 0 {
                        lean_dec_ref(v___x_971_);
                        v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0;
                        v___x_975_ = 1usize;
                        v___x_976_ = lean_usize_add(v_i_965_, v___x_975_);
                        v_i_965_ = v___x_976_;
                        v_b_966_ = v___x_974_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_rel_962_);
                        v___x_978_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_978_, 0, v___x_971_);
                        v___x_979_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_979_, 0, v___x_978_);
                        v___x_980_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_980_, 0, v___x_979_);
                        lean_ctor_set(v___x_980_, 1, v___x_973_);
                        v___x_981_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_981_, 0, v___x_980_);
                        return v___x_981_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___boxed(
    mut v_rel_982_: *mut LeanObject,
    mut v_as_983_: *mut LeanObject,
    mut v_sz_984_: *mut LeanObject,
    mut v_i_985_: *mut LeanObject,
    mut v_b_986_: *mut LeanObject,
    mut v___y_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_988_: usize = 0;
    let mut v_i_boxed_989_: usize = 0;
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_988_ = lean_unbox_usize(v_sz_984_);
    lean_dec(v_sz_984_);
    v_i_boxed_989_ = lean_unbox_usize(v_i_985_);
    lean_dec(v_i_985_);
    v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_982_, v_as_983_, v_sz_boxed_988_, v_i_boxed_989_, v_b_986_);
    lean_dec_ref(v_as_983_);
    return v_res_990_;
}
pub unsafe fn l_Std_Time_Database_TZdb_findInPaths(
    mut v_searchPaths_991_: *mut LeanObject,
    mut v_rel_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_996_: usize = 0;
    let mut v___x_997_: usize = 0;
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v_fst_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_a_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_994_ = lean_box(0);
                v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0___closed__0;
                v_sz_996_ = lean_array_size(v_searchPaths_991_);
                v___x_997_ = 0usize;
                v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_findInPaths_spec__0(v_rel_992_, v_searchPaths_991_, v_sz_996_, v___x_997_, v___x_995_);
                if lean_obj_tag(v___x_998_) == 0 {
                    v_a_999_ = lean_ctor_get(v___x_998_, 0);
                    v_isSharedCheck_1011_ = (!lean_is_exclusive(v___x_998_)) as u8;
                    if v_isSharedCheck_1011_ == 0 {
                        v___x_1001_ = v___x_998_;
                        v_isShared_1002_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_999_);
                        lean_dec(v___x_998_);
                        v___x_1001_ = lean_box(0);
                        v_isShared_1002_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1012_ = lean_ctor_get(v___x_998_, 0);
                    v_isSharedCheck_1019_ = (!lean_is_exclusive(v___x_998_)) as u8;
                    if v_isSharedCheck_1019_ == 0 {
                        v___x_1014_ = v___x_998_;
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1012_);
                        lean_dec(v___x_998_);
                        v___x_1014_ = lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
                lean_inc(v_fst_1003_);
                lean_dec(v_a_999_);
                if lean_obj_tag(v_fst_1003_) == 0 {
                    if v_isShared_1002_ == 0 {
                        lean_ctor_set(v___x_1001_, 0, v___x_994_);
                        v___x_1005_ = v___x_1001_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_994_);
                        v___x_1005_ = v_reuseFailAlloc_1006_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1007_ = lean_ctor_get(v_fst_1003_, 0);
                    lean_inc(v_val_1007_);
                    lean_dec_ref_known(v_fst_1003_, 1);
                    if v_isShared_1002_ == 0 {
                        lean_ctor_set(v___x_1001_, 0, v_val_1007_);
                        v___x_1009_ = v___x_1001_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1007_);
                        v___x_1009_ = v_reuseFailAlloc_1010_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1005_;
            }
            3 => {
                return v___x_1009_;
            }
            4 => {
                if v_isShared_1015_ == 0 {
                    v___x_1017_ = v___x_1014_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_findInPaths___boxed(
    mut v_searchPaths_1020_: *mut LeanObject,
    mut v_rel_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1023_: *mut LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Std_Time_Database_TZdb_findInPaths(v_searchPaths_1020_, v_rel_1021_);
    lean_dec_ref(v_searchPaths_1020_);
    return v_res_1023_;
}
pub unsafe fn _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4() -> *mut LeanObject {
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1028_ = l_Std_Time_Database_TZdb_idFromPath___closed__1;
    v___x_1029_ = lean_string_utf8_byte_size(v___x_1028_);
    return v___x_1029_;
}
pub unsafe fn l_Std_Time_Database_TZdb_resolveLocalPath(
    mut v_zonesPaths_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v_val_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut v_a_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v_id_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v_val_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1104_: u8 = 0;
    let mut v_a_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1108_: u8 = 0;
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1034_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__0;
                v___x_1035_ = lean_io_getenv(v___x_1034_);
                if lean_obj_tag(v___x_1035_) == 1 {
                    v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
                    v_isSharedCheck_1117_ = (!lean_is_exclusive(v___x_1035_)) as u8;
                    if v_isSharedCheck_1117_ == 0 {
                        v___x_1038_ = v___x_1035_;
                        v_isShared_1039_ = v_isSharedCheck_1117_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1036_);
                        lean_dec(v___x_1035_);
                        v___x_1038_ = lean_box(0);
                        v_isShared_1039_ = v_isSharedCheck_1117_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1035_);
                    v___x_1118_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__6;
                    v___x_1119_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1119_, 0, v___x_1118_);
                    return v___x_1119_;
                }
            }
            1 => {
                lean_inc(v_val_1036_);
                v___x_1040_ = l_Std_Time_Database_TZdb_parseTZValue(v_val_1036_);
                if lean_obj_tag(v___x_1040_) == 1 {
                    lean_del_object(v___x_1038_);
                    v_val_1041_ = lean_ctor_get(v___x_1040_, 0);
                    lean_inc(v_val_1041_);
                    lean_dec_ref_known(v___x_1040_, 1);
                    if lean_obj_tag(v_val_1041_) == 0 {
                        v_p_1042_ = lean_ctor_get(v_val_1041_, 0);
                        v_isSharedCheck_1085_ = (!lean_is_exclusive(v_val_1041_)) as u8;
                        if v_isSharedCheck_1085_ == 0 {
                            v___x_1044_ = v_val_1041_;
                            v_isShared_1045_ = v_isSharedCheck_1085_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_p_1042_);
                            lean_dec(v_val_1041_);
                            v___x_1044_ = lean_box(0);
                            v_isShared_1045_ = v_isSharedCheck_1085_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_id_1086_ = lean_ctor_get(v_val_1041_, 0);
                        lean_inc_ref(v_id_1086_);
                        lean_dec_ref_known(v_val_1041_, 1);
                        v___x_1087_ =
                            l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_1032_, v_id_1086_);
                        if lean_obj_tag(v___x_1087_) == 0 {
                            v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
                            v_isSharedCheck_1104_ = (!lean_is_exclusive(v___x_1087_)) as u8;
                            if v_isSharedCheck_1104_ == 0 {
                                v___x_1090_ = v___x_1087_;
                                v_isShared_1091_ = v_isSharedCheck_1104_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_1088_);
                                lean_dec(v___x_1087_);
                                v___x_1090_ = lean_box(0);
                                v_isShared_1091_ = v_isSharedCheck_1104_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_1036_);
                            v_a_1105_ = lean_ctor_get(v___x_1087_, 0);
                            v_isSharedCheck_1112_ = (!lean_is_exclusive(v___x_1087_)) as u8;
                            if v_isSharedCheck_1112_ == 0 {
                                v___x_1107_ = v___x_1087_;
                                v_isShared_1108_ = v_isSharedCheck_1112_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_1105_);
                                lean_dec(v___x_1087_);
                                v___x_1107_ = lean_box(0);
                                v_isShared_1108_ = v_isSharedCheck_1112_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_1040_);
                    lean_dec(v_val_1036_);
                    v___x_1113_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__6;
                    if v_isShared_1039_ == 0 {
                        lean_ctor_set_tag(v___x_1038_, 0);
                        lean_ctor_set(v___x_1038_, 0, v___x_1113_);
                        v___x_1115_ = v___x_1038_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
                        v___x_1115_ = v_reuseFailAlloc_1116_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1076_ = l_Std_Time_Database_TZdb_idFromPath___closed__1;
                v___x_1077_ = lean_string_utf8_byte_size(v_p_1042_);
                v___x_1078_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Database_TZdb_resolveLocalPath___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_Database_TZdb_resolveLocalPath___closed__4_once
                    ),
                    _init_l_Std_Time_Database_TZdb_resolveLocalPath___closed__4,
                );
                v___x_1079_ = lean_nat_dec_le(v___x_1078_, v___x_1077_);
                if v___x_1079_ == 0 {
                    lean_del_object(v___x_1044_);
                    state = 3;
                    continue;
                } else {
                    v___x_1080_ = lean_unsigned_to_nat(0);
                    v___x_1081_ = lean_string_memcmp(
                        v_p_1042_,
                        v___x_1076_,
                        v___x_1080_,
                        v___x_1080_,
                        v___x_1078_,
                    );
                    if v___x_1081_ == 0 {
                        lean_del_object(v___x_1044_);
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_val_1036_);
                        if v_isShared_1045_ == 0 {
                            v___x_1083_ = v___x_1044_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_p_1042_);
                            v___x_1083_ = v_reuseFailAlloc_1084_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                lean_inc_ref(v_p_1042_);
                v___x_1047_ = l_Std_Time_Database_TZdb_findInPaths(v_zonesPaths_1032_, v_p_1042_);
                if lean_obj_tag(v___x_1047_) == 0 {
                    v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
                    v_isSharedCheck_1067_ = (!lean_is_exclusive(v___x_1047_)) as u8;
                    if v_isSharedCheck_1067_ == 0 {
                        v___x_1050_ = v___x_1047_;
                        v_isShared_1051_ = v_isSharedCheck_1067_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1048_);
                        lean_dec(v___x_1047_);
                        v___x_1050_ = lean_box(0);
                        v_isShared_1051_ = v_isSharedCheck_1067_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_1042_);
                    lean_dec(v_val_1036_);
                    v_a_1068_ = lean_ctor_get(v___x_1047_, 0);
                    v_isSharedCheck_1075_ = (!lean_is_exclusive(v___x_1047_)) as u8;
                    if v_isSharedCheck_1075_ == 0 {
                        v___x_1070_ = v___x_1047_;
                        v_isShared_1071_ = v_isSharedCheck_1075_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1068_);
                        lean_dec(v___x_1047_);
                        v___x_1070_ = lean_box(0);
                        v_isShared_1071_ = v_isSharedCheck_1075_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_1048_) == 1 {
                    lean_dec_ref(v_p_1042_);
                    lean_dec(v_val_1036_);
                    v_val_1052_ = lean_ctor_get(v_a_1048_, 0);
                    lean_inc(v_val_1052_);
                    lean_dec_ref_known(v_a_1048_, 1);
                    if v_isShared_1051_ == 0 {
                        lean_ctor_set(v___x_1050_, 0, v_val_1052_);
                        v___x_1054_ = v___x_1050_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_val_1052_);
                        v___x_1054_ = v_reuseFailAlloc_1055_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1048_);
                    v___x_1056_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__1;
                    v___x_1057_ = lean_string_append(v___x_1056_, v_val_1036_);
                    lean_dec(v_val_1036_);
                    v___x_1058_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__2;
                    v___x_1059_ = lean_string_append(v___x_1057_, v___x_1058_);
                    v___x_1060_ = lean_string_append(v___x_1059_, v_p_1042_);
                    lean_dec_ref(v_p_1042_);
                    v___x_1061_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__3;
                    v___x_1062_ = lean_string_append(v___x_1060_, v___x_1061_);
                    v___x_1063_ = lean_mk_io_user_error(v___x_1062_);
                    if v_isShared_1051_ == 0 {
                        lean_ctor_set_tag(v___x_1050_, 1);
                        lean_ctor_set(v___x_1050_, 0, v___x_1063_);
                        v___x_1065_ = v___x_1050_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
                        v___x_1065_ = v_reuseFailAlloc_1066_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1054_;
            }
            6 => {
                return v___x_1065_;
            }
            7 => {
                if v_isShared_1071_ == 0 {
                    v___x_1073_ = v___x_1070_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
                    v___x_1073_ = v_reuseFailAlloc_1074_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1073_;
            }
            9 => {
                return v___x_1083_;
            }
            10 => {
                if lean_obj_tag(v_a_1088_) == 1 {
                    lean_dec(v_val_1036_);
                    v_val_1092_ = lean_ctor_get(v_a_1088_, 0);
                    lean_inc(v_val_1092_);
                    lean_dec_ref_known(v_a_1088_, 1);
                    if v_isShared_1091_ == 0 {
                        lean_ctor_set(v___x_1090_, 0, v_val_1092_);
                        v___x_1094_ = v___x_1090_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_val_1092_);
                        v___x_1094_ = v_reuseFailAlloc_1095_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1088_);
                    v___x_1096_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__1;
                    v___x_1097_ = lean_string_append(v___x_1096_, v_val_1036_);
                    lean_dec(v_val_1036_);
                    v___x_1098_ = l_Std_Time_Database_TZdb_resolveLocalPath___closed__5;
                    v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
                    v___x_1100_ = lean_mk_io_user_error(v___x_1099_);
                    if v_isShared_1091_ == 0 {
                        lean_ctor_set_tag(v___x_1090_, 1);
                        lean_ctor_set(v___x_1090_, 0, v___x_1100_);
                        v___x_1102_ = v___x_1090_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
                        v___x_1102_ = v_reuseFailAlloc_1103_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_1094_;
            }
            12 => {
                return v___x_1102_;
            }
            13 => {
                if v_isShared_1108_ == 0 {
                    v___x_1110_ = v___x_1107_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
                    v___x_1110_ = v_reuseFailAlloc_1111_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1110_;
            }
            15 => {
                return v___x_1115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_resolveLocalPath___boxed(
    mut v_zonesPaths_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_zonesPaths_1120_);
    lean_dec_ref(v_zonesPaths_1120_);
    return v_res_1122_;
}
pub unsafe fn l_Std_Time_Database_TZdb_resolveZonesPaths(
    mut v_db_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1142_ = l_Std_Time_Database_TZdb_resolveZonesPaths___closed__0;
                v___x_1143_ = lean_io_getenv(v___x_1142_);
                if lean_obj_tag(v___x_1143_) == 0 {
                    v___x_1144_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1144_, 0, v_db_1140_);
                    return v___x_1144_;
                } else {
                    v_val_1145_ = lean_ctor_get(v___x_1143_, 0);
                    v_isSharedCheck_1165_ = (!lean_is_exclusive(v___x_1143_)) as u8;
                    if v_isSharedCheck_1165_ == 0 {
                        v___x_1147_ = v___x_1143_;
                        v_isShared_1148_ = v_isSharedCheck_1165_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1145_);
                        lean_dec(v___x_1143_);
                        v___x_1147_ = lean_box(0);
                        v_isShared_1148_ = v_isSharedCheck_1165_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1149_ = l_Std_Time_Database_TZdb_resolveZonesPaths___closed__1;
                v___x_1150_ = lean_string_dec_eq(v_val_1145_, v___x_1149_);
                if v___x_1150_ == 0 {
                    v___x_1151_ = l_System_FilePath_pathExists(v_val_1145_);
                    if v___x_1151_ == 0 {
                        lean_dec(v_val_1145_);
                        if v_isShared_1148_ == 0 {
                            lean_ctor_set_tag(v___x_1147_, 0);
                            lean_ctor_set(v___x_1147_, 0, v_db_1140_);
                            v___x_1153_ = v___x_1147_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_db_1140_);
                            v___x_1153_ = v_reuseFailAlloc_1154_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1155_ = lean_unsigned_to_nat(1);
                        v___x_1156_ = lean_mk_empty_array_with_capacity(v___x_1155_);
                        v___x_1157_ = lean_array_push(v___x_1156_, v_val_1145_);
                        v___x_1158_ = l_Array_append___redArg(v___x_1157_, v_db_1140_);
                        lean_dec_ref(v_db_1140_);
                        if v_isShared_1148_ == 0 {
                            lean_ctor_set_tag(v___x_1147_, 0);
                            lean_ctor_set(v___x_1147_, 0, v___x_1158_);
                            v___x_1160_ = v___x_1147_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
                            v___x_1160_ = v_reuseFailAlloc_1161_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_1145_);
                    if v_isShared_1148_ == 0 {
                        lean_ctor_set_tag(v___x_1147_, 0);
                        lean_ctor_set(v___x_1147_, 0, v_db_1140_);
                        v___x_1163_ = v___x_1147_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_db_1140_);
                        v___x_1163_ = v_reuseFailAlloc_1164_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1153_;
            }
            3 => {
                return v___x_1160_;
            }
            4 => {
                return v___x_1163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_resolveZonesPaths___boxed(
    mut v_db_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1168_: *mut LeanObject = core::ptr::null_mut();
    v_res_1168_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_1166_);
    return v_res_1168_;
}
pub unsafe fn l_Std_Time_Database_TZdb_getLocalZoneRules(
    mut v_db_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1179_: u8 = 0;
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1171_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_1169_);
                v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
                lean_inc(v_a_1172_);
                lean_dec_ref(v___x_1171_);
                v___x_1173_ = l_Std_Time_Database_TZdb_resolveLocalPath(v_a_1172_);
                lean_dec(v_a_1172_);
                if lean_obj_tag(v___x_1173_) == 0 {
                    v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
                    lean_inc(v_a_1174_);
                    lean_dec_ref_known(v___x_1173_, 1);
                    v___x_1175_ = l_Std_Time_Database_TZdb_localRules(v_a_1174_);
                    return v___x_1175_;
                } else {
                    v_a_1176_ = lean_ctor_get(v___x_1173_, 0);
                    v_isSharedCheck_1183_ = (!lean_is_exclusive(v___x_1173_)) as u8;
                    if v_isSharedCheck_1183_ == 0 {
                        v___x_1178_ = v___x_1173_;
                        v_isShared_1179_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1176_);
                        lean_dec(v___x_1173_);
                        v___x_1178_ = lean_box(0);
                        v_isShared_1179_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1179_ == 0 {
                    v___x_1181_ = v___x_1178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
                    v___x_1181_ = v_reuseFailAlloc_1182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_getLocalZoneRules___boxed(
    mut v_db_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1186_: *mut LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Std_Time_Database_TZdb_getLocalZoneRules(v_db_1184_);
    return v_res_1186_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(
    mut v_id_1190_: *mut LeanObject,
    mut v_as_1191_: *mut LeanObject,
    mut v_sz_1192_: usize,
    mut v_i_1193_: usize,
    mut v_b_1194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: usize = 0;
    let mut v___x_1204_: usize = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_a_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1196_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
                if v___x_1196_ == 0 {
                    lean_dec_ref(v_id_1190_);
                    v___x_1197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1197_, 0, v_b_1194_);
                    return v___x_1197_;
                } else {
                    lean_dec_ref(v_b_1194_);
                    v_a_1198_ = lean_array_uget_borrowed(v_as_1191_, v_i_1193_);
                    lean_inc_ref(v_id_1190_);
                    lean_inc(v_a_1198_);
                    v___x_1199_ = l_System_FilePath_join(v_a_1198_, v_id_1190_);
                    v___x_1200_ = l_System_FilePath_pathExists(v___x_1199_);
                    lean_dec_ref(v___x_1199_);
                    v___x_1201_ = lean_box(0);
                    if v___x_1200_ == 0 {
                        v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0;
                        v___x_1203_ = 1usize;
                        v___x_1204_ = lean_usize_add(v_i_1193_, v___x_1203_);
                        v_i_1193_ = v___x_1204_;
                        v_b_1194_ = v___x_1202_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_a_1198_);
                        v___x_1206_ =
                            l_Std_Time_Database_TZdb_readRulesFromDisk(v_a_1198_, v_id_1190_);
                        if lean_obj_tag(v___x_1206_) == 0 {
                            v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
                            v_isSharedCheck_1216_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                            if v_isSharedCheck_1216_ == 0 {
                                v___x_1209_ = v___x_1206_;
                                v_isShared_1210_ = v_isSharedCheck_1216_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1207_);
                                lean_dec(v___x_1206_);
                                v___x_1209_ = lean_box(0);
                                v_isShared_1210_ = v_isSharedCheck_1216_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1217_ = lean_ctor_get(v___x_1206_, 0);
                            v_isSharedCheck_1224_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                            if v_isSharedCheck_1224_ == 0 {
                                v___x_1219_ = v___x_1206_;
                                v_isShared_1220_ = v_isSharedCheck_1224_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1217_);
                                lean_dec(v___x_1206_);
                                v___x_1219_ = lean_box(0);
                                v_isShared_1220_ = v_isSharedCheck_1224_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1211_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1211_, 0, v_a_1207_);
                v___x_1212_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1212_, 0, v___x_1211_);
                lean_ctor_set(v___x_1212_, 1, v___x_1201_);
                if v_isShared_1210_ == 0 {
                    lean_ctor_set(v___x_1209_, 0, v___x_1212_);
                    v___x_1214_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
                    v___x_1214_ = v_reuseFailAlloc_1215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1214_;
            }
            3 => {
                if v_isShared_1220_ == 0 {
                    v___x_1222_ = v___x_1219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
                    v___x_1222_ = v_reuseFailAlloc_1223_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___boxed(
    mut v_id_1225_: *mut LeanObject,
    mut v_as_1226_: *mut LeanObject,
    mut v_sz_1227_: *mut LeanObject,
    mut v_i_1228_: *mut LeanObject,
    mut v_b_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1231_: usize = 0;
    let mut v_i_boxed_1232_: usize = 0;
    let mut v_res_1233_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1227_);
    lean_dec(v_sz_1227_);
    v_i_boxed_1232_ = lean_unbox_usize(v_i_1228_);
    lean_dec(v_i_1228_);
    v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_1225_, v_as_1226_, v_sz_boxed_1231_, v_i_boxed_1232_, v_b_1229_);
    lean_dec_ref(v_as_1226_);
    return v_res_1233_;
}
pub unsafe fn l_Std_Time_Database_TZdb_getZoneRules(
    mut v_db_1236_: *mut LeanObject,
    mut v_id_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v_fst_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut v_a_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = l_Std_Time_Database_TZdb_resolveZonesPaths(v_db_1236_);
                v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
                lean_inc(v_a_1240_);
                lean_dec_ref(v___x_1239_);
                v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0___closed__0;
                v_sz_1242_ = lean_array_size(v_a_1240_);
                v___x_1243_ = 0usize;
                lean_inc_ref(v_id_1237_);
                v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_Database_TZdb_getZoneRules_spec__0(v_id_1237_, v_a_1240_, v_sz_1242_, v___x_1243_, v___x_1241_);
                lean_dec(v_a_1240_);
                if lean_obj_tag(v___x_1244_) == 0 {
                    v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
                    v_isSharedCheck_1262_ = (!lean_is_exclusive(v___x_1244_)) as u8;
                    if v_isSharedCheck_1262_ == 0 {
                        v___x_1247_ = v___x_1244_;
                        v_isShared_1248_ = v_isSharedCheck_1262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1245_);
                        lean_dec(v___x_1244_);
                        v___x_1247_ = lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1262_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_id_1237_);
                    v_a_1263_ = lean_ctor_get(v___x_1244_, 0);
                    v_isSharedCheck_1270_ = (!lean_is_exclusive(v___x_1244_)) as u8;
                    if v_isSharedCheck_1270_ == 0 {
                        v___x_1265_ = v___x_1244_;
                        v_isShared_1266_ = v_isSharedCheck_1270_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1263_);
                        lean_dec(v___x_1244_);
                        v___x_1265_ = lean_box(0);
                        v_isShared_1266_ = v_isSharedCheck_1270_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
                lean_inc(v_fst_1249_);
                lean_dec(v_a_1245_);
                if lean_obj_tag(v_fst_1249_) == 0 {
                    v___x_1250_ = l_Std_Time_Database_TZdb_getZoneRules___closed__0;
                    v___x_1251_ = lean_string_append(v___x_1250_, v_id_1237_);
                    lean_dec_ref(v_id_1237_);
                    v___x_1252_ = l_Std_Time_Database_TZdb_getZoneRules___closed__1;
                    v___x_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
                    v___x_1254_ = lean_mk_io_user_error(v___x_1253_);
                    if v_isShared_1248_ == 0 {
                        lean_ctor_set_tag(v___x_1247_, 1);
                        lean_ctor_set(v___x_1247_, 0, v___x_1254_);
                        v___x_1256_ = v___x_1247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
                        v___x_1256_ = v_reuseFailAlloc_1257_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_id_1237_);
                    v_val_1258_ = lean_ctor_get(v_fst_1249_, 0);
                    lean_inc(v_val_1258_);
                    lean_dec_ref_known(v_fst_1249_, 1);
                    if v_isShared_1248_ == 0 {
                        lean_ctor_set(v___x_1247_, 0, v_val_1258_);
                        v___x_1260_ = v___x_1247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1258_);
                        v___x_1260_ = v_reuseFailAlloc_1261_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1256_;
            }
            3 => {
                return v___x_1260_;
            }
            4 => {
                if v_isShared_1266_ == 0 {
                    v___x_1268_ = v___x_1265_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
                    v___x_1268_ = v_reuseFailAlloc_1269_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_TZdb_getZoneRules___boxed(
    mut v_db_1271_: *mut LeanObject,
    mut v_id_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1274_: *mut LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Std_Time_Database_TZdb_getZoneRules(v_db_1271_, v_id_1272_);
    return v_res_1274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database_TZdb(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_Database_TZdb(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_Database_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_TZdb(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database_TZdb(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database_TZdb(builtin);
}
