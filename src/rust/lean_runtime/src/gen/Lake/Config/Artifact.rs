// Lean compiler output
// Module: Lake.Config.Artifact
// Imports: Lake.Build.Trace
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::System::IO::l_IO_FS_instReprSystemTime_repr___redArg;
use crate::r#gen::Lake::Build::Trace::{
    initialize_Lake_Build_Trace, l_Lake_Hash_nil, l_Lake_Hash_ofHex_x3f,
    l_Lake_instReprHash_repr___redArg, runtime_initialize_Lake_Build_Trace,
};
use crate::r#gen::Lake::Util::String::l_Lake_lowerHexUInt64;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_getStr_x3f;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint32,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_Lake_artifactPath___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_artifactPath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_artifactPath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedArtifactDescr_default___closed__0_value: LeanStringObject<4> =
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
        m_data: [97, 114, 116, 0],
    };
static mut l_Lake_instInhabitedArtifactDescr_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedArtifactDescr_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedArtifactDescr_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedArtifactDescr_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedArtifactDescr_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedArtifactDescr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value: LeanStringObject<3> =
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
        m_data: [123, 32, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value: LeanStringObject<5> =
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
        m_data: [104, 97, 115, 104, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value: LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value: LeanStringObject<4> =
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
        m_data: [101, 120, 116, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value: LeanStringObject<3> =
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
        m_data: [32, 125, 0],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifactDescr_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifactDescr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprArtifactDescr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprArtifactDescr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprArtifactDescr: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifactDescr___closed__0_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ArtifactDescr_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ArtifactDescr_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ArtifactDescr_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_instToJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ArtifactDescr_instToJson___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ArtifactDescr_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ArtifactDescr_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value: LeanStringObject<49> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 114, 116, 105, 102, 97, 99, 116, 32,
            102, 105, 108, 101, 32, 110, 97, 109, 101, 32, 116, 111, 32, 98, 101, 32, 97, 32, 99,
            111, 110, 116, 101, 110, 116, 32, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value: LeanStringObject<1> =
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
static mut l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value: LeanStringObject<37> =
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
            97, 114, 116, 105, 102, 97, 99, 116, 32, 105, 110, 32, 117, 110, 101, 120, 112, 101,
            99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 102, 111, 114, 109, 97, 116, 58, 32, 0,
        ],
    };
static mut l_Lake_ArtifactDescr_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_ArtifactDescr_instFromJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ArtifactDescr_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ArtifactDescr_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ArtifactDescr_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArtifactDescr_instFromJson___closed__0_value) as *mut LeanObject;
static mut l_Lake_instInhabitedArtifact_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedArtifact_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedArtifact_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedArtifact_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedArtifact_default___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedArtifact_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedArtifact_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedArtifact: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprArtifact_repr___redArg___closed__0_value: LeanStringObject<6> =
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
        m_data: [100, 101, 115, 99, 114, 0],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lake_instReprArtifact_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprArtifact_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprArtifact_repr___redArg___closed__5_value: LeanStringObject<5> =
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
        m_data: [112, 97, 116, 104, 0],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__7_value: LeanStringObject<13> =
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
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__9_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__10_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__11_value: LeanStringObject<6> =
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
        m_data: [109, 116, 105, 109, 101, 0],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifact_repr___redArg___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprArtifact_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_instReprArtifact___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprArtifact_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprArtifact___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprArtifact: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprArtifact___closed__0_value) as *mut LeanObject;
pub static l_Lake_Artifact_trace___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Artifact_trace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Artifact_trace___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_artifactPath(
    mut v_contentHash_380_: u64,
    mut v_ext_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: u8 = 0;
    v___x_382_ = lean_string_utf8_byte_size(v_ext_381_);
    v___x_383_ = lean_unsigned_to_nat(0);
    v___x_384_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
    if v___x_384_ == 0 {
        let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
        v___x_385_ = l_Lake_lowerHexUInt64(v_contentHash_380_);
        v___x_386_ = l_Lake_artifactPath___closed__0;
        v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
        v___x_388_ = lean_string_append(v___x_387_, v_ext_381_);
        return v___x_388_;
    } else {
        let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
        v___x_389_ = l_Lake_lowerHexUInt64(v_contentHash_380_);
        return v___x_389_;
    }
}
pub unsafe fn l_Lake_artifactPath___boxed(
    mut v_contentHash_390_: *mut LeanObject,
    mut v_ext_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_contentHash_boxed_392_: u64 = 0;
    let mut v_res_393_: *mut LeanObject = core::ptr::null_mut();
    v_contentHash_boxed_392_ = lean_unbox_uint64(v_contentHash_390_);
    lean_dec_ref(v_contentHash_390_);
    v_res_393_ = l_Lake_artifactPath(v_contentHash_boxed_392_, v_ext_391_);
    lean_dec_ref(v_ext_391_);
    return v_res_393_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifactDescr_default___closed__1() -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u64 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Lake_instInhabitedArtifactDescr_default___closed__0;
    v___x_396_ = l_Lake_Hash_nil;
    v___x_397_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_397_, 0, v___x_395_);
    lean_ctor_set_uint64(
        v___x_397_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_396_,
    );
    return v___x_397_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifactDescr_default() -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifactDescr_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifactDescr_default___closed__1_once),
        _init_l_Lake_instInhabitedArtifactDescr_default___closed__1,
    );
    return v___x_398_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifactDescr() -> *mut LeanObject {
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    v___x_399_ = l_Lake_instInhabitedArtifactDescr_default;
    return v___x_399_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprArtifactDescr_repr_spec__0(
    mut v_a_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = lean_nat_to_int(v_a_400_);
    return v___x_401_;
}
pub unsafe fn _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_415_ = lean_unsigned_to_nat(8);
    v___x_416_ = lean_nat_to_int(v___x_415_);
    return v___x_416_;
}
pub unsafe fn _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_unsigned_to_nat(7);
    v___x_424_ = lean_nat_to_int(v___x_423_);
    return v___x_424_;
}
pub unsafe fn _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_426_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__0;
    v___x_427_ = lean_string_length(v___x_426_);
    return v___x_427_;
}
pub unsafe fn _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14,
    );
    v___x_429_ = lean_nat_to_int(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Lake_instReprArtifactDescr_repr___redArg(
    mut v_x_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_435_: u64 = 0;
    let mut v_ext_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v_hash_435_ = lean_ctor_get_uint64(
        v_x_434_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_ext_436_ = lean_ctor_get(v_x_434_, 0);
    lean_inc_ref(v_ext_436_);
    lean_dec_ref(v_x_434_);
    v___x_437_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__5;
    v___x_438_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__6;
    v___x_439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7,
    );
    v___x_440_ = l_Lake_instReprHash_repr___redArg(v_hash_435_);
    v___x_441_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_441_, 0, v___x_439_);
    lean_ctor_set(v___x_441_, 1, v___x_440_);
    v___x_442_ = 0;
    v___x_443_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_443_, 0, v___x_441_);
    lean_ctor_set_uint8(
        v___x_443_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_442_,
    );
    v___x_444_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_444_, 0, v___x_438_);
    lean_ctor_set(v___x_444_, 1, v___x_443_);
    v___x_445_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__9;
    v___x_446_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_446_, 0, v___x_444_);
    lean_ctor_set(v___x_446_, 1, v___x_445_);
    v___x_447_ = lean_box(1);
    v___x_448_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_448_, 0, v___x_446_);
    lean_ctor_set(v___x_448_, 1, v___x_447_);
    v___x_449_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__11;
    v___x_450_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_450_, 0, v___x_448_);
    lean_ctor_set(v___x_450_, 1, v___x_449_);
    v___x_451_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_451_, 0, v___x_450_);
    lean_ctor_set(v___x_451_, 1, v___x_437_);
    v___x_452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12,
    );
    v___x_453_ = l_String_quote(v_ext_436_);
    v___x_454_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_454_, 0, v___x_453_);
    v___x_455_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_455_, 0, v___x_452_);
    lean_ctor_set(v___x_455_, 1, v___x_454_);
    v___x_456_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_456_, 0, v___x_455_);
    lean_ctor_set_uint8(
        v___x_456_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_442_,
    );
    v___x_457_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_457_, 0, v___x_451_);
    lean_ctor_set(v___x_457_, 1, v___x_456_);
    v___x_458_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15,
    );
    v___x_459_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__16;
    v___x_460_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_460_, 0, v___x_459_);
    lean_ctor_set(v___x_460_, 1, v___x_457_);
    v___x_461_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__17;
    v___x_462_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_462_, 0, v___x_460_);
    lean_ctor_set(v___x_462_, 1, v___x_461_);
    v___x_463_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_463_, 0, v___x_458_);
    lean_ctor_set(v___x_463_, 1, v___x_462_);
    v___x_464_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_464_, 0, v___x_463_);
    lean_ctor_set_uint8(
        v___x_464_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_442_,
    );
    return v___x_464_;
}
pub unsafe fn l_Lake_instReprArtifactDescr_repr(
    mut v_x_465_: *mut LeanObject,
    mut v_prec_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Lake_instReprArtifactDescr_repr___redArg(v_x_465_);
    return v___x_467_;
}
pub unsafe fn l_Lake_instReprArtifactDescr_repr___boxed(
    mut v_x_468_: *mut LeanObject,
    mut v_prec_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_470_: *mut LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lake_instReprArtifactDescr_repr(v_x_468_, v_prec_469_);
    lean_dec(v_prec_469_);
    return v_res_470_;
}
pub unsafe fn l_Lake_artifactWithExt(
    mut v_contentHash_473_: u64,
    mut v_ext_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_475_, 0, v_ext_474_);
    lean_ctor_set_uint64(
        v___x_475_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_contentHash_473_,
    );
    return v___x_475_;
}
pub unsafe fn l_Lake_artifactWithExt___boxed(
    mut v_contentHash_476_: *mut LeanObject,
    mut v_ext_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_contentHash_boxed_478_: u64 = 0;
    let mut v_res_479_: *mut LeanObject = core::ptr::null_mut();
    v_contentHash_boxed_478_ = lean_unbox_uint64(v_contentHash_476_);
    lean_dec_ref(v_contentHash_476_);
    v_res_479_ = l_Lake_artifactWithExt(v_contentHash_boxed_478_, v_ext_477_);
    return v_res_479_;
}
pub unsafe fn l_Lake_ArtifactDescr_relPath(mut v_self_480_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hash_481_: u64 = 0;
    let mut v_ext_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: u8 = 0;
    v_hash_481_ = lean_ctor_get_uint64(
        v_self_480_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_ext_482_ = lean_ctor_get(v_self_480_, 0);
    v___x_483_ = lean_string_utf8_byte_size(v_ext_482_);
    v___x_484_ = lean_unsigned_to_nat(0);
    v___x_485_ = lean_nat_dec_eq(v___x_483_, v___x_484_);
    if v___x_485_ == 0 {
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        v___x_486_ = l_Lake_lowerHexUInt64(v_hash_481_);
        v___x_487_ = l_Lake_artifactPath___closed__0;
        v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
        v___x_489_ = lean_string_append(v___x_488_, v_ext_482_);
        return v___x_489_;
    } else {
        let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
        v___x_490_ = l_Lake_lowerHexUInt64(v_hash_481_);
        return v___x_490_;
    }
}
pub unsafe fn l_Lake_ArtifactDescr_relPath___boxed(
    mut v_self_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_492_: *mut LeanObject = core::ptr::null_mut();
    v_res_492_ = l_Lake_ArtifactDescr_relPath(v_self_491_);
    lean_dec_ref(v_self_491_);
    return v_res_492_;
}
pub unsafe fn l_Lake_ArtifactDescr_instToString___lam__0(
    mut v_x_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_494_: u64 = 0;
    let mut v_ext_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    v_hash_494_ = lean_ctor_get_uint64(
        v_x_493_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_ext_495_ = lean_ctor_get(v_x_493_, 0);
    v___x_496_ = lean_string_utf8_byte_size(v_ext_495_);
    v___x_497_ = lean_unsigned_to_nat(0);
    v___x_498_ = lean_nat_dec_eq(v___x_496_, v___x_497_);
    if v___x_498_ == 0 {
        let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        v___x_499_ = l_Lake_lowerHexUInt64(v_hash_494_);
        v___x_500_ = l_Lake_artifactPath___closed__0;
        v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
        v___x_502_ = lean_string_append(v___x_501_, v_ext_495_);
        return v___x_502_;
    } else {
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        v___x_503_ = l_Lake_lowerHexUInt64(v_hash_494_);
        return v___x_503_;
    }
}
pub unsafe fn l_Lake_ArtifactDescr_instToString___lam__0___boxed(
    mut v_x_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_505_: *mut LeanObject = core::ptr::null_mut();
    v_res_505_ = l_Lake_ArtifactDescr_instToString___lam__0(v_x_504_);
    lean_dec_ref(v_x_504_);
    return v_res_505_;
}
pub unsafe fn l_Lake_ArtifactDescr_instToJson___lam__0(
    mut v_x_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_509_: u64 = 0;
    let mut v_ext_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    v_hash_509_ = lean_ctor_get_uint64(
        v_x_508_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_ext_510_ = lean_ctor_get(v_x_508_, 0);
    v___x_511_ = lean_string_utf8_byte_size(v_ext_510_);
    v___x_512_ = lean_unsigned_to_nat(0);
    v___x_513_ = lean_nat_dec_eq(v___x_511_, v___x_512_);
    if v___x_513_ == 0 {
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
        v___x_514_ = l_Lake_lowerHexUInt64(v_hash_509_);
        v___x_515_ = l_Lake_artifactPath___closed__0;
        v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
        v___x_517_ = lean_string_append(v___x_516_, v_ext_510_);
        v___x_518_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_518_, 0, v___x_517_);
        return v___x_518_;
    } else {
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        v___x_519_ = l_Lake_lowerHexUInt64(v_hash_509_);
        v___x_520_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_520_, 0, v___x_519_);
        return v___x_520_;
    }
}
pub unsafe fn l_Lake_ArtifactDescr_instToJson___lam__0___boxed(
    mut v_x_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_522_: *mut LeanObject = core::ptr::null_mut();
    v_res_522_ = l_Lake_ArtifactDescr_instToJson___lam__0(v_x_521_);
    lean_dec_ref(v_x_521_);
    return v_res_522_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(
    mut v___x_525_: *mut LeanObject,
    mut v_s_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
    mut v_b_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    let mut v___x_533_: u32 = 0;
    let mut v___x_534_: u32 = 0;
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_529_ = lean_ctor_get(v___x_525_, 1);
                v_endExclusive_530_ = lean_ctor_get(v___x_525_, 2);
                v___x_531_ = lean_nat_sub(v_endExclusive_530_, v_startInclusive_529_);
                v___x_532_ = lean_nat_dec_eq(v_a_527_, v___x_531_);
                lean_dec(v___x_531_);
                if v___x_532_ == 0 {
                    v___x_533_ = lean_string_utf8_get_fast(v_s_526_, v_a_527_);
                    v___x_534_ = 46;
                    v___x_535_ = lean_uint32_dec_eq(v___x_533_, v___x_534_);
                    if v___x_535_ == 0 {
                        v___x_536_ = lean_box(0);
                        v___x_537_ = lean_string_utf8_next_fast(v_s_526_, v_a_527_);
                        lean_dec(v_a_527_);
                        v_a_527_ = v___x_537_;
                        v_b_528_ = v___x_536_;
                        state = 0;
                        continue;
                    } else {
                        v___x_539_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_539_, 0, v_a_527_);
                        return v___x_539_;
                    }
                } else {
                    lean_dec(v_a_527_);
                    lean_inc(v_b_528_);
                    return v_b_528_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg___boxed(
    mut v___x_540_: *mut LeanObject,
    mut v_s_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
    mut v_b_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_544_: *mut LeanObject = core::ptr::null_mut();
    v_res_544_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(
            v___x_540_, v_s_541_, v_a_542_, v_b_543_,
        );
    lean_dec(v_b_543_);
    lean_dec_ref(v_s_541_);
    lean_dec_ref(v___x_540_);
    return v_res_544_;
}
pub unsafe fn l_Lake_ArtifactDescr_ofFilePath_x3f(
    mut v_path_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_560_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: u64 = 0;
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_568_: u8 = 0;
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: u64 = 0;
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_588_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_583_ = lean_unsigned_to_nat(0);
                v___x_584_ = lean_string_utf8_byte_size(v_path_549_);
                lean_inc_ref(v_path_549_);
                v___x_585_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_585_, 0, v_path_549_);
                lean_ctor_set(v___x_585_, 1, v_searcher_583_);
                lean_ctor_set(v___x_585_, 2, v___x_584_);
                v___x_586_ = lean_box(0);
                v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_585_, v_path_549_, v_searcher_583_, v___x_586_);
                lean_dec_ref_known(v___x_585_, 3);
                if lean_obj_tag(v___x_587_) == 0 {
                    v___y_551_ = v___x_584_;
                    state = 1;
                    continue;
                } else {
                    v_val_588_ = lean_ctor_get(v___x_587_, 0);
                    lean_inc(v_val_588_);
                    lean_dec_ref_known(v___x_587_, 1);
                    v___y_551_ = v_val_588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_552_ = lean_string_utf8_byte_size(v_path_549_);
                v___x_553_ = lean_nat_dec_eq(v___y_551_, v___x_552_);
                if v___x_553_ == 0 {
                    v___x_554_ = lean_unsigned_to_nat(0);
                    v___x_555_ = lean_string_utf8_extract(v_path_549_, v___x_554_, v___y_551_);
                    v___x_556_ = l_Lake_Hash_ofHex_x3f(v___x_555_);
                    lean_dec_ref(v___x_555_);
                    if lean_obj_tag(v___x_556_) == 1 {
                        v_val_557_ = lean_ctor_get(v___x_556_, 0);
                        v_isSharedCheck_568_ = (!lean_is_exclusive(v___x_556_)) as u8;
                        if v_isSharedCheck_568_ == 0 {
                            v___x_559_ = v___x_556_;
                            v_isShared_560_ = v_isSharedCheck_568_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_557_);
                            lean_dec(v___x_556_);
                            v___x_559_ = lean_box(0);
                            v_isShared_560_ = v_isSharedCheck_568_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_556_);
                        lean_dec(v___y_551_);
                        lean_dec_ref(v_path_549_);
                        v___x_569_ = l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1;
                        return v___x_569_;
                    }
                } else {
                    lean_dec(v___y_551_);
                    v___x_570_ = l_Lake_Hash_ofHex_x3f(v_path_549_);
                    lean_dec_ref(v_path_549_);
                    if lean_obj_tag(v___x_570_) == 1 {
                        v_val_571_ = lean_ctor_get(v___x_570_, 0);
                        v_isSharedCheck_581_ = (!lean_is_exclusive(v___x_570_)) as u8;
                        if v_isSharedCheck_581_ == 0 {
                            v___x_573_ = v___x_570_;
                            v_isShared_574_ = v_isSharedCheck_581_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_571_);
                            lean_dec(v___x_570_);
                            v___x_573_ = lean_box(0);
                            v_isShared_574_ = v_isSharedCheck_581_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_570_);
                        v___x_582_ = l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1;
                        return v___x_582_;
                    }
                }
            }
            2 => {
                v___x_561_ = lean_string_utf8_next_fast(v_path_549_, v___y_551_);
                lean_dec(v___y_551_);
                v_ext_562_ = lean_string_utf8_extract(v_path_549_, v___x_561_, v___x_552_);
                lean_dec_ref(v_path_549_);
                v___x_563_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_563_, 0, v_ext_562_);
                v___x_564_ = lean_unbox_uint64(v_val_557_);
                lean_dec(v_val_557_);
                lean_ctor_set_uint64(
                    v___x_563_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_564_,
                );
                if v_isShared_560_ == 0 {
                    lean_ctor_set(v___x_559_, 0, v___x_563_);
                    v___x_566_ = v___x_559_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
                    v___x_566_ = v_reuseFailAlloc_567_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_566_;
            }
            4 => {
                v___x_575_ = l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2;
                v___x_576_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_576_, 0, v___x_575_);
                v___x_577_ = lean_unbox_uint64(v_val_571_);
                lean_dec(v_val_571_);
                lean_ctor_set_uint64(
                    v___x_576_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_577_,
                );
                if v_isShared_574_ == 0 {
                    lean_ctor_set(v___x_573_, 0, v___x_576_);
                    v___x_579_ = v___x_573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_576_);
                    v___x_579_ = v_reuseFailAlloc_580_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(
    mut v___x_589_: *mut LeanObject,
    mut v_s_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
    mut v_R_592_: *mut LeanObject,
    mut v_a_593_: *mut LeanObject,
    mut v_b_594_: *mut LeanObject,
    mut v_c_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_596_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(
            v___x_589_, v_s_590_, v_a_593_, v_b_594_,
        );
    return v___x_596_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___boxed(
    mut v___x_597_: *mut LeanObject,
    mut v_s_598_: *mut LeanObject,
    mut v_inst_599_: *mut LeanObject,
    mut v_R_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
    mut v_b_602_: *mut LeanObject,
    mut v_c_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_604_: *mut LeanObject = core::ptr::null_mut();
    v_res_604_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(
        v___x_597_,
        v_s_598_,
        v_inst_599_,
        v_R_600_,
        v_a_601_,
        v_b_602_,
        v_c_603_,
    );
    lean_dec(v_b_602_);
    lean_dec_ref(v_s_598_);
    lean_dec_ref(v___x_597_);
    return v_res_604_;
}
pub unsafe fn l_Lake_ArtifactDescr_fromJson_x3f(
    mut v_data_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_a_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_607_ = l_Lean_Json_getStr_x3f(v_data_606_);
                if lean_obj_tag(v___x_607_) == 0 {
                    v_a_608_ = lean_ctor_get(v___x_607_, 0);
                    v_isSharedCheck_617_ = (!lean_is_exclusive(v___x_607_)) as u8;
                    if v_isSharedCheck_617_ == 0 {
                        v___x_610_ = v___x_607_;
                        v_isShared_611_ = v_isSharedCheck_617_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_608_);
                        lean_dec(v___x_607_);
                        v___x_610_ = lean_box(0);
                        v_isShared_611_ = v_isSharedCheck_617_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_618_ = lean_ctor_get(v___x_607_, 0);
                    lean_inc(v_a_618_);
                    lean_dec_ref_known(v___x_607_, 1);
                    v___x_619_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_a_618_);
                    return v___x_619_;
                }
            }
            1 => {
                v___x_612_ = l_Lake_ArtifactDescr_fromJson_x3f___closed__0;
                v___x_613_ = lean_string_append(v___x_612_, v_a_608_);
                lean_dec(v_a_608_);
                if v_isShared_611_ == 0 {
                    lean_ctor_set(v___x_610_, 0, v___x_613_);
                    v___x_615_ = v___x_610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_instInhabitedArtifact_default___closed__0() -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = lean_unsigned_to_nat(0);
    v___x_623_ = lean_nat_to_int(v___x_622_);
    return v___x_623_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifact_default___closed__1() -> *mut LeanObject {
    let mut v___x_624_: u32 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = 0;
    v___x_625_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__0_once),
        _init_l_Lake_instInhabitedArtifact_default___closed__0,
    );
    v___x_626_ = lean_alloc_ctor(0, 1, (4) as u32);
    lean_ctor_set(v___x_626_, 0, v___x_625_);
    lean_ctor_set_uint32(
        v___x_626_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_624_,
    );
    return v___x_626_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifact_default___closed__2() -> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__1_once),
        _init_l_Lake_instInhabitedArtifact_default___closed__1,
    );
    v___x_628_ = l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2;
    v___x_629_ = l_Lake_instInhabitedArtifactDescr_default;
    v___x_630_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_630_, 0, v___x_629_);
    lean_ctor_set(v___x_630_, 1, v___x_628_);
    lean_ctor_set(v___x_630_, 2, v___x_628_);
    lean_ctor_set(v___x_630_, 3, v___x_627_);
    return v___x_630_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifact_default() -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedArtifact_default___closed__2_once),
        _init_l_Lake_instInhabitedArtifact_default___closed__2,
    );
    return v___x_631_;
}
pub unsafe fn _init_l_Lake_instInhabitedArtifact() -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    v___x_632_ = l_Lake_instInhabitedArtifact_default;
    return v___x_632_;
}
pub unsafe fn _init_l_Lake_instReprArtifact_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ = lean_unsigned_to_nat(9);
    v___x_643_ = lean_nat_to_int(v___x_642_);
    return v___x_643_;
}
pub unsafe fn l_Lake_instReprArtifact_repr___redArg(
    mut v_x_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_descr_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mtime_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v_descr_657_ = lean_ctor_get(v_x_656_, 0);
    lean_inc_ref(v_descr_657_);
    v_path_658_ = lean_ctor_get(v_x_656_, 1);
    lean_inc_ref(v_path_658_);
    v_name_659_ = lean_ctor_get(v_x_656_, 2);
    lean_inc_ref(v_name_659_);
    v_mtime_660_ = lean_ctor_get(v_x_656_, 3);
    lean_inc_ref(v_mtime_660_);
    lean_dec_ref(v_x_656_);
    v___x_661_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__5;
    v___x_662_ = l_Lake_instReprArtifact_repr___redArg___closed__3;
    v___x_663_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifact_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifact_repr___redArg___closed__4_once),
        _init_l_Lake_instReprArtifact_repr___redArg___closed__4,
    );
    v___x_664_ = lean_unsigned_to_nat(0);
    v___x_665_ = l_Lake_instReprArtifactDescr_repr___redArg(v_descr_657_);
    v___x_666_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_666_, 0, v___x_663_);
    lean_ctor_set(v___x_666_, 1, v___x_665_);
    v___x_667_ = 0;
    v___x_668_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_668_, 0, v___x_666_);
    lean_ctor_set_uint8(
        v___x_668_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_667_,
    );
    v___x_669_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_669_, 0, v___x_662_);
    lean_ctor_set(v___x_669_, 1, v___x_668_);
    v___x_670_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__9;
    v___x_671_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_671_, 0, v___x_669_);
    lean_ctor_set(v___x_671_, 1, v___x_670_);
    v___x_672_ = lean_box(1);
    v___x_673_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_673_, 0, v___x_671_);
    lean_ctor_set(v___x_673_, 1, v___x_672_);
    v___x_674_ = l_Lake_instReprArtifact_repr___redArg___closed__6;
    v___x_675_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_675_, 0, v___x_673_);
    lean_ctor_set(v___x_675_, 1, v___x_674_);
    v___x_676_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_676_, 0, v___x_675_);
    lean_ctor_set(v___x_676_, 1, v___x_661_);
    v___x_677_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7,
    );
    v___x_678_ = l_Lake_instReprArtifact_repr___redArg___closed__8;
    v___x_679_ = l_String_quote(v_path_658_);
    v___x_680_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_680_, 0, v___x_679_);
    v___x_681_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_681_, 0, v___x_678_);
    lean_ctor_set(v___x_681_, 1, v___x_680_);
    v___x_682_ = l_Repr_addAppParen(v___x_681_, v___x_664_);
    v___x_683_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_683_, 0, v___x_677_);
    lean_ctor_set(v___x_683_, 1, v___x_682_);
    v___x_684_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_684_, 0, v___x_683_);
    lean_ctor_set_uint8(
        v___x_684_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_667_,
    );
    v___x_685_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_685_, 0, v___x_676_);
    lean_ctor_set(v___x_685_, 1, v___x_684_);
    v___x_686_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_686_, 0, v___x_685_);
    lean_ctor_set(v___x_686_, 1, v___x_670_);
    v___x_687_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_687_, 0, v___x_686_);
    lean_ctor_set(v___x_687_, 1, v___x_672_);
    v___x_688_ = l_Lake_instReprArtifact_repr___redArg___closed__10;
    v___x_689_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_689_, 0, v___x_687_);
    lean_ctor_set(v___x_689_, 1, v___x_688_);
    v___x_690_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_690_, 0, v___x_689_);
    lean_ctor_set(v___x_690_, 1, v___x_661_);
    v___x_691_ = l_String_quote(v_name_659_);
    v___x_692_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_692_, 0, v___x_691_);
    v___x_693_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_693_, 0, v___x_677_);
    lean_ctor_set(v___x_693_, 1, v___x_692_);
    v___x_694_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_694_, 0, v___x_693_);
    lean_ctor_set_uint8(
        v___x_694_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_667_,
    );
    v___x_695_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_695_, 0, v___x_690_);
    lean_ctor_set(v___x_695_, 1, v___x_694_);
    v___x_696_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_696_, 0, v___x_695_);
    lean_ctor_set(v___x_696_, 1, v___x_670_);
    v___x_697_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_697_, 0, v___x_696_);
    lean_ctor_set(v___x_697_, 1, v___x_672_);
    v___x_698_ = l_Lake_instReprArtifact_repr___redArg___closed__12;
    v___x_699_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_699_, 0, v___x_697_);
    lean_ctor_set(v___x_699_, 1, v___x_698_);
    v___x_700_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_700_, 0, v___x_699_);
    lean_ctor_set(v___x_700_, 1, v___x_661_);
    v___x_701_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_660_);
    lean_dec_ref(v_mtime_660_);
    v___x_702_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_702_, 0, v___x_663_);
    lean_ctor_set(v___x_702_, 1, v___x_701_);
    v___x_703_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_703_, 0, v___x_702_);
    lean_ctor_set_uint8(
        v___x_703_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_667_,
    );
    v___x_704_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_704_, 0, v___x_700_);
    lean_ctor_set(v___x_704_, 1, v___x_703_);
    v___x_705_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once),
        _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15,
    );
    v___x_706_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__16;
    v___x_707_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_707_, 0, v___x_706_);
    lean_ctor_set(v___x_707_, 1, v___x_704_);
    v___x_708_ = l_Lake_instReprArtifactDescr_repr___redArg___closed__17;
    v___x_709_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_709_, 0, v___x_707_);
    lean_ctor_set(v___x_709_, 1, v___x_708_);
    v___x_710_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_710_, 0, v___x_705_);
    lean_ctor_set(v___x_710_, 1, v___x_709_);
    v___x_711_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_711_, 0, v___x_710_);
    lean_ctor_set_uint8(
        v___x_711_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_667_,
    );
    return v___x_711_;
}
pub unsafe fn l_Lake_instReprArtifact_repr(
    mut v_x_712_: *mut LeanObject,
    mut v_prec_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_714_ = l_Lake_instReprArtifact_repr___redArg(v_x_712_);
    return v___x_714_;
}
pub unsafe fn l_Lake_instReprArtifact_repr___boxed(
    mut v_x_715_: *mut LeanObject,
    mut v_prec_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lake_instReprArtifact_repr(v_x_715_, v_prec_716_);
    lean_dec(v_prec_716_);
    return v_res_717_;
}
pub unsafe fn l_Lake_Artifact_withName(
    mut v_name_720_: *mut LeanObject,
    mut v_self_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_descr_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mtime_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_727_: u8 = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut v_unused_732_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_descr_722_ = lean_ctor_get(v_self_721_, 0);
                v_path_723_ = lean_ctor_get(v_self_721_, 1);
                v_mtime_724_ = lean_ctor_get(v_self_721_, 3);
                v_isSharedCheck_731_ = (!lean_is_exclusive(v_self_721_)) as u8;
                if v_isSharedCheck_731_ == 0 {
                    v_unused_732_ = lean_ctor_get(v_self_721_, 2);
                    lean_dec(v_unused_732_);
                    v___x_726_ = v_self_721_;
                    v_isShared_727_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mtime_724_);
                    lean_inc(v_path_723_);
                    lean_inc(v_descr_722_);
                    lean_dec(v_self_721_);
                    v___x_726_ = lean_box(0);
                    v_isShared_727_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_727_ == 0 {
                    lean_ctor_set(v___x_726_, 2, v_name_720_);
                    v___x_729_ = v___x_726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_730_, 0, v_descr_722_);
                    lean_ctor_set(v_reuseFailAlloc_730_, 1, v_path_723_);
                    lean_ctor_set(v_reuseFailAlloc_730_, 2, v_name_720_);
                    lean_ctor_set(v_reuseFailAlloc_730_, 3, v_mtime_724_);
                    v___x_729_ = v_reuseFailAlloc_730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Artifact_useLocalFile(
    mut v_path_733_: *mut LeanObject,
    mut v_self_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_descr_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mtime_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_743_: u8 = 0;
    let mut v_unused_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_745_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_descr_735_ = lean_ctor_get(v_self_734_, 0);
                v_mtime_736_ = lean_ctor_get(v_self_734_, 3);
                v_isSharedCheck_743_ = (!lean_is_exclusive(v_self_734_)) as u8;
                if v_isSharedCheck_743_ == 0 {
                    v_unused_744_ = lean_ctor_get(v_self_734_, 2);
                    lean_dec(v_unused_744_);
                    v_unused_745_ = lean_ctor_get(v_self_734_, 1);
                    lean_dec(v_unused_745_);
                    v___x_738_ = v_self_734_;
                    v_isShared_739_ = v_isSharedCheck_743_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mtime_736_);
                    lean_inc(v_descr_735_);
                    lean_dec(v_self_734_);
                    v___x_738_ = lean_box(0);
                    v_isShared_739_ = v_isSharedCheck_743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_path_733_);
                if v_isShared_739_ == 0 {
                    lean_ctor_set(v___x_738_, 2, v_path_733_);
                    lean_ctor_set(v___x_738_, 1, v_path_733_);
                    v___x_741_ = v___x_738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_742_, 0, v_descr_735_);
                    lean_ctor_set(v_reuseFailAlloc_742_, 1, v_path_733_);
                    lean_ctor_set(v_reuseFailAlloc_742_, 2, v_path_733_);
                    lean_ctor_set(v_reuseFailAlloc_742_, 3, v_mtime_736_);
                    v___x_741_ = v_reuseFailAlloc_742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Artifact_trace(mut v_self_748_: *mut LeanObject) -> *mut LeanObject {
    let mut v_descr_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mtime_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_752_: u64 = 0;
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v_descr_749_ = lean_ctor_get(v_self_748_, 0);
    v_name_750_ = lean_ctor_get(v_self_748_, 2);
    v_mtime_751_ = lean_ctor_get(v_self_748_, 3);
    v_hash_752_ = lean_ctor_get_uint64(
        v_descr_749_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_753_ = l_Lake_Artifact_trace___closed__0;
    lean_inc_ref(v_mtime_751_);
    lean_inc_ref(v_name_750_);
    v___x_754_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_754_, 0, v_name_750_);
    lean_ctor_set(v___x_754_, 1, v___x_753_);
    lean_ctor_set(v___x_754_, 2, v_mtime_751_);
    lean_ctor_set_uint64(
        v___x_754_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_hash_752_,
    );
    return v___x_754_;
}
pub unsafe fn l_Lake_Artifact_trace___boxed(mut v_self_755_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lake_Artifact_trace(v_self_755_);
    lean_dec_ref(v_self_755_);
    return v_res_756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Artifact(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedArtifactDescr_default = _init_l_Lake_instInhabitedArtifactDescr_default();
    lean_mark_persistent(l_Lake_instInhabitedArtifactDescr_default);
    l_Lake_instInhabitedArtifactDescr = _init_l_Lake_instInhabitedArtifactDescr();
    lean_mark_persistent(l_Lake_instInhabitedArtifactDescr);
    l_Lake_instInhabitedArtifact_default = _init_l_Lake_instInhabitedArtifact_default();
    lean_mark_persistent(l_Lake_instInhabitedArtifact_default);
    l_Lake_instInhabitedArtifact = _init_l_Lake_instInhabitedArtifact();
    lean_mark_persistent(l_Lake_instInhabitedArtifact);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Artifact(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Artifact(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Artifact(builtin);
}
