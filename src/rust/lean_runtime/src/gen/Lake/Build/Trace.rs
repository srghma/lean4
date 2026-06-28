// Lean compiler output
// Module: Lake.Build.Trace
// Imports: Lean.Data.Json Init.Data.Nat.Fold Init.Data.Nat.Fold Lake.Util.String Init.Data.String.Search Init.Data.String.Extra Init.Data.Option.Coe
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::List::Control::l_List_foldlM___redArg;
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, meta_initialize_Init_Data_Nat_Fold,
    runtime_initialize_Init_Data_Nat_Fold,
};
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::String::Extra::{
    initialize_Init_Data_String_Extra, l_String_crlfToLf, runtime_initialize_Init_Data_String_Extra,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toNat_x3f;
use crate::r#gen::Init::Prelude::{l_List_foldl___redArg, l_instMonadLiftT___lam__0___boxed};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_instBEqSystemTime_beq, l_IO_FS_instOrdSystemTime_ord,
    l_IO_FS_instReprSystemTime_repr___redArg, l_IO_FS_readBinFile, l_IO_FS_readFile,
    l_System_FilePath_pathExists___boxed,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, l_Lake_isHex, l_Lake_lowerHexUInt64,
    runtime_initialize_Lake_Util_String,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_hash;
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_dec_le, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_sub, lean_uint64_add, lean_uint64_shift_left,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_uint64, lean_uint64_of_nat, lean_uint64_to_nat, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_hash,
    lean_string_utf8_byte_size, lean_uint8_dec_le, lean_uint64_dec_eq, lean_uint64_mix_hash,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_metadata;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_uint64, lean_closure_set,
    lean_cstr_to_nat, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_Lake_instCheckExistsFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_System_FilePath_pathExists___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCheckExistsFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCheckExistsFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCheckExistsFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCheckExistsFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_mixTraceArray___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_mixTraceArray___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_mixTraceArray___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_mixTraceArray___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instComputeTraceListOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lake_instReprHash_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__1_value: LeanStringObject<4> =
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
        m_data: [118, 97, 108, 0],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lake_instReprHash_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lake_instReprHash_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprHash_repr___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprHash_repr___redArg___closed__8_value: LeanStringObject<3> =
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
static mut l_Lake_instReprHash_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lake_instReprHash_repr___redArg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprHash_repr___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprHash_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprHash_repr___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprHash_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__11_value) as *mut LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__12_value) as *mut LeanObject;
pub static l_Lake_instReprHash___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprHash_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprHash___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprHash: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash___closed__0_value) as *mut LeanObject;
pub static l_Lake_Hash_instHashable___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Hash_instHashable___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Hash_instHashable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_instHashable: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_nil: u64 = 0;
pub static mut l_Lake_Hash_instNilTrace: u64 = 0;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__0_value: LeanStringObject<24> =
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
            110, 117, 109, 98, 101, 114, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 110, 97, 116,
            117, 114, 97, 108, 0,
        ],
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__3_value: LeanStringObject<15> =
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
            110, 117, 109, 98, 101, 114, 32, 116, 111, 111, 32, 98, 105, 103, 0,
        ],
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__4_value) as *mut LeanObject;
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Hash_instMixTrace___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Hash_mix___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Hash_instMixTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instMixTrace___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_instMixTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instMixTrace___closed__0_value) as *mut LeanObject;
pub static l_Lake_Hash_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Hash_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Hash_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToString___closed__0_value) as *mut LeanObject;
static mut l_Lake_Hash_ofBool___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Hash_ofBool___closed__0: u64 = 0;
static mut l_Lake_Hash_ofBool___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Hash_ofBool___closed__1: u64 = 0;
pub static l_Lake_Hash_instToJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Hash_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Hash_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__0_value: LeanStringObject<42> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101, 99,
        116, 101, 100, 32, 104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 115, 116, 114,
        105, 110, 103, 0,
    ],
};
static mut l_Lake_Hash_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_Hash_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__2_value: LeanStringObject<55> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101, 99,
        116, 101, 100, 32, 104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 115, 116, 114,
        105, 110, 103, 32, 111, 102, 32, 108, 101, 110, 103, 116, 104, 32, 49, 54, 0,
    ],
};
static mut l_Lake_Hash_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_Hash_fromJson_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__4_value: LeanStringObject<15> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 0,
    ],
};
static mut l_Lake_Hash_fromJson_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__5_value: LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101, 99,
        116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32, 110, 117, 109, 98, 101,
        114, 0,
    ],
};
static mut l_Lake_Hash_fromJson_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_Hash_fromJson_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lake_Hash_instFromJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Hash_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Hash_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Hash_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instComputeHashFilePathIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_computeBinFileHash___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instComputeHashFilePathIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashFilePathIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instComputeHashFilePathIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashFilePathIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_instCoeTextFilePathFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeTextFilePathFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeTextFilePathFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCoeTextFilePathFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instComputeHashTextFilePathIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_computeTextFileHash___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instComputeHashTextFilePathIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashTextFilePathIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instComputeHashTextFilePathIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashTextFilePathIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToStringTextFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_computeArrayHash___redArg___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [1723 as *mut LeanObject],
    };
pub static mut l_Lake_computeArrayHash___redArg___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_computeArrayHash___redArg___boxed__const__1_value)
        as *mut LeanObject;
static mut l_Lake_MTime_instOfNat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_MTime_instOfNat___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MTime_instOfNat: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_MTime_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MTime_instBEq___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MTime_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instBEq___closed__0_value) as *mut LeanObject;
pub static l_Lake_MTime_instRepr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MTime_instRepr___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MTime_instRepr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instRepr___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instRepr: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instRepr___closed__0_value) as *mut LeanObject;
pub static l_Lake_MTime_instOrd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MTime_instOrd___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MTime_instOrd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instOrd___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instOrd: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instOrd___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MTime_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_MTime_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MTime_instMin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MTime_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMin___closed__0_value) as *mut LeanObject;
pub static l_Lake_MTime_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MTime_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MTime_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MTime_instNilTrace: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MTime_instMixTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut LeanObject;
pub static l_Lake_instGetMTimeFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getFileMTime___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instGetMTimeFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instGetMTimeFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instGetMTimeTextFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instGetMTimeTextFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instGetMTimeTextFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeTextFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instGetMTimeTextFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeTextFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 97, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
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
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value
)
    as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__5_value: LeanStringObject<7> =
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
        m_data: [105, 110, 112, 117, 116, 115, 0],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value
)
    as *mut LeanObject;
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value:
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
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value
) as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__8_value: LeanStringObject<5> =
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__11_value: LeanStringObject<6> =
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildTrace___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprBuildTrace_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprBuildTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprBuildTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildTrace_withoutInputs___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_BuildTrace_withoutInputs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_withoutInputs___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value: LeanStringObject<7> =
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
        m_data: [60, 104, 97, 115, 104, 62, 0],
    };
static mut l_Lake_BuildTrace_instCoeHash___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_BuildTrace_instCoeHash___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildTrace_instCoeHash___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instCoeHash___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildTrace_instCoeHash: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value: LeanStringObject<8> =
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
        m_data: [60, 109, 116, 105, 109, 101, 62, 0],
    };
static mut l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_BuildTrace_instCoeMTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildTrace_instCoeMTime___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instCoeMTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildTrace_instCoeMTime: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildTrace_instNilTrace___closed__0_value: LeanStringObject<6> =
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
        m_data: [60, 110, 105, 108, 62, 0],
    };
static mut l_Lake_BuildTrace_instNilTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instNilTrace___closed__0_value) as *mut LeanObject;
static mut l_Lake_BuildTrace_instNilTrace___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_BuildTrace_instNilTrace___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_BuildTrace_instNilTrace: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_BuildTrace_instMixTrace___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildTrace_mix as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instMixTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instMixTrace___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildTrace_instMixTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instMixTrace___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_computeTrace___redArg(
    mut v_inst_1282_: *mut LeanObject,
    mut v_inst_1283_: *mut LeanObject,
    mut v_a_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = lean_apply_1(v_inst_1282_, v_a_1284_);
    v___x_1286_ = lean_apply_2(v_inst_1283_, lean_box(0), v___x_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lake_computeTrace(
    mut v_00_u03b1_1287_: *mut LeanObject,
    mut v_m_1288_: *mut LeanObject,
    mut v_00_u03c4_1289_: *mut LeanObject,
    mut v_n_1290_: *mut LeanObject,
    mut v_inst_1291_: *mut LeanObject,
    mut v_inst_1292_: *mut LeanObject,
    mut v_a_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_apply_1(v_inst_1291_, v_a_1293_);
    v___x_1295_ = lean_apply_2(v_inst_1292_, lean_box(0), v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___redArg(
    mut v_inst_1296_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1296_);
    return v_inst_1296_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___redArg___boxed(
    mut v_inst_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1298_: *mut LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lake_inhabitedOfNilTrace___redArg(v_inst_1297_);
    lean_dec(v_inst_1297_);
    return v_res_1298_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace(
    mut v_00_u03b1_1299_: *mut LeanObject,
    mut v_inst_1300_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1300_);
    return v_inst_1300_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___boxed(
    mut v_00_u03b1_1301_: *mut LeanObject,
    mut v_inst_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1303_: *mut LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Lake_inhabitedOfNilTrace(v_00_u03b1_1301_, v_inst_1302_);
    lean_dec(v_inst_1302_);
    return v_res_1303_;
}
pub unsafe fn l_Lake_mixTraceList___redArg(
    mut v_inst_1304_: *mut LeanObject,
    mut v_inst_1305_: *mut LeanObject,
    mut v_traces_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = l_List_foldl___redArg(v_inst_1304_, v_inst_1305_, v_traces_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Lake_mixTraceList(
    mut v_00_u03c4_1308_: *mut LeanObject,
    mut v_inst_1309_: *mut LeanObject,
    mut v_inst_1310_: *mut LeanObject,
    mut v_traces_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_List_foldl___redArg(v_inst_1309_, v_inst_1310_, v_traces_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Lake_mixTraceArray___redArg___lam__0(
    mut v_inst_1313_: *mut LeanObject,
    mut v_x1_1314_: *mut LeanObject,
    mut v_x2_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = lean_apply_2(v_inst_1313_, v_x1_1314_, v_x2_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Lake_mixTraceArray___redArg(
    mut v_inst_1336_: *mut LeanObject,
    mut v_inst_1337_: *mut LeanObject,
    mut v_traces_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    v___x_1339_ = lean_unsigned_to_nat(0);
    v___x_1340_ = lean_array_get_size(v_traces_1338_);
    v___x_1341_ = l_Lake_mixTraceArray___redArg___closed__9;
    v___x_1342_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
    if v___x_1342_ == 0 {
        lean_dec_ref(v_traces_1338_);
        lean_dec(v_inst_1336_);
        return v_inst_1337_;
    } else {
        let mut v___f_1343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: u8 = 0;
        v___f_1343_ = lean_alloc_closure(
            l_Lake_mixTraceArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1343_, 0, v_inst_1336_);
        v___x_1344_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
        if v___x_1344_ == 0 {
            if v___x_1342_ == 0 {
                lean_dec_ref(v___f_1343_);
                lean_dec_ref(v_traces_1338_);
                return v_inst_1337_;
            } else {
                let mut v___x_1345_: usize = 0;
                let mut v___x_1346_: usize = 0;
                let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
                v___x_1345_ = 0usize;
                v___x_1346_ = lean_usize_of_nat(v___x_1340_);
                v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1341_,
                    v___f_1343_,
                    v_traces_1338_,
                    v___x_1345_,
                    v___x_1346_,
                    v_inst_1337_,
                );
                return v___x_1347_;
            }
        } else {
            let mut v___x_1348_: usize = 0;
            let mut v___x_1349_: usize = 0;
            let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
            v___x_1348_ = 0usize;
            v___x_1349_ = lean_usize_of_nat(v___x_1340_);
            v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_1341_,
                v___f_1343_,
                v_traces_1338_,
                v___x_1348_,
                v___x_1349_,
                v_inst_1337_,
            );
            return v___x_1350_;
        }
    }
}
pub unsafe fn l_Lake_mixTraceArray(
    mut v_00_u03c4_1351_: *mut LeanObject,
    mut v_inst_1352_: *mut LeanObject,
    mut v_inst_1353_: *mut LeanObject,
    mut v_traces_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lake_mixTraceArray___redArg(v_inst_1352_, v_inst_1353_, v_traces_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Lake_computeListTrace___redArg___lam__0(
    mut v_inst_1356_: *mut LeanObject,
    mut v_ts_1357_: *mut LeanObject,
    mut v_toPure_1358_: *mut LeanObject,
    mut v_____do__lift_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = lean_apply_2(v_inst_1356_, v_ts_1357_, v_____do__lift_1359_);
    v___x_1361_ = lean_apply_2(v_toPure_1358_, lean_box(0), v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn l_Lake_computeListTrace___redArg___lam__1(
    mut v_inst_1362_: *mut LeanObject,
    mut v_toPure_1363_: *mut LeanObject,
    mut v_inst_1364_: *mut LeanObject,
    mut v_inst_1365_: *mut LeanObject,
    mut v_toBind_1366_: *mut LeanObject,
    mut v_ts_1367_: *mut LeanObject,
    mut v_t_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___f_1369_ = lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1369_, 0, v_inst_1362_);
    lean_closure_set(v___f_1369_, 1, v_ts_1367_);
    lean_closure_set(v___f_1369_, 2, v_toPure_1363_);
    v___x_1370_ = lean_apply_1(v_inst_1364_, v_t_1368_);
    v___x_1371_ = lean_apply_2(v_inst_1365_, lean_box(0), v___x_1370_);
    v___x_1372_ = lean_apply_4(
        v_toBind_1366_,
        lean_box(0),
        lean_box(0),
        v___x_1371_,
        v___f_1369_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lake_computeListTrace___redArg(
    mut v_inst_1373_: *mut LeanObject,
    mut v_inst_1374_: *mut LeanObject,
    mut v_inst_1375_: *mut LeanObject,
    mut v_inst_1376_: *mut LeanObject,
    mut v_inst_1377_: *mut LeanObject,
    mut v_as_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1379_ = lean_ctor_get(v_inst_1377_, 0);
    v_toBind_1380_ = lean_ctor_get(v_inst_1377_, 1);
    v_toPure_1381_ = lean_ctor_get(v_toApplicative_1379_, 1);
    lean_inc(v_toBind_1380_);
    lean_inc(v_toPure_1381_);
    v___f_1382_ = lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_1382_, 0, v_inst_1373_);
    lean_closure_set(v___f_1382_, 1, v_toPure_1381_);
    lean_closure_set(v___f_1382_, 2, v_inst_1375_);
    lean_closure_set(v___f_1382_, 3, v_inst_1376_);
    lean_closure_set(v___f_1382_, 4, v_toBind_1380_);
    v___x_1383_ = l_List_foldlM___redArg(v_inst_1377_, v___f_1382_, v_inst_1374_, v_as_1378_);
    return v___x_1383_;
}
pub unsafe fn l_Lake_computeListTrace(
    mut v_00_u03c4_1384_: *mut LeanObject,
    mut v_00_u03b1_1385_: *mut LeanObject,
    mut v_m_1386_: *mut LeanObject,
    mut v_inst_1387_: *mut LeanObject,
    mut v_inst_1388_: *mut LeanObject,
    mut v_inst_1389_: *mut LeanObject,
    mut v_n_1390_: *mut LeanObject,
    mut v_inst_1391_: *mut LeanObject,
    mut v_inst_1392_: *mut LeanObject,
    mut v_as_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1394_ = lean_ctor_get(v_inst_1392_, 0);
    v_toBind_1395_ = lean_ctor_get(v_inst_1392_, 1);
    v_toPure_1396_ = lean_ctor_get(v_toApplicative_1394_, 1);
    lean_inc(v_toBind_1395_);
    lean_inc(v_toPure_1396_);
    v___f_1397_ = lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_1397_, 0, v_inst_1387_);
    lean_closure_set(v___f_1397_, 1, v_toPure_1396_);
    lean_closure_set(v___f_1397_, 2, v_inst_1389_);
    lean_closure_set(v___f_1397_, 3, v_inst_1391_);
    lean_closure_set(v___f_1397_, 4, v_toBind_1395_);
    v___x_1398_ = l_List_foldlM___redArg(v_inst_1392_, v___f_1397_, v_inst_1388_, v_as_1393_);
    return v___x_1398_;
}
pub unsafe fn l_Lake_instComputeTraceListOfMonad___redArg(
    mut v_inst_1400_: *mut LeanObject,
    mut v_inst_1401_: *mut LeanObject,
    mut v_inst_1402_: *mut LeanObject,
    mut v_inst_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___f_1404_ = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
    v___x_1405_ = lean_alloc_closure(l_Lake_computeListTrace as *mut core::ffi::c_void, 10, 9);
    lean_closure_set(v___x_1405_, 0, lean_box(0));
    lean_closure_set(v___x_1405_, 1, lean_box(0));
    lean_closure_set(v___x_1405_, 2, lean_box(0));
    lean_closure_set(v___x_1405_, 3, v_inst_1400_);
    lean_closure_set(v___x_1405_, 4, v_inst_1401_);
    lean_closure_set(v___x_1405_, 5, v_inst_1402_);
    lean_closure_set(v___x_1405_, 6, lean_box(0));
    lean_closure_set(v___x_1405_, 7, v___f_1404_);
    lean_closure_set(v___x_1405_, 8, v_inst_1403_);
    return v___x_1405_;
}
pub unsafe fn l_Lake_instComputeTraceListOfMonad(
    mut v_00_u03c4_1406_: *mut LeanObject,
    mut v_00_u03b1_1407_: *mut LeanObject,
    mut v_m_1408_: *mut LeanObject,
    mut v_inst_1409_: *mut LeanObject,
    mut v_inst_1410_: *mut LeanObject,
    mut v_inst_1411_: *mut LeanObject,
    mut v_inst_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ = l_Lake_instComputeTraceListOfMonad___redArg(
        v_inst_1409_,
        v_inst_1410_,
        v_inst_1411_,
        v_inst_1412_,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lake_computeArrayTrace___redArg(
    mut v_inst_1414_: *mut LeanObject,
    mut v_inst_1415_: *mut LeanObject,
    mut v_inst_1416_: *mut LeanObject,
    mut v_inst_1417_: *mut LeanObject,
    mut v_inst_1418_: *mut LeanObject,
    mut v_as_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    v_toApplicative_1420_ = lean_ctor_get(v_inst_1418_, 0);
    v_toBind_1421_ = lean_ctor_get(v_inst_1418_, 1);
    v_toPure_1422_ = lean_ctor_get(v_toApplicative_1420_, 1);
    v___x_1423_ = lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_as_1419_);
    v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1425_ == 0 {
        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1422_);
        lean_dec_ref(v_as_1419_);
        lean_dec_ref(v_inst_1418_);
        lean_dec(v_inst_1417_);
        lean_dec(v_inst_1416_);
        lean_dec(v_inst_1414_);
        v___x_1426_ = lean_apply_2(v_toPure_1422_, lean_box(0), v_inst_1415_);
        return v___x_1426_;
    } else {
        let mut v___f_1427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: u8 = 0;
        lean_inc(v_toBind_1421_);
        lean_inc(v_toPure_1422_);
        v___f_1427_ = lean_alloc_closure(
            l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
            7,
            5,
        );
        lean_closure_set(v___f_1427_, 0, v_inst_1414_);
        lean_closure_set(v___f_1427_, 1, v_toPure_1422_);
        lean_closure_set(v___f_1427_, 2, v_inst_1416_);
        lean_closure_set(v___f_1427_, 3, v_inst_1417_);
        lean_closure_set(v___f_1427_, 4, v_toBind_1421_);
        v___x_1428_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
        if v___x_1428_ == 0 {
            if v___x_1425_ == 0 {
                let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1422_);
                lean_dec_ref(v___f_1427_);
                lean_dec_ref(v_as_1419_);
                lean_dec_ref(v_inst_1418_);
                v___x_1429_ = lean_apply_2(v_toPure_1422_, lean_box(0), v_inst_1415_);
                return v___x_1429_;
            } else {
                let mut v___x_1430_: usize = 0;
                let mut v___x_1431_: usize = 0;
                let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
                v___x_1430_ = 0usize;
                v___x_1431_ = lean_usize_of_nat(v___x_1424_);
                v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_1418_,
                    v___f_1427_,
                    v_as_1419_,
                    v___x_1430_,
                    v___x_1431_,
                    v_inst_1415_,
                );
                return v___x_1432_;
            }
        } else {
            let mut v___x_1433_: usize = 0;
            let mut v___x_1434_: usize = 0;
            let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
            v___x_1433_ = 0usize;
            v___x_1434_ = lean_usize_of_nat(v___x_1424_);
            v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_1418_,
                v___f_1427_,
                v_as_1419_,
                v___x_1433_,
                v___x_1434_,
                v_inst_1415_,
            );
            return v___x_1435_;
        }
    }
}
pub unsafe fn l_Lake_computeArrayTrace(
    mut v_00_u03c4_1436_: *mut LeanObject,
    mut v_00_u03b1_1437_: *mut LeanObject,
    mut v_m_1438_: *mut LeanObject,
    mut v_inst_1439_: *mut LeanObject,
    mut v_inst_1440_: *mut LeanObject,
    mut v_inst_1441_: *mut LeanObject,
    mut v_n_1442_: *mut LeanObject,
    mut v_inst_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_as_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    v_toApplicative_1446_ = lean_ctor_get(v_inst_1444_, 0);
    v_toBind_1447_ = lean_ctor_get(v_inst_1444_, 1);
    v_toPure_1448_ = lean_ctor_get(v_toApplicative_1446_, 1);
    v___x_1449_ = lean_unsigned_to_nat(0);
    v___x_1450_ = lean_array_get_size(v_as_1445_);
    v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
    if v___x_1451_ == 0 {
        let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1448_);
        lean_dec_ref(v_as_1445_);
        lean_dec_ref(v_inst_1444_);
        lean_dec(v_inst_1443_);
        lean_dec(v_inst_1441_);
        lean_dec(v_inst_1439_);
        v___x_1452_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_inst_1440_);
        return v___x_1452_;
    } else {
        let mut v___f_1453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: u8 = 0;
        lean_inc(v_toBind_1447_);
        lean_inc(v_toPure_1448_);
        v___f_1453_ = lean_alloc_closure(
            l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
            7,
            5,
        );
        lean_closure_set(v___f_1453_, 0, v_inst_1439_);
        lean_closure_set(v___f_1453_, 1, v_toPure_1448_);
        lean_closure_set(v___f_1453_, 2, v_inst_1441_);
        lean_closure_set(v___f_1453_, 3, v_inst_1443_);
        lean_closure_set(v___f_1453_, 4, v_toBind_1447_);
        v___x_1454_ = lean_nat_dec_le(v___x_1450_, v___x_1450_);
        if v___x_1454_ == 0 {
            if v___x_1451_ == 0 {
                let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1448_);
                lean_dec_ref(v___f_1453_);
                lean_dec_ref(v_as_1445_);
                lean_dec_ref(v_inst_1444_);
                v___x_1455_ = lean_apply_2(v_toPure_1448_, lean_box(0), v_inst_1440_);
                return v___x_1455_;
            } else {
                let mut v___x_1456_: usize = 0;
                let mut v___x_1457_: usize = 0;
                let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
                v___x_1456_ = 0usize;
                v___x_1457_ = lean_usize_of_nat(v___x_1450_);
                v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_1444_,
                    v___f_1453_,
                    v_as_1445_,
                    v___x_1456_,
                    v___x_1457_,
                    v_inst_1440_,
                );
                return v___x_1458_;
            }
        } else {
            let mut v___x_1459_: usize = 0;
            let mut v___x_1460_: usize = 0;
            let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
            v___x_1459_ = 0usize;
            v___x_1460_ = lean_usize_of_nat(v___x_1450_);
            v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_1444_,
                v___f_1453_,
                v_as_1445_,
                v___x_1459_,
                v___x_1460_,
                v_inst_1440_,
            );
            return v___x_1461_;
        }
    }
}
pub unsafe fn l_Lake_instComputeTraceArrayOfMonad___redArg(
    mut v_inst_1462_: *mut LeanObject,
    mut v_inst_1463_: *mut LeanObject,
    mut v_inst_1464_: *mut LeanObject,
    mut v_inst_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___f_1466_ = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
    v___x_1467_ = lean_alloc_closure(l_Lake_computeArrayTrace as *mut core::ffi::c_void, 10, 9);
    lean_closure_set(v___x_1467_, 0, lean_box(0));
    lean_closure_set(v___x_1467_, 1, lean_box(0));
    lean_closure_set(v___x_1467_, 2, lean_box(0));
    lean_closure_set(v___x_1467_, 3, v_inst_1462_);
    lean_closure_set(v___x_1467_, 4, v_inst_1463_);
    lean_closure_set(v___x_1467_, 5, v_inst_1464_);
    lean_closure_set(v___x_1467_, 6, lean_box(0));
    lean_closure_set(v___x_1467_, 7, v___f_1466_);
    lean_closure_set(v___x_1467_, 8, v_inst_1465_);
    return v___x_1467_;
}
pub unsafe fn l_Lake_instComputeTraceArrayOfMonad(
    mut v_00_u03c4_1468_: *mut LeanObject,
    mut v_00_u03b1_1469_: *mut LeanObject,
    mut v_m_1470_: *mut LeanObject,
    mut v_inst_1471_: *mut LeanObject,
    mut v_inst_1472_: *mut LeanObject,
    mut v_inst_1473_: *mut LeanObject,
    mut v_inst_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lake_instComputeTraceArrayOfMonad___redArg(
        v_inst_1471_,
        v_inst_1472_,
        v_inst_1473_,
        v_inst_1474_,
    );
    return v___x_1475_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(
    mut v_a_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    v___x_1477_ = lean_nat_to_int(v_a_1476_);
    return v___x_1477_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1491_ = lean_unsigned_to_nat(7);
    v___x_1492_ = lean_nat_to_int(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lake_instReprHash_repr___redArg___closed__0;
    v___x_1495_ = lean_string_length(v___x_1494_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__9_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__9,
    );
    v___x_1497_ = lean_nat_to_int(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_instReprHash_repr___redArg(mut v_x_1502_: u64) -> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lake_instReprHash_repr___redArg___closed__6;
    v___x_1504_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__7_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__7,
    );
    v___x_1505_ = lean_uint64_to_nat(v_x_1502_);
    v___x_1506_ = l_Nat_reprFast(v___x_1505_);
    v___x_1507_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    v___x_1508_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1508_, 0, v___x_1504_);
    lean_ctor_set(v___x_1508_, 1, v___x_1507_);
    v___x_1509_ = 0;
    v___x_1510_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1510_, 0, v___x_1508_);
    lean_ctor_set_uint8(
        v___x_1510_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1509_,
    );
    v___x_1511_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1511_, 0, v___x_1503_);
    lean_ctor_set(v___x_1511_, 1, v___x_1510_);
    v___x_1512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__10,
    );
    v___x_1513_ = l_Lake_instReprHash_repr___redArg___closed__11;
    v___x_1514_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    lean_ctor_set(v___x_1514_, 1, v___x_1511_);
    v___x_1515_ = l_Lake_instReprHash_repr___redArg___closed__12;
    v___x_1516_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1516_, 0, v___x_1514_);
    lean_ctor_set(v___x_1516_, 1, v___x_1515_);
    v___x_1517_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1517_, 0, v___x_1512_);
    lean_ctor_set(v___x_1517_, 1, v___x_1516_);
    v___x_1518_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    lean_ctor_set_uint8(
        v___x_1518_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1509_,
    );
    return v___x_1518_;
}
pub unsafe fn l_Lake_instReprHash_repr___redArg___boxed(
    mut v_x_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_147__boxed_1520_: u64 = 0;
    let mut v_res_1521_: *mut LeanObject = core::ptr::null_mut();
    v_x_147__boxed_1520_ = lean_unbox_uint64(v_x_1519_);
    lean_dec_ref(v_x_1519_);
    v_res_1521_ = l_Lake_instReprHash_repr___redArg(v_x_147__boxed_1520_);
    return v_res_1521_;
}
pub unsafe fn l_Lake_instReprHash_repr(
    mut v_x_1522_: u64,
    mut v_prec_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lake_instReprHash_repr___redArg(v_x_1522_);
    return v___x_1524_;
}
pub unsafe fn l_Lake_instReprHash_repr___boxed(
    mut v_x_1525_: *mut LeanObject,
    mut v_prec_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_206__boxed_1527_: u64 = 0;
    let mut v_res_1528_: *mut LeanObject = core::ptr::null_mut();
    v_x_206__boxed_1527_ = lean_unbox_uint64(v_x_1525_);
    lean_dec_ref(v_x_1525_);
    v_res_1528_ = l_Lake_instReprHash_repr(v_x_206__boxed_1527_, v_prec_1526_);
    lean_dec(v_prec_1526_);
    return v_res_1528_;
}
pub unsafe fn l_Lake_instDecidableEqHash_decEq(mut v_x_1531_: u64, mut v_x_1532_: u64) -> u8 {
    let mut v___x_1533_: u8 = 0;
    v___x_1533_ = lean_uint64_dec_eq(v_x_1531_, v_x_1532_);
    return v___x_1533_;
}
pub unsafe fn l_Lake_instDecidableEqHash_decEq___boxed(
    mut v_x_1534_: *mut LeanObject,
    mut v_x_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_25__boxed_1536_: u64 = 0;
    let mut v_x_26__boxed_1537_: u64 = 0;
    let mut v_res_1538_: u8 = 0;
    let mut v_r_1539_: *mut LeanObject = core::ptr::null_mut();
    v_x_25__boxed_1536_ = lean_unbox_uint64(v_x_1534_);
    lean_dec_ref(v_x_1534_);
    v_x_26__boxed_1537_ = lean_unbox_uint64(v_x_1535_);
    lean_dec_ref(v_x_1535_);
    v_res_1538_ = l_Lake_instDecidableEqHash_decEq(v_x_25__boxed_1536_, v_x_26__boxed_1537_);
    v_r_1539_ = lean_box((v_res_1538_) as usize);
    return v_r_1539_;
}
pub unsafe fn l_Lake_instDecidableEqHash(mut v_x_1540_: u64, mut v_x_1541_: u64) -> u8 {
    let mut v___x_1542_: u8 = 0;
    v___x_1542_ = lean_uint64_dec_eq(v_x_1540_, v_x_1541_);
    return v___x_1542_;
}
pub unsafe fn l_Lake_instDecidableEqHash___boxed(
    mut v_x_1543_: *mut LeanObject,
    mut v_x_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6__boxed_1545_: u64 = 0;
    let mut v_x_7__boxed_1546_: u64 = 0;
    let mut v_res_1547_: u8 = 0;
    let mut v_r_1548_: *mut LeanObject = core::ptr::null_mut();
    v_x_6__boxed_1545_ = lean_unbox_uint64(v_x_1543_);
    lean_dec_ref(v_x_1543_);
    v_x_7__boxed_1546_ = lean_unbox_uint64(v_x_1544_);
    lean_dec_ref(v_x_1544_);
    v_res_1547_ = l_Lake_instDecidableEqHash(v_x_6__boxed_1545_, v_x_7__boxed_1546_);
    v_r_1548_ = lean_box((v_res_1547_) as usize);
    return v_r_1548_;
}
pub unsafe fn l_Lake_Hash_instHashable___lam__0(mut v_self_1549_: u64) -> u64 {
    return v_self_1549_;
}
pub unsafe fn l_Lake_Hash_instHashable___lam__0___boxed(
    mut v_self_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_self_boxed_1551_: u64 = 0;
    let mut v_res_1552_: u64 = 0;
    let mut v_r_1553_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_1551_ = lean_unbox_uint64(v_self_1550_);
    lean_dec_ref(v_self_1550_);
    v_res_1552_ = l_Lake_Hash_instHashable___lam__0(v_self_boxed_1551_);
    v_r_1553_ = lean_box_uint64(v_res_1552_);
    return v_r_1553_;
}
pub unsafe fn _init_l_Lake_Hash_nil() -> u64 {
    let mut v___x_1556_: u64 = 0;
    v___x_1556_ = 1723u64;
    return v___x_1556_;
}
pub unsafe fn _init_l_Lake_Hash_instNilTrace() -> u64 {
    let mut v___x_1557_: u64 = 0;
    v___x_1557_ = 1723u64;
    return v___x_1557_;
}
pub unsafe fn l_Lake_Hash_ofNat(mut v_n_1558_: *mut LeanObject) -> u64 {
    let mut v___x_1559_: u64 = 0;
    v___x_1559_ = lean_uint64_of_nat(v_n_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_Hash_ofNat___boxed(mut v_n_1560_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1561_: u64 = 0;
    let mut v_r_1562_: *mut LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lake_Hash_ofNat(v_n_1560_);
    lean_dec(v_n_1560_);
    v_r_1562_ = lean_box_uint64(v_res_1561_);
    return v_r_1562_;
}
pub unsafe fn _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_1566_;
}
pub unsafe fn _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1570_ = lean_unsigned_to_nat(0);
    v___x_1571_ = lean_nat_to_int(v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lake_Hash_ofJsonNumber_x3f(mut v_n_1572_: *mut LeanObject) -> *mut LeanObject {
    let mut v_mantissa_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u64 = 0;
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1573_ = lean_ctor_get(v_n_1572_, 0);
                v_exponent_1574_ = lean_ctor_get(v_n_1572_, 1);
                v___x_1585_ = lean_unsigned_to_nat(0);
                v___x_1586_ = lean_nat_dec_eq(v_exponent_1574_, v___x_1585_);
                if v___x_1586_ == 0 {
                    v___y_1576_ = v___x_1586_;
                    state = 1;
                    continue;
                } else {
                    v___x_1587_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5),
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5_once),
                        _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5,
                    );
                    v___x_1588_ = lean_int_dec_le(v___x_1587_, v_mantissa_1573_);
                    v___y_1576_ = v___x_1588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1576_ == 0 {
                    v___x_1577_ = l_Lake_Hash_ofJsonNumber_x3f___closed__1;
                    return v___x_1577_;
                } else {
                    v___x_1578_ = l_Int_toNat(v_mantissa_1573_);
                    v___x_1579_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__2),
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__2_once),
                        _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2,
                    );
                    v___x_1580_ = lean_nat_dec_lt(v___x_1578_, v___x_1579_);
                    if v___x_1580_ == 0 {
                        lean_dec(v___x_1578_);
                        v___x_1581_ = l_Lake_Hash_ofJsonNumber_x3f___closed__4;
                        return v___x_1581_;
                    } else {
                        v___x_1582_ = lean_uint64_of_nat(v___x_1578_);
                        lean_dec(v___x_1578_);
                        v___x_1583_ = lean_box_uint64(v___x_1582_);
                        v___x_1584_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1584_, 0, v___x_1583_);
                        return v___x_1584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Hash_ofJsonNumber_x3f___boxed(
    mut v_n_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1589_);
    lean_dec_ref(v_n_1589_);
    return v_res_1590_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
    mut v_s_1591_: *mut LeanObject,
    mut v_n_1592_: *mut LeanObject,
    mut v_j_1593_: *mut LeanObject,
    mut v_a_1594_: u64,
) -> u64 {
    let mut v_zero_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1596_: u8 = 0;
    let mut v_one_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1600_: u8 = 0;
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: u64 = 0;
    let mut v___x_1606_: u64 = 0;
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: u8 = 0;
    let mut v___x_1609_: u64 = 0;
    let mut v___x_1610_: u64 = 0;
    let mut v___x_1612_: u64 = 0;
    let mut v___x_1613_: u64 = 0;
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: u64 = 0;
    let mut v___x_1617_: u64 = 0;
    let mut v___x_1619_: u64 = 0;
    let mut v___x_1620_: u64 = 0;
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: u64 = 0;
    let mut v___x_1624_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1595_ = lean_unsigned_to_nat(0);
                v_isZero_1596_ = lean_nat_dec_eq(v_j_1593_, v_zero_1595_);
                if v_isZero_1596_ == 1 {
                    lean_dec(v_j_1593_);
                    return v_a_1594_;
                } else {
                    v_one_1597_ = lean_unsigned_to_nat(1);
                    v_n_1598_ = lean_nat_sub(v_j_1593_, v_one_1597_);
                    v___x_1599_ = lean_nat_sub(v_n_1592_, v_j_1593_);
                    lean_dec(v_j_1593_);
                    v_c_1600_ = lean_string_get_byte_fast(v_s_1591_, v___x_1599_);
                    v___x_1601_ = 57;
                    v___x_1602_ = lean_uint8_dec_le(v_c_1600_, v___x_1601_);
                    if v___x_1602_ == 0 {
                        v___x_1603_ = 97;
                        v___x_1604_ = lean_uint8_dec_le(v___x_1603_, v_c_1600_);
                        if v___x_1604_ == 0 {
                            v___x_1605_ = 4u64;
                            v___x_1606_ = lean_uint64_shift_left(v_a_1594_, v___x_1605_);
                            v___x_1607_ = 55;
                            v___x_1608_ = lean_uint8_sub(v_c_1600_, v___x_1607_);
                            v___x_1609_ = lean_uint8_to_uint64(v___x_1608_);
                            v___x_1610_ = lean_uint64_add(v___x_1606_, v___x_1609_);
                            v_j_1593_ = v_n_1598_;
                            v_a_1594_ = v___x_1610_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1612_ = 4u64;
                            v___x_1613_ = lean_uint64_shift_left(v_a_1594_, v___x_1612_);
                            v___x_1614_ = 87;
                            v___x_1615_ = lean_uint8_sub(v_c_1600_, v___x_1614_);
                            v___x_1616_ = lean_uint8_to_uint64(v___x_1615_);
                            v___x_1617_ = lean_uint64_add(v___x_1613_, v___x_1616_);
                            v_j_1593_ = v_n_1598_;
                            v_a_1594_ = v___x_1617_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1619_ = 4u64;
                        v___x_1620_ = lean_uint64_shift_left(v_a_1594_, v___x_1619_);
                        v___x_1621_ = 48;
                        v___x_1622_ = lean_uint8_sub(v_c_1600_, v___x_1621_);
                        v___x_1623_ = lean_uint8_to_uint64(v___x_1622_);
                        v___x_1624_ = lean_uint64_add(v___x_1620_, v___x_1623_);
                        v_j_1593_ = v_n_1598_;
                        v_a_1594_ = v___x_1624_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(
    mut v_s_1626_: *mut LeanObject,
    mut v_n_1627_: *mut LeanObject,
    mut v_j_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_252__boxed_1630_: u64 = 0;
    let mut v_res_1631_: u64 = 0;
    let mut v_r_1632_: *mut LeanObject = core::ptr::null_mut();
    v_a_252__boxed_1630_ = lean_unbox_uint64(v_a_1629_);
    lean_dec_ref(v_a_1629_);
    v_res_1631_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
            v_s_1626_,
            v_n_1627_,
            v_j_1628_,
            v_a_252__boxed_1630_,
        );
    lean_dec(v_n_1627_);
    lean_dec_ref(v_s_1626_);
    v_r_1632_ = lean_box_uint64(v_res_1631_);
    return v_r_1632_;
}
pub unsafe fn l_Lake_Hash_ofHex(mut v_s_1633_: *mut LeanObject) -> u64 {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u64 = 0;
    let mut v___x_1636_: u64 = 0;
    v___x_1634_ = lean_string_utf8_byte_size(v_s_1633_);
    v___x_1635_ = 0u64;
    v___x_1636_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
            v_s_1633_,
            v___x_1634_,
            v___x_1634_,
            v___x_1635_,
        );
    return v___x_1636_;
}
pub unsafe fn l_Lake_Hash_ofHex___boxed(mut v_s_1637_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1638_: u64 = 0;
    let mut v_r_1639_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lake_Hash_ofHex(v_s_1637_);
    lean_dec_ref(v_s_1637_);
    v_r_1639_ = lean_box_uint64(v_res_1638_);
    return v_r_1639_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(
    mut v_s_1640_: *mut LeanObject,
    mut v_n_1641_: *mut LeanObject,
    mut v_j_1642_: *mut LeanObject,
    mut v_a_1643_: *mut LeanObject,
    mut v_a_1644_: u64,
) -> u64 {
    let mut v___x_1645_: u64 = 0;
    v___x_1645_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
            v_s_1640_, v_n_1641_, v_j_1642_, v_a_1644_,
        );
    return v___x_1645_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(
    mut v_s_1646_: *mut LeanObject,
    mut v_n_1647_: *mut LeanObject,
    mut v_j_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_316__boxed_1651_: u64 = 0;
    let mut v_res_1652_: u64 = 0;
    let mut v_r_1653_: *mut LeanObject = core::ptr::null_mut();
    v_a_316__boxed_1651_ = lean_unbox_uint64(v_a_1650_);
    lean_dec_ref(v_a_1650_);
    v_res_1652_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(
            v_s_1646_,
            v_n_1647_,
            v_j_1648_,
            v_a_1649_,
            v_a_316__boxed_1651_,
        );
    lean_dec(v_n_1647_);
    lean_dec_ref(v_s_1646_);
    v_r_1653_ = lean_box_uint64(v_res_1652_);
    return v_r_1653_;
}
pub unsafe fn l_Lake_Hash_ofHex_x3f(mut v_s_1654_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_1656_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u64 = 0;
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_string_utf8_byte_size(v_s_1654_);
                v___x_1662_ = lean_unsigned_to_nat(16);
                v___x_1663_ = lean_nat_dec_eq(v___x_1661_, v___x_1662_);
                if v___x_1663_ == 0 {
                    v___y_1656_ = v___x_1663_;
                    state = 1;
                    continue;
                } else {
                    v___x_1664_ = l_Lake_isHex(v_s_1654_);
                    v___y_1656_ = v___x_1664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1656_ == 0 {
                    v___x_1657_ = lean_box(0);
                    return v___x_1657_;
                } else {
                    v___x_1658_ = l_Lake_Hash_ofHex(v_s_1654_);
                    v___x_1659_ = lean_box_uint64(v___x_1658_);
                    v___x_1660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1660_, 0, v___x_1659_);
                    return v___x_1660_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Hash_ofHex_x3f___boxed(mut v_s_1665_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1666_: *mut LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lake_Hash_ofHex_x3f(v_s_1665_);
    lean_dec_ref(v_s_1665_);
    return v_res_1666_;
}
pub unsafe fn l_Lake_Hash_hex(mut v_self_1667_: u64) -> *mut LeanObject {
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lake_lowerHexUInt64(v_self_1667_);
    return v___x_1668_;
}
pub unsafe fn l_Lake_Hash_hex___boxed(mut v_self_1669_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_1670_: u64 = 0;
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_1670_ = lean_unbox_uint64(v_self_1669_);
    lean_dec_ref(v_self_1669_);
    v_res_1671_ = l_Lake_Hash_hex(v_self_boxed_1670_);
    return v_res_1671_;
}
pub unsafe fn l_Lake_Hash_ofDecimal_x3f(mut v_s_1672_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: u64 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1673_ = lean_unsigned_to_nat(0);
                v___x_1674_ = lean_string_utf8_byte_size(v_s_1672_);
                v___x_1675_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1675_, 0, v_s_1672_);
                lean_ctor_set(v___x_1675_, 1, v___x_1673_);
                lean_ctor_set(v___x_1675_, 2, v___x_1674_);
                v___x_1676_ = l_String_Slice_toNat_x3f(v___x_1675_);
                lean_dec_ref_known(v___x_1675_, 3);
                if lean_obj_tag(v___x_1676_) == 0 {
                    v___x_1677_ = lean_box(0);
                    return v___x_1677_;
                } else {
                    v_val_1678_ = lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1687_ = (!lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1680_ = v___x_1676_;
                        v_isShared_1681_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1678_);
                        lean_dec(v___x_1676_);
                        v___x_1680_ = lean_box(0);
                        v_isShared_1681_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1682_ = lean_uint64_of_nat(v_val_1678_);
                lean_dec(v_val_1678_);
                v___x_1683_ = lean_box_uint64(v___x_1682_);
                if v_isShared_1681_ == 0 {
                    lean_ctor_set(v___x_1680_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Hash_ofString_x3f(mut v_s_1688_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lake_Hash_ofHex_x3f(v_s_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lake_Hash_ofString_x3f___boxed(mut v_s_1690_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1691_: *mut LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Lake_Hash_ofString_x3f(v_s_1690_);
    lean_dec_ref(v_s_1690_);
    return v_res_1691_;
}
pub unsafe fn l_Lake_Hash_load_x3f(mut v_hashFile_1692_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_IO_FS_readFile(v_hashFile_1692_);
    if lean_obj_tag(v___x_1694_) == 0 {
        let mut v_a_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
        v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
        lean_inc(v_a_1695_);
        lean_dec_ref_known(v___x_1694_, 1);
        v___x_1696_ = l_Lake_Hash_ofHex_x3f(v_a_1695_);
        lean_dec(v_a_1695_);
        return v___x_1696_;
    } else {
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_1694_, 1);
        v___x_1697_ = lean_box(0);
        return v___x_1697_;
    }
}
pub unsafe fn l_Lake_Hash_load_x3f___boxed(
    mut v_hashFile_1698_: *mut LeanObject,
    mut v_a_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1700_: *mut LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_Lake_Hash_load_x3f(v_hashFile_1698_);
    lean_dec_ref(v_hashFile_1698_);
    return v_res_1700_;
}
pub unsafe fn l_Lake_Hash_mix(mut v_h1_1701_: u64, mut v_h2_1702_: u64) -> u64 {
    let mut v___x_1703_: u64 = 0;
    v___x_1703_ = lean_uint64_mix_hash(v_h1_1701_, v_h2_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Lake_Hash_mix___boxed(
    mut v_h1_1704_: *mut LeanObject,
    mut v_h2_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h1_boxed_1706_: u64 = 0;
    let mut v_h2_boxed_1707_: u64 = 0;
    let mut v_res_1708_: u64 = 0;
    let mut v_r_1709_: *mut LeanObject = core::ptr::null_mut();
    v_h1_boxed_1706_ = lean_unbox_uint64(v_h1_1704_);
    lean_dec_ref(v_h1_1704_);
    v_h2_boxed_1707_ = lean_unbox_uint64(v_h2_1705_);
    lean_dec_ref(v_h2_1705_);
    v_res_1708_ = l_Lake_Hash_mix(v_h1_boxed_1706_, v_h2_boxed_1707_);
    v_r_1709_ = lean_box_uint64(v_res_1708_);
    return v_r_1709_;
}
pub unsafe fn l_Lake_Hash_toString(mut v_self_1712_: u64) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lake_lowerHexUInt64(v_self_1712_);
    return v___x_1713_;
}
pub unsafe fn l_Lake_Hash_toString___boxed(mut v_self_1714_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_1715_: u64 = 0;
    let mut v_res_1716_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_1715_ = lean_unbox_uint64(v_self_1714_);
    lean_dec_ref(v_self_1714_);
    v_res_1716_ = l_Lake_Hash_toString(v_self_boxed_1715_);
    return v_res_1716_;
}
pub unsafe fn l_Lake_Hash_ofHashable___redArg(
    mut v_inst_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
) -> u64 {
    let mut v___x_1721_: u64 = 0;
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: u64 = 0;
    let mut v___x_1724_: u64 = 0;
    v___x_1721_ = 1723u64;
    v___x_1722_ = lean_apply_1(v_inst_1719_, v_a_1720_);
    v___x_1723_ = lean_unbox_uint64(v___x_1722_);
    lean_dec_ref(v___x_1722_);
    v___x_1724_ = lean_uint64_mix_hash(v___x_1721_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lake_Hash_ofHashable___redArg___boxed(
    mut v_inst_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1727_: u64 = 0;
    let mut v_r_1728_: *mut LeanObject = core::ptr::null_mut();
    v_res_1727_ = l_Lake_Hash_ofHashable___redArg(v_inst_1725_, v_a_1726_);
    v_r_1728_ = lean_box_uint64(v_res_1727_);
    return v_r_1728_;
}
pub unsafe fn l_Lake_Hash_ofHashable(
    mut v_00_u03b1_1729_: *mut LeanObject,
    mut v_inst_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
) -> u64 {
    let mut v___x_1732_: u64 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u64 = 0;
    let mut v___x_1735_: u64 = 0;
    v___x_1732_ = 1723u64;
    v___x_1733_ = lean_apply_1(v_inst_1730_, v_a_1731_);
    v___x_1734_ = lean_unbox_uint64(v___x_1733_);
    lean_dec_ref(v___x_1733_);
    v___x_1735_ = lean_uint64_mix_hash(v___x_1732_, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Lake_Hash_ofHashable___boxed(
    mut v_00_u03b1_1736_: *mut LeanObject,
    mut v_inst_1737_: *mut LeanObject,
    mut v_a_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1739_: u64 = 0;
    let mut v_r_1740_: *mut LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lake_Hash_ofHashable(v_00_u03b1_1736_, v_inst_1737_, v_a_1738_);
    v_r_1740_ = lean_box_uint64(v_res_1739_);
    return v_r_1740_;
}
pub unsafe fn l_Lake_Hash_ofString(mut v_str_1741_: *mut LeanObject) -> u64 {
    let mut v___x_1742_: u64 = 0;
    let mut v___x_1743_: u64 = 0;
    let mut v___x_1744_: u64 = 0;
    v___x_1742_ = 1723u64;
    v___x_1743_ = lean_string_hash(v_str_1741_);
    v___x_1744_ = lean_uint64_mix_hash(v___x_1742_, v___x_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Lake_Hash_ofString___boxed(mut v_str_1745_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1746_: u64 = 0;
    let mut v_r_1747_: *mut LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lake_Hash_ofString(v_str_1745_);
    lean_dec_ref(v_str_1745_);
    v_r_1747_ = lean_box_uint64(v_res_1746_);
    return v_r_1747_;
}
pub unsafe fn l_Lake_Hash_ofText(mut v_str_1748_: *mut LeanObject) -> u64 {
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: u64 = 0;
    v___x_1749_ = l_String_crlfToLf(v_str_1748_);
    v___x_1750_ = 1723u64;
    v___x_1751_ = lean_string_hash(v___x_1749_);
    lean_dec_ref(v___x_1749_);
    v___x_1752_ = lean_uint64_mix_hash(v___x_1750_, v___x_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Lake_Hash_ofText___boxed(mut v_str_1753_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1754_: u64 = 0;
    let mut v_r_1755_: *mut LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Lake_Hash_ofText(v_str_1753_);
    lean_dec_ref(v_str_1753_);
    v_r_1755_ = lean_box_uint64(v_res_1754_);
    return v_r_1755_;
}
pub unsafe fn l_Lake_Hash_ofByteArray(mut v_bytes_1756_: *mut LeanObject) -> u64 {
    let mut v___x_1757_: u64 = 0;
    let mut v___x_1758_: u64 = 0;
    let mut v___x_1759_: u64 = 0;
    v___x_1757_ = 1723u64;
    v___x_1758_ = lean_byte_array_hash(v_bytes_1756_);
    v___x_1759_ = lean_uint64_mix_hash(v___x_1757_, v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Lake_Hash_ofByteArray___boxed(
    mut v_bytes_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1761_: u64 = 0;
    let mut v_r_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1761_ = l_Lake_Hash_ofByteArray(v_bytes_1760_);
    lean_dec_ref(v_bytes_1760_);
    v_r_1762_ = lean_box_uint64(v_res_1761_);
    return v_r_1762_;
}
pub unsafe fn _init_l_Lake_Hash_ofBool___closed__0() -> u64 {
    let mut v___x_1763_: u64 = 0;
    let mut v___x_1764_: u64 = 0;
    let mut v___x_1765_: u64 = 0;
    v___x_1763_ = 13u64;
    v___x_1764_ = 1723u64;
    v___x_1765_ = lean_uint64_mix_hash(v___x_1764_, v___x_1763_);
    return v___x_1765_;
}
pub unsafe fn _init_l_Lake_Hash_ofBool___closed__1() -> u64 {
    let mut v___x_1766_: u64 = 0;
    let mut v___x_1767_: u64 = 0;
    let mut v___x_1768_: u64 = 0;
    v___x_1766_ = 11u64;
    v___x_1767_ = 1723u64;
    v___x_1768_ = lean_uint64_mix_hash(v___x_1767_, v___x_1766_);
    return v___x_1768_;
}
pub unsafe fn l_Lake_Hash_ofBool(mut v_b_1769_: u8) -> u64 {
    if v_b_1769_ == 0 {
        let mut v___x_1770_: u64 = 0;
        v___x_1770_ = lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__0),
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__0_once),
            _init_l_Lake_Hash_ofBool___closed__0,
        );
        return v___x_1770_;
    } else {
        let mut v___x_1771_: u64 = 0;
        v___x_1771_ = lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__1),
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__1_once),
            _init_l_Lake_Hash_ofBool___closed__1,
        );
        return v___x_1771_;
    }
}
pub unsafe fn l_Lake_Hash_ofBool___boxed(mut v_b_1772_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_1773_: u8 = 0;
    let mut v_res_1774_: u64 = 0;
    let mut v_r_1775_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1773_ = (lean_unbox(v_b_1772_) as u8);
    v_res_1774_ = l_Lake_Hash_ofBool(v_b_boxed_1773_);
    v_r_1775_ = lean_box_uint64(v_res_1774_);
    return v_r_1775_;
}
pub unsafe fn l_Lake_Hash_toJson(mut v_self_1776_: u64) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lake_lowerHexUInt64(v_self_1776_);
    v___x_1778_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lake_Hash_toJson___boxed(mut v_self_1779_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_1780_: u64 = 0;
    let mut v_res_1781_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_1780_ = lean_unbox_uint64(v_self_1779_);
    lean_dec_ref(v_self_1779_);
    v_res_1781_ = l_Lake_Hash_toJson(v_self_boxed_1780_);
    return v_res_1781_;
}
pub unsafe fn l_Lake_Hash_fromJson_x3f(mut v_json_1794_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u64 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_n_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_json_1794_) {
                3 => {
                    v_s_1795_ = lean_ctor_get(v_json_1794_, 0);
                    v_isSharedCheck_1810_ = (!lean_is_exclusive(v_json_1794_)) as u8;
                    if v_isSharedCheck_1810_ == 0 {
                        v___x_1797_ = v_json_1794_;
                        v_isShared_1798_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_1795_);
                        lean_dec(v_json_1794_);
                        v___x_1797_ = lean_box(0);
                        v_isShared_1798_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_n_1811_ = lean_ctor_get(v_json_1794_, 0);
                    lean_inc_ref(v_n_1811_);
                    lean_dec_ref_known(v_json_1794_, 1);
                    v___x_1812_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1811_);
                    lean_dec_ref(v_n_1811_);
                    if lean_obj_tag(v___x_1812_) == 0 {
                        v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
                        v_isSharedCheck_1822_ = (!lean_is_exclusive(v___x_1812_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v___x_1815_ = v___x_1812_;
                            v_isShared_1816_ = v_isSharedCheck_1822_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1813_);
                            lean_dec(v___x_1812_);
                            v___x_1815_ = lean_box(0);
                            v_isShared_1816_ = v_isSharedCheck_1822_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_1812_;
                    }
                }
                _ => {
                    lean_dec(v_json_1794_);
                    v___x_1823_ = l_Lake_Hash_fromJson_x3f___closed__6;
                    return v___x_1823_;
                }
            },
            1 => {
                v___x_1799_ = l_Lake_isHex(v_s_1795_);
                if v___x_1799_ == 0 {
                    lean_del_object(v___x_1797_);
                    lean_dec_ref(v_s_1795_);
                    v___x_1800_ = l_Lake_Hash_fromJson_x3f___closed__1;
                    return v___x_1800_;
                } else {
                    v___x_1801_ = lean_string_utf8_byte_size(v_s_1795_);
                    v___x_1802_ = lean_unsigned_to_nat(16);
                    v___x_1803_ = lean_nat_dec_eq(v___x_1801_, v___x_1802_);
                    if v___x_1803_ == 0 {
                        lean_del_object(v___x_1797_);
                        lean_dec_ref(v_s_1795_);
                        v___x_1804_ = l_Lake_Hash_fromJson_x3f___closed__3;
                        return v___x_1804_;
                    } else {
                        v___x_1805_ = l_Lake_Hash_ofHex(v_s_1795_);
                        lean_dec_ref(v_s_1795_);
                        v___x_1806_ = lean_box_uint64(v___x_1805_);
                        if v_isShared_1798_ == 0 {
                            lean_ctor_set_tag(v___x_1797_, 1);
                            lean_ctor_set(v___x_1797_, 0, v___x_1806_);
                            v___x_1808_ = v___x_1797_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                            v___x_1808_ = v_reuseFailAlloc_1809_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1808_;
            }
            3 => {
                v___x_1817_ = l_Lake_Hash_fromJson_x3f___closed__4;
                v___x_1818_ = lean_string_append(v___x_1817_, v_a_1813_);
                lean_dec(v_a_1813_);
                if v_isShared_1816_ == 0 {
                    lean_ctor_set(v___x_1815_, 0, v___x_1818_);
                    v___x_1820_ = v___x_1815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash___redArg(
    mut v_inst_1826_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1826_);
    return v_inst_1826_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(
    mut v_inst_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_1827_);
    lean_dec(v_inst_1827_);
    return v_res_1828_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash(
    mut v_00_u03b1_1829_: *mut LeanObject,
    mut v_m_1830_: *mut LeanObject,
    mut v_inst_1831_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_1831_);
    return v_inst_1831_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash___boxed(
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_m_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1835_: *mut LeanObject = core::ptr::null_mut();
    v_res_1835_ =
        l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_1832_, v_m_1833_, v_inst_1834_);
    lean_dec(v_inst_1834_);
    return v_res_1835_;
}
pub unsafe fn l_Lake_pureHash___redArg(
    mut v_inst_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
) -> u64 {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u64 = 0;
    v___x_1838_ = lean_apply_1(v_inst_1836_, v_a_1837_);
    v___x_1839_ = lean_unbox_uint64(v___x_1838_);
    lean_dec_ref(v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l_Lake_pureHash___redArg___boxed(
    mut v_inst_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: u64 = 0;
    let mut v_r_1843_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lake_pureHash___redArg(v_inst_1840_, v_a_1841_);
    v_r_1843_ = lean_box_uint64(v_res_1842_);
    return v_r_1843_;
}
pub unsafe fn l_Lake_pureHash(
    mut v_00_u03b1_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> u64 {
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u64 = 0;
    v___x_1847_ = lean_apply_1(v_inst_1845_, v_a_1846_);
    v___x_1848_ = lean_unbox_uint64(v___x_1847_);
    lean_dec_ref(v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Lake_pureHash___boxed(
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_inst_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1852_: u64 = 0;
    let mut v_r_1853_: *mut LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Lake_pureHash(v_00_u03b1_1849_, v_inst_1850_, v_a_1851_);
    v_r_1853_ = lean_box_uint64(v_res_1852_);
    return v_r_1853_;
}
pub unsafe fn l_Lake_computeHash___redArg(
    mut v_inst_1854_: *mut LeanObject,
    mut v_inst_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___x_1857_ = lean_apply_1(v_inst_1854_, v_a_1856_);
    v___x_1858_ = lean_apply_2(v_inst_1855_, lean_box(0), v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn l_Lake_computeHash(
    mut v_00_u03b1_1859_: *mut LeanObject,
    mut v_m_1860_: *mut LeanObject,
    mut v_n_1861_: *mut LeanObject,
    mut v_inst_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
    mut v_a_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1865_ = lean_apply_1(v_inst_1862_, v_a_1864_);
    v___x_1866_ = lean_apply_2(v_inst_1863_, lean_box(0), v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Lake_instComputeHashIdOfHashable___redArg(
    mut v_inst_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v___x_1868_ = lean_alloc_closure(
        l_Lake_Hash_ofHashable___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_1868_, 0, lean_box(0));
    lean_closure_set(v___x_1868_, 1, v_inst_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Lake_instComputeHashIdOfHashable(
    mut v_00_u03b1_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    v___x_1871_ = lean_alloc_closure(
        l_Lake_Hash_ofHashable___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_1871_, 0, lean_box(0));
    lean_closure_set(v___x_1871_, 1, v_inst_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lake_computeBinFileHash(mut v_file_1872_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1879_: u64 = 0;
    let mut v___x_1880_: u64 = 0;
    let mut v___x_1881_: u64 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_a_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1874_ = l_IO_FS_readBinFile(v_file_1872_);
                if lean_obj_tag(v___x_1874_) == 0 {
                    v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
                    v_isSharedCheck_1886_ = (!lean_is_exclusive(v___x_1874_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v___x_1877_ = v___x_1874_;
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1875_);
                        lean_dec(v___x_1874_);
                        v___x_1877_ = lean_box(0);
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1887_ = lean_ctor_get(v___x_1874_, 0);
                    v_isSharedCheck_1894_ = (!lean_is_exclusive(v___x_1874_)) as u8;
                    if v_isSharedCheck_1894_ == 0 {
                        v___x_1889_ = v___x_1874_;
                        v_isShared_1890_ = v_isSharedCheck_1894_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1887_);
                        lean_dec(v___x_1874_);
                        v___x_1889_ = lean_box(0);
                        v_isShared_1890_ = v_isSharedCheck_1894_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1879_ = 1723u64;
                v___x_1880_ = lean_byte_array_hash(v_a_1875_);
                lean_dec(v_a_1875_);
                v___x_1881_ = lean_uint64_mix_hash(v___x_1879_, v___x_1880_);
                v___x_1882_ = lean_box_uint64(v___x_1881_);
                if v_isShared_1878_ == 0 {
                    lean_ctor_set(v___x_1877_, 0, v___x_1882_);
                    v___x_1884_ = v___x_1877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
                    v___x_1884_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1884_;
            }
            3 => {
                if v_isShared_1890_ == 0 {
                    v___x_1892_ = v___x_1889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_computeBinFileHash___boxed(
    mut v_file_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lake_computeBinFileHash(v_file_1895_);
    lean_dec_ref(v_file_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Lake_computeTextFileHash(mut v_file_1900_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u64 = 0;
    let mut v___x_1909_: u64 = 0;
    let mut v___x_1910_: u64 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_a_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1902_ = l_IO_FS_readFile(v_file_1900_);
                if lean_obj_tag(v___x_1902_) == 0 {
                    v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
                    v_isSharedCheck_1915_ = (!lean_is_exclusive(v___x_1902_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1905_ = v___x_1902_;
                        v_isShared_1906_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1903_);
                        lean_dec(v___x_1902_);
                        v___x_1905_ = lean_box(0);
                        v_isShared_1906_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1916_ = lean_ctor_get(v___x_1902_, 0);
                    v_isSharedCheck_1923_ = (!lean_is_exclusive(v___x_1902_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1902_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1916_);
                        lean_dec(v___x_1902_);
                        v___x_1918_ = lean_box(0);
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1907_ = l_String_crlfToLf(v_a_1903_);
                lean_dec(v_a_1903_);
                v___x_1908_ = 1723u64;
                v___x_1909_ = lean_string_hash(v___x_1907_);
                lean_dec_ref(v___x_1907_);
                v___x_1910_ = lean_uint64_mix_hash(v___x_1908_, v___x_1909_);
                v___x_1911_ = lean_box_uint64(v___x_1910_);
                if v_isShared_1906_ == 0 {
                    lean_ctor_set(v___x_1905_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1913_;
            }
            3 => {
                if v_isShared_1919_ == 0 {
                    v___x_1921_ = v___x_1918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_computeTextFileHash___boxed(
    mut v_file_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1926_: *mut LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Lake_computeTextFileHash(v_file_1924_);
    lean_dec_ref(v_file_1924_);
    return v_res_1926_;
}
pub unsafe fn l_Lake_instCoeTextFilePathFilePath___lam__0(
    mut v_x_1927_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_x_1927_);
    return v_x_1927_;
}
pub unsafe fn l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(
    mut v_x_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_1928_);
    lean_dec_ref(v_x_1928_);
    return v_res_1929_;
}
pub unsafe fn l_Lake_computeFileHash(
    mut v_file_1935_: *mut LeanObject,
    mut v_text_1936_: u8,
) -> *mut LeanObject {
    if v_text_1936_ == 0 {
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        v___x_1938_ = l_Lake_computeBinFileHash(v_file_1935_);
        return v___x_1938_;
    } else {
        let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
        v___x_1939_ = l_Lake_computeTextFileHash(v_file_1935_);
        return v___x_1939_;
    }
}
pub unsafe fn l_Lake_computeFileHash___boxed(
    mut v_file_1940_: *mut LeanObject,
    mut v_text_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_text_boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_text_boxed_1943_ = (lean_unbox(v_text_1941_) as u8);
    v_res_1944_ = l_Lake_computeFileHash(v_file_1940_, v_text_boxed_1943_);
    lean_dec_ref(v_file_1940_);
    return v_res_1944_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__0(
    mut v_ts_1945_: u64,
    mut v_toPure_1946_: *mut LeanObject,
    mut v_____do__lift_1947_: u64,
) -> *mut LeanObject {
    let mut v___x_1948_: u64 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_uint64_mix_hash(v_ts_1945_, v_____do__lift_1947_);
    v___x_1949_ = lean_box_uint64(v___x_1948_);
    v___x_1950_ = lean_apply_2(v_toPure_1946_, lean_box(0), v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__0___boxed(
    mut v_ts_1951_: *mut LeanObject,
    mut v_toPure_1952_: *mut LeanObject,
    mut v_____do__lift_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ts_boxed_1954_: u64 = 0;
    let mut v_____do__lift_97__boxed_1955_: u64 = 0;
    let mut v_res_1956_: *mut LeanObject = core::ptr::null_mut();
    v_ts_boxed_1954_ = lean_unbox_uint64(v_ts_1951_);
    lean_dec_ref(v_ts_1951_);
    v_____do__lift_97__boxed_1955_ = lean_unbox_uint64(v_____do__lift_1953_);
    lean_dec_ref(v_____do__lift_1953_);
    v_res_1956_ = l_Lake_computeArrayHash___redArg___lam__0(
        v_ts_boxed_1954_,
        v_toPure_1952_,
        v_____do__lift_97__boxed_1955_,
    );
    return v_res_1956_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__1(
    mut v_toPure_1957_: *mut LeanObject,
    mut v_inst_1958_: *mut LeanObject,
    mut v_toBind_1959_: *mut LeanObject,
    mut v_ts_1960_: u64,
    mut v_t_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1962_ = lean_box_uint64(v_ts_1960_);
    v___f_1963_ = lean_alloc_closure(
        l_Lake_computeArrayHash___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1963_, 0, v___x_1962_);
    lean_closure_set(v___f_1963_, 1, v_toPure_1957_);
    v___x_1964_ = lean_apply_1(v_inst_1958_, v_t_1961_);
    v___x_1965_ = lean_apply_4(
        v_toBind_1959_,
        lean_box(0),
        lean_box(0),
        v___x_1964_,
        v___f_1963_,
    );
    return v___x_1965_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__1___boxed(
    mut v_toPure_1966_: *mut LeanObject,
    mut v_inst_1967_: *mut LeanObject,
    mut v_toBind_1968_: *mut LeanObject,
    mut v_ts_1969_: *mut LeanObject,
    mut v_t_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ts_boxed_1971_: u64 = 0;
    let mut v_res_1972_: *mut LeanObject = core::ptr::null_mut();
    v_ts_boxed_1971_ = lean_unbox_uint64(v_ts_1969_);
    lean_dec_ref(v_ts_1969_);
    v_res_1972_ = l_Lake_computeArrayHash___redArg___lam__1(
        v_toPure_1966_,
        v_inst_1967_,
        v_toBind_1968_,
        v_ts_boxed_1971_,
        v_t_1970_,
    );
    return v_res_1972_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg(
    mut v_inst_1975_: *mut LeanObject,
    mut v_inst_1976_: *mut LeanObject,
    mut v_as_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    v_toApplicative_1978_ = lean_ctor_get(v_inst_1976_, 0);
    v_toBind_1979_ = lean_ctor_get(v_inst_1976_, 1);
    v_toPure_1980_ = lean_ctor_get(v_toApplicative_1978_, 1);
    v___x_1981_ = lean_unsigned_to_nat(0);
    v___x_1982_ = lean_array_get_size(v_as_1977_);
    v___x_1983_ = lean_nat_dec_lt(v___x_1981_, v___x_1982_);
    if v___x_1983_ == 0 {
        let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_1980_);
        lean_dec_ref(v_as_1977_);
        lean_dec_ref(v_inst_1976_);
        lean_dec(v_inst_1975_);
        v___x_1984_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
        v___x_1985_ = lean_apply_2(v_toPure_1980_, lean_box(0), v___x_1984_);
        return v___x_1985_;
    } else {
        let mut v___f_1986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: u8 = 0;
        lean_inc(v_toBind_1979_);
        lean_inc(v_toPure_1980_);
        v___f_1986_ = lean_alloc_closure(
            l_Lake_computeArrayHash___redArg___lam__1___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_1986_, 0, v_toPure_1980_);
        lean_closure_set(v___f_1986_, 1, v_inst_1975_);
        lean_closure_set(v___f_1986_, 2, v_toBind_1979_);
        v___x_1987_ = lean_nat_dec_le(v___x_1982_, v___x_1982_);
        if v___x_1987_ == 0 {
            if v___x_1983_ == 0 {
                let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_1980_);
                lean_dec_ref(v___f_1986_);
                lean_dec_ref(v_as_1977_);
                lean_dec_ref(v_inst_1976_);
                v___x_1988_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_1989_ = lean_apply_2(v_toPure_1980_, lean_box(0), v___x_1988_);
                return v___x_1989_;
            } else {
                let mut v___x_1990_: usize = 0;
                let mut v___x_1991_: usize = 0;
                let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
                v___x_1990_ = 0usize;
                v___x_1991_ = lean_usize_of_nat(v___x_1982_);
                v___x_1992_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_1976_,
                    v___f_1986_,
                    v_as_1977_,
                    v___x_1990_,
                    v___x_1991_,
                    v___x_1992_,
                );
                return v___x_1993_;
            }
        } else {
            let mut v___x_1994_: usize = 0;
            let mut v___x_1995_: usize = 0;
            let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
            v___x_1994_ = 0usize;
            v___x_1995_ = lean_usize_of_nat(v___x_1982_);
            v___x_1996_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
            v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_1976_,
                v___f_1986_,
                v_as_1977_,
                v___x_1994_,
                v___x_1995_,
                v___x_1996_,
            );
            return v___x_1997_;
        }
    }
}
pub unsafe fn l_Lake_computeArrayHash(
    mut v_00_u03b1_1998_: *mut LeanObject,
    mut v_m_1999_: *mut LeanObject,
    mut v_inst_2000_: *mut LeanObject,
    mut v_inst_2001_: *mut LeanObject,
    mut v_as_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    v_toApplicative_2003_ = lean_ctor_get(v_inst_2001_, 0);
    v_toBind_2004_ = lean_ctor_get(v_inst_2001_, 1);
    v_toPure_2005_ = lean_ctor_get(v_toApplicative_2003_, 1);
    v___x_2006_ = lean_unsigned_to_nat(0);
    v___x_2007_ = lean_array_get_size(v_as_2002_);
    v___x_2008_ = lean_nat_dec_lt(v___x_2006_, v___x_2007_);
    if v___x_2008_ == 0 {
        let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_2005_);
        lean_dec_ref(v_as_2002_);
        lean_dec_ref(v_inst_2001_);
        lean_dec(v_inst_2000_);
        v___x_2009_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
        v___x_2010_ = lean_apply_2(v_toPure_2005_, lean_box(0), v___x_2009_);
        return v___x_2010_;
    } else {
        let mut v___f_2011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: u8 = 0;
        lean_inc(v_toBind_2004_);
        lean_inc(v_toPure_2005_);
        v___f_2011_ = lean_alloc_closure(
            l_Lake_computeArrayHash___redArg___lam__1___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        lean_closure_set(v___f_2011_, 0, v_toPure_2005_);
        lean_closure_set(v___f_2011_, 1, v_inst_2000_);
        lean_closure_set(v___f_2011_, 2, v_toBind_2004_);
        v___x_2012_ = lean_nat_dec_le(v___x_2007_, v___x_2007_);
        if v___x_2012_ == 0 {
            if v___x_2008_ == 0 {
                let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_toPure_2005_);
                lean_dec_ref(v___f_2011_);
                lean_dec_ref(v_as_2002_);
                lean_dec_ref(v_inst_2001_);
                v___x_2013_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_2014_ = lean_apply_2(v_toPure_2005_, lean_box(0), v___x_2013_);
                return v___x_2014_;
            } else {
                let mut v___x_2015_: usize = 0;
                let mut v___x_2016_: usize = 0;
                let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
                v___x_2015_ = 0usize;
                v___x_2016_ = lean_usize_of_nat(v___x_2007_);
                v___x_2017_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_2001_,
                    v___f_2011_,
                    v_as_2002_,
                    v___x_2015_,
                    v___x_2016_,
                    v___x_2017_,
                );
                return v___x_2018_;
            }
        } else {
            let mut v___x_2019_: usize = 0;
            let mut v___x_2020_: usize = 0;
            let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
            v___x_2019_ = 0usize;
            v___x_2020_ = lean_usize_of_nat(v___x_2007_);
            v___x_2021_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
            v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_2001_,
                v___f_2011_,
                v_as_2002_,
                v___x_2019_,
                v___x_2020_,
                v___x_2021_,
            );
            return v___x_2022_;
        }
    }
}
pub unsafe fn l_Lake_instComputeHashArrayOfMonad___redArg(
    mut v_inst_2023_: *mut LeanObject,
    mut v_inst_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    v___x_2025_ = lean_alloc_closure(l_Lake_computeArrayHash as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_2025_, 0, lean_box(0));
    lean_closure_set(v___x_2025_, 1, lean_box(0));
    lean_closure_set(v___x_2025_, 2, v_inst_2023_);
    lean_closure_set(v___x_2025_, 3, v_inst_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Lake_instComputeHashArrayOfMonad(
    mut v_00_u03b1_2026_: *mut LeanObject,
    mut v_m_2027_: *mut LeanObject,
    mut v_inst_2028_: *mut LeanObject,
    mut v_inst_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    v___x_2030_ = lean_alloc_closure(l_Lake_computeArrayHash as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_2030_, 0, lean_box(0));
    lean_closure_set(v___x_2030_, 1, lean_box(0));
    lean_closure_set(v___x_2030_, 2, v_inst_2028_);
    lean_closure_set(v___x_2030_, 3, v_inst_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lake_MTime_instOfNat___closed__0() -> *mut LeanObject {
    let mut v___x_2031_: u32 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = 0;
    v___x_2032_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5_once),
        _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5,
    );
    v___x_2033_ = lean_alloc_ctor(0, 1, (4) as u32);
    lean_ctor_set(v___x_2033_, 0, v___x_2032_);
    lean_ctor_set_uint32(
        v___x_2033_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2031_,
    );
    return v___x_2033_;
}
pub unsafe fn _init_l_Lake_MTime_instOfNat() -> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    return v___x_2034_;
}
pub unsafe fn l_Lake_MTime_instBEq___aux__1(
    mut v_x_2035_: *mut LeanObject,
    mut v_x_2036_: *mut LeanObject,
) -> u8 {
    let mut v___x_2037_: u8 = 0;
    v___x_2037_ = l_IO_FS_instBEqSystemTime_beq(v_x_2035_, v_x_2036_);
    return v___x_2037_;
}
pub unsafe fn l_Lake_MTime_instBEq___aux__1___boxed(
    mut v_x_2038_: *mut LeanObject,
    mut v_x_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2040_: u8 = 0;
    let mut v_r_2041_: *mut LeanObject = core::ptr::null_mut();
    v_res_2040_ = l_Lake_MTime_instBEq___aux__1(v_x_2038_, v_x_2039_);
    lean_dec_ref(v_x_2039_);
    lean_dec_ref(v_x_2038_);
    v_r_2041_ = lean_box((v_res_2040_) as usize);
    return v_r_2041_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___redArg(
    mut v_x_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    v___x_2045_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2044_);
    return v___x_2045_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___redArg___boxed(
    mut v_x_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2047_: *mut LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_2046_);
    lean_dec_ref(v_x_2046_);
    return v_res_2047_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1(
    mut v_x_2048_: *mut LeanObject,
    mut v_prec_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2048_);
    return v___x_2050_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___boxed(
    mut v_x_2051_: *mut LeanObject,
    mut v_prec_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2053_: *mut LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lake_MTime_instRepr___aux__1(v_x_2051_, v_prec_2052_);
    lean_dec(v_prec_2052_);
    lean_dec_ref(v_x_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Lake_MTime_instOrd___aux__1(
    mut v_x_2056_: *mut LeanObject,
    mut v_x_2057_: *mut LeanObject,
) -> u8 {
    let mut v___x_2058_: u8 = 0;
    v___x_2058_ = l_IO_FS_instOrdSystemTime_ord(v_x_2056_, v_x_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Lake_MTime_instOrd___aux__1___boxed(
    mut v_x_2059_: *mut LeanObject,
    mut v_x_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2061_: u8 = 0;
    let mut v_r_2062_: *mut LeanObject = core::ptr::null_mut();
    v_res_2061_ = l_Lake_MTime_instOrd___aux__1(v_x_2059_, v_x_2060_);
    lean_dec_ref(v_x_2060_);
    lean_dec_ref(v_x_2059_);
    v_r_2062_ = lean_box((v_res_2061_) as usize);
    return v_r_2062_;
}
pub unsafe fn _init_l_Lake_MTime_instLT() -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = lean_box(0);
    return v___x_2065_;
}
pub unsafe fn _init_l_Lake_MTime_instLE() -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2066_ = lean_box(0);
    return v___x_2066_;
}
pub unsafe fn l_Lake_MTime_instMin___lam__0(
    mut v_x_2067_: *mut LeanObject,
    mut v_y_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2069_: u8 = 0;
    v___x_2069_ = l_IO_FS_instOrdSystemTime_ord(v_x_2067_, v_y_2068_);
    if v___x_2069_ == 2 {
        lean_inc_ref(v_y_2068_);
        return v_y_2068_;
    } else {
        lean_inc_ref(v_x_2067_);
        return v_x_2067_;
    }
}
pub unsafe fn l_Lake_MTime_instMin___lam__0___boxed(
    mut v_x_2070_: *mut LeanObject,
    mut v_y_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2072_: *mut LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lake_MTime_instMin___lam__0(v_x_2070_, v_y_2071_);
    lean_dec_ref(v_y_2071_);
    lean_dec_ref(v_x_2070_);
    return v_res_2072_;
}
pub unsafe fn l_Lake_MTime_instMax___lam__0(
    mut v_x_2075_: *mut LeanObject,
    mut v_y_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2077_: u8 = 0;
    v___x_2077_ = l_IO_FS_instOrdSystemTime_ord(v_x_2075_, v_y_2076_);
    if v___x_2077_ == 2 {
        lean_inc_ref(v_x_2075_);
        return v_x_2075_;
    } else {
        lean_inc_ref(v_y_2076_);
        return v_y_2076_;
    }
}
pub unsafe fn l_Lake_MTime_instMax___lam__0___boxed(
    mut v_x_2078_: *mut LeanObject,
    mut v_y_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2080_: *mut LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lake_MTime_instMax___lam__0(v_x_2078_, v_y_2079_);
    lean_dec_ref(v_y_2079_);
    lean_dec_ref(v_x_2078_);
    return v_res_2080_;
}
pub unsafe fn _init_l_Lake_MTime_instNilTrace() -> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    return v___x_2083_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(
    mut v_inst_2085_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_inst_2085_);
    return v_inst_2085_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(
    mut v_inst_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_res_2087_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(
        v_inst_2086_,
    );
    lean_dec_ref(v_inst_2086_);
    return v_res_2087_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(
    mut v_00_u03b1_2088_: *mut LeanObject,
    mut v_inst_2089_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_inst_2089_);
    return v_inst_2089_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(
    mut v_00_u03b1_2090_: *mut LeanObject,
    mut v_inst_2091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2092_: *mut LeanObject = core::ptr::null_mut();
    v_res_2092_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(
        v_00_u03b1_2090_,
        v_inst_2091_,
    );
    lean_dec_ref(v_inst_2091_);
    return v_res_2092_;
}
pub unsafe fn l_Lake_getFileMTime(mut v_file_2093_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v_modified_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_a_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2108_: u8 = 0;
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2095_ = lean_io_metadata(v_file_2093_);
                if lean_obj_tag(v___x_2095_) == 0 {
                    v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2104_ = (!lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2104_ == 0 {
                        v___x_2098_ = v___x_2095_;
                        v_isShared_2099_ = v_isSharedCheck_2104_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2096_);
                        lean_dec(v___x_2095_);
                        v___x_2098_ = lean_box(0);
                        v_isShared_2099_ = v_isSharedCheck_2104_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2105_ = lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2112_ = (!lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2112_ == 0 {
                        v___x_2107_ = v___x_2095_;
                        v_isShared_2108_ = v_isSharedCheck_2112_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2105_);
                        lean_dec(v___x_2095_);
                        v___x_2107_ = lean_box(0);
                        v_isShared_2108_ = v_isSharedCheck_2112_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_modified_2100_ = lean_ctor_get(v_a_2096_, 1);
                lean_inc_ref(v_modified_2100_);
                lean_dec(v_a_2096_);
                if v_isShared_2099_ == 0 {
                    lean_ctor_set(v___x_2098_, 0, v_modified_2100_);
                    v___x_2102_ = v___x_2098_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_modified_2100_);
                    v___x_2102_ = v_reuseFailAlloc_2103_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2102_;
            }
            3 => {
                if v_isShared_2108_ == 0 {
                    v___x_2110_ = v___x_2107_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
                    v___x_2110_ = v_reuseFailAlloc_2111_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getFileMTime___boxed(
    mut v_file_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2115_: *mut LeanObject = core::ptr::null_mut();
    v_res_2115_ = l_Lake_getFileMTime(v_file_2113_);
    lean_dec_ref(v_file_2113_);
    return v_res_2115_;
}
pub unsafe fn l_Lake_instGetMTimeTextFilePath___lam__0(
    mut v_x_2118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v_modified_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut v_a_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2120_ = lean_io_metadata(v_x_2118_);
                if lean_obj_tag(v___x_2120_) == 0 {
                    v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2129_ = (!lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2123_ = v___x_2120_;
                        v_isShared_2124_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2121_);
                        lean_dec(v___x_2120_);
                        v___x_2123_ = lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2130_ = lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2137_ = (!lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2132_ = v___x_2120_;
                        v_isShared_2133_ = v_isSharedCheck_2137_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2130_);
                        lean_dec(v___x_2120_);
                        v___x_2132_ = lean_box(0);
                        v_isShared_2133_ = v_isSharedCheck_2137_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_modified_2125_ = lean_ctor_get(v_a_2121_, 1);
                lean_inc_ref(v_modified_2125_);
                lean_dec(v_a_2121_);
                if v_isShared_2124_ == 0 {
                    lean_ctor_set(v___x_2123_, 0, v_modified_2125_);
                    v___x_2127_ = v___x_2123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_modified_2125_);
                    v___x_2127_ = v_reuseFailAlloc_2128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2127_;
            }
            3 => {
                if v_isShared_2133_ == 0 {
                    v___x_2135_ = v___x_2132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
                    v___x_2135_ = v_reuseFailAlloc_2136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instGetMTimeTextFilePath___lam__0___boxed(
    mut v_x_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_2138_);
    lean_dec_ref(v_x_2138_);
    return v_res_2140_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate___redArg(
    mut v_inst_2143_: *mut LeanObject,
    mut v_info_2144_: *mut LeanObject,
    mut v_self_2145_: *mut LeanObject,
) -> u8 {
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    v___x_2147_ = lean_apply_2(v_inst_2143_, v_info_2144_, lean_box(0));
    if lean_obj_tag(v___x_2147_) == 0 {
        let mut v_a_2148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: u8 = 0;
        v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
        lean_inc(v_a_2148_);
        lean_dec_ref_known(v___x_2147_, 1);
        v___x_2149_ = l_IO_FS_instOrdSystemTime_ord(v_self_2145_, v_a_2148_);
        lean_dec(v_a_2148_);
        if v___x_2149_ == 0 {
            let mut v___x_2150_: u8 = 0;
            v___x_2150_ = 1;
            return v___x_2150_;
        } else {
            let mut v___x_2151_: u8 = 0;
            v___x_2151_ = 0;
            return v___x_2151_;
        }
    } else {
        let mut v___x_2152_: u8 = 0;
        lean_dec_ref_known(v___x_2147_, 1);
        v___x_2152_ = 0;
        return v___x_2152_;
    }
}
pub unsafe fn l_Lake_MTime_checkUpToDate___redArg___boxed(
    mut v_inst_2153_: *mut LeanObject,
    mut v_info_2154_: *mut LeanObject,
    mut v_self_2155_: *mut LeanObject,
    mut v_a_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2153_, v_info_2154_, v_self_2155_);
    lean_dec_ref(v_self_2155_);
    v_r_2158_ = lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate(
    mut v_i_2159_: *mut LeanObject,
    mut v_inst_2160_: *mut LeanObject,
    mut v_info_2161_: *mut LeanObject,
    mut v_self_2162_: *mut LeanObject,
) -> u8 {
    let mut v___x_2164_: u8 = 0;
    v___x_2164_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2160_, v_info_2161_, v_self_2162_);
    return v___x_2164_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate___boxed(
    mut v_i_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
    mut v_info_2167_: *mut LeanObject,
    mut v_self_2168_: *mut LeanObject,
    mut v_a_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2170_: u8 = 0;
    let mut v_r_2171_: *mut LeanObject = core::ptr::null_mut();
    v_res_2170_ = l_Lake_MTime_checkUpToDate(v_i_2165_, v_inst_2166_, v_info_2167_, v_self_2168_);
    lean_dec_ref(v_self_2168_);
    v_r_2171_ = lean_box((v_res_2170_) as usize);
    return v_r_2171_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    v___x_2181_ = lean_unsigned_to_nat(11);
    v___x_2182_ = lean_nat_to_int(v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2189_ = lean_unsigned_to_nat(10);
    v___x_2190_ = lean_nat_to_int(v___x_2189_);
    return v___x_2190_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(
    mut v_x_2194_: *mut LeanObject,
    mut v_x_2195_: *mut LeanObject,
    mut v_x_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2196_) == 0 {
                    lean_dec(v_x_2194_);
                    return v_x_2195_;
                } else {
                    v_head_2197_ = lean_ctor_get(v_x_2196_, 0);
                    v_tail_2198_ = lean_ctor_get(v_x_2196_, 1);
                    v_isSharedCheck_2208_ = (!lean_is_exclusive(v_x_2196_)) as u8;
                    if v_isSharedCheck_2208_ == 0 {
                        v___x_2200_ = v_x_2196_;
                        v_isShared_2201_ = v_isSharedCheck_2208_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2198_);
                        lean_inc(v_head_2197_);
                        lean_dec(v_x_2196_);
                        v___x_2200_ = lean_box(0);
                        v_isShared_2201_ = v_isSharedCheck_2208_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2194_);
                if v_isShared_2201_ == 0 {
                    lean_ctor_set_tag(v___x_2200_, 5);
                    lean_ctor_set(v___x_2200_, 1, v_x_2194_);
                    lean_ctor_set(v___x_2200_, 0, v_x_2195_);
                    v___x_2203_ = v___x_2200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2207_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_x_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_x_2194_);
                    v___x_2203_ = v_reuseFailAlloc_2207_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2204_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2197_);
                v___x_2205_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2205_, 0, v___x_2203_);
                lean_ctor_set(v___x_2205_, 1, v___x_2204_);
                v___x_2206_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_2194_, v___x_2205_, v_tail_2198_);
                return v___x_2206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(
    mut v_x_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2209_) == 0 {
        let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2210_);
        v___x_2211_ = lean_box(0);
        return v___x_2211_;
    } else {
        let mut v_tail_2212_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2212_ = lean_ctor_get(v_x_2209_, 1);
        if lean_obj_tag(v_tail_2212_) == 0 {
            let mut v_head_2213_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2210_);
            v_head_2213_ = lean_ctor_get(v_x_2209_, 0);
            lean_inc(v_head_2213_);
            lean_dec_ref_known(v_x_2209_, 2);
            v___x_2214_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2213_);
            return v___x_2214_;
        } else {
            let mut v_head_2215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2212_);
            v_head_2215_ = lean_ctor_get(v_x_2209_, 0);
            lean_inc(v_head_2215_);
            lean_dec_ref_known(v_x_2209_, 2);
            v___x_2216_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2215_);
            v___x_2217_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_2210_, v___x_2216_, v_tail_2212_);
            return v___x_2217_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    v___x_2219_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0;
    v___x_2220_ = lean_string_length(v___x_2219_);
    return v___x_2220_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    v___x_2221_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5,
    );
    v___x_2222_ = lean_nat_to_int(v___x_2221_);
    return v___x_2222_;
}
pub unsafe fn l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(
    mut v_xs_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    v___x_2232_ = lean_array_get_size(v_xs_2231_);
    v___x_2233_ = lean_unsigned_to_nat(0);
    v___x_2234_ = lean_nat_dec_eq(v___x_2232_, v___x_2233_);
    if v___x_2234_ == 0 {
        let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        v___x_2235_ = lean_array_to_list(v_xs_2231_);
        v___x_2236_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3;
        v___x_2237_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_2235_, v___x_2236_);
        v___x_2238_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6,
        );
        v___x_2239_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7;
        v___x_2240_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2240_, 0, v___x_2239_);
        lean_ctor_set(v___x_2240_, 1, v___x_2237_);
        v___x_2241_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8;
        v___x_2242_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2242_, 0, v___x_2240_);
        lean_ctor_set(v___x_2242_, 1, v___x_2241_);
        v___x_2243_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2243_, 0, v___x_2238_);
        lean_ctor_set(v___x_2243_, 1, v___x_2242_);
        v___x_2244_ = l_Std_Format_fill(v___x_2243_);
        return v___x_2244_;
    } else {
        let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2231_);
        v___x_2245_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10;
        return v___x_2245_;
    }
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2249_ = lean_unsigned_to_nat(8);
    v___x_2250_ = lean_nat_to_int(v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13() -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = lean_unsigned_to_nat(9);
    v___x_2255_ = lean_nat_to_int(v___x_2254_);
    return v___x_2255_;
}
pub unsafe fn l_Lake_instReprBuildTrace_repr___redArg(
    mut v_x_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_caption_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inputs_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_2259_: u64 = 0;
    let mut v_mtime_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    v_caption_2257_ = lean_ctor_get(v_x_2256_, 0);
    lean_inc_ref(v_caption_2257_);
    v_inputs_2258_ = lean_ctor_get(v_x_2256_, 1);
    lean_inc_ref(v_inputs_2258_);
    v_hash_2259_ = lean_ctor_get_uint64(
        v_x_2256_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_mtime_2260_ = lean_ctor_get(v_x_2256_, 2);
    lean_inc_ref(v_mtime_2260_);
    lean_dec_ref(v_x_2256_);
    v___x_2261_ = l_Lake_instReprHash_repr___redArg___closed__5;
    v___x_2262_ = l_Lake_instReprBuildTrace_repr___redArg___closed__3;
    v___x_2263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__4_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4,
    );
    v___x_2264_ = l_String_quote(v_caption_2257_);
    v___x_2265_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2265_, 0, v___x_2264_);
    v___x_2266_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2266_, 0, v___x_2263_);
    lean_ctor_set(v___x_2266_, 1, v___x_2265_);
    v___x_2267_ = 0;
    v___x_2268_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2268_, 0, v___x_2266_);
    lean_ctor_set_uint8(
        v___x_2268_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2269_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2269_, 0, v___x_2262_);
    lean_ctor_set(v___x_2269_, 1, v___x_2268_);
    v___x_2270_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2;
    v___x_2271_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2271_, 0, v___x_2269_);
    lean_ctor_set(v___x_2271_, 1, v___x_2270_);
    v___x_2272_ = lean_box(1);
    v___x_2273_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2273_, 0, v___x_2271_);
    lean_ctor_set(v___x_2273_, 1, v___x_2272_);
    v___x_2274_ = l_Lake_instReprBuildTrace_repr___redArg___closed__6;
    v___x_2275_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2275_, 0, v___x_2273_);
    lean_ctor_set(v___x_2275_, 1, v___x_2274_);
    v___x_2276_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2276_, 0, v___x_2275_);
    lean_ctor_set(v___x_2276_, 1, v___x_2261_);
    v___x_2277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__7_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7,
    );
    v___x_2278_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_2258_);
    v___x_2279_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2280_, 0, v___x_2279_);
    lean_ctor_set_uint8(
        v___x_2280_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2281_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2281_, 0, v___x_2276_);
    lean_ctor_set(v___x_2281_, 1, v___x_2280_);
    v___x_2282_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    lean_ctor_set(v___x_2282_, 1, v___x_2270_);
    v___x_2283_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    lean_ctor_set(v___x_2283_, 1, v___x_2272_);
    v___x_2284_ = l_Lake_instReprBuildTrace_repr___redArg___closed__9;
    v___x_2285_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2285_, 0, v___x_2283_);
    lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    v___x_2286_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    lean_ctor_set(v___x_2286_, 1, v___x_2261_);
    v___x_2287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__10_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10,
    );
    v___x_2288_ = l_Lake_instReprHash_repr___redArg(v_hash_2259_);
    v___x_2289_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2289_, 0, v___x_2287_);
    lean_ctor_set(v___x_2289_, 1, v___x_2288_);
    v___x_2290_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2290_, 0, v___x_2289_);
    lean_ctor_set_uint8(
        v___x_2290_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2291_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2291_, 0, v___x_2286_);
    lean_ctor_set(v___x_2291_, 1, v___x_2290_);
    v___x_2292_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    lean_ctor_set(v___x_2292_, 1, v___x_2270_);
    v___x_2293_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2293_, 0, v___x_2292_);
    lean_ctor_set(v___x_2293_, 1, v___x_2272_);
    v___x_2294_ = l_Lake_instReprBuildTrace_repr___redArg___closed__12;
    v___x_2295_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2295_, 0, v___x_2293_);
    lean_ctor_set(v___x_2295_, 1, v___x_2294_);
    v___x_2296_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2296_, 0, v___x_2295_);
    lean_ctor_set(v___x_2296_, 1, v___x_2261_);
    v___x_2297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__13_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13,
    );
    v___x_2298_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_2260_);
    lean_dec_ref(v_mtime_2260_);
    v___x_2299_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2299_, 0, v___x_2297_);
    lean_ctor_set(v___x_2299_, 1, v___x_2298_);
    v___x_2300_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    lean_ctor_set_uint8(
        v___x_2300_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2301_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2301_, 0, v___x_2296_);
    lean_ctor_set(v___x_2301_, 1, v___x_2300_);
    v___x_2302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__10,
    );
    v___x_2303_ = l_Lake_instReprHash_repr___redArg___closed__11;
    v___x_2304_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2304_, 0, v___x_2303_);
    lean_ctor_set(v___x_2304_, 1, v___x_2301_);
    v___x_2305_ = l_Lake_instReprHash_repr___redArg___closed__12;
    v___x_2306_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2306_, 0, v___x_2304_);
    lean_ctor_set(v___x_2306_, 1, v___x_2305_);
    v___x_2307_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2307_, 0, v___x_2302_);
    lean_ctor_set(v___x_2307_, 1, v___x_2306_);
    v___x_2308_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    lean_ctor_set_uint8(
        v___x_2308_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    return v___x_2308_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_2309_: *mut LeanObject,
    mut v_x_2310_: *mut LeanObject,
    mut v_x_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2311_) == 0 {
                    lean_dec(v_x_2309_);
                    return v_x_2310_;
                } else {
                    v_head_2312_ = lean_ctor_get(v_x_2311_, 0);
                    v_tail_2313_ = lean_ctor_get(v_x_2311_, 1);
                    v_isSharedCheck_2323_ = (!lean_is_exclusive(v_x_2311_)) as u8;
                    if v_isSharedCheck_2323_ == 0 {
                        v___x_2315_ = v_x_2311_;
                        v_isShared_2316_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2313_);
                        lean_inc(v_head_2312_);
                        lean_dec(v_x_2311_);
                        v___x_2315_ = lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2309_);
                if v_isShared_2316_ == 0 {
                    lean_ctor_set_tag(v___x_2315_, 5);
                    lean_ctor_set(v___x_2315_, 1, v_x_2309_);
                    lean_ctor_set(v___x_2315_, 0, v_x_2310_);
                    v___x_2318_ = v___x_2315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_x_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_x_2309_);
                    v___x_2318_ = v_reuseFailAlloc_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2319_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2312_);
                v___x_2320_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2320_, 0, v___x_2318_);
                lean_ctor_set(v___x_2320_, 1, v___x_2319_);
                v_x_2310_ = v___x_2320_;
                v_x_2311_ = v_tail_2313_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprBuildTrace_repr(
    mut v_x_2324_: *mut LeanObject,
    mut v_prec_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    v___x_2326_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_2324_);
    return v___x_2326_;
}
pub unsafe fn l_Lake_instReprBuildTrace_repr___boxed(
    mut v_x_2327_: *mut LeanObject,
    mut v_prec_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lake_instReprBuildTrace_repr(v_x_2327_, v_prec_2328_);
    lean_dec(v_prec_2328_);
    return v_res_2329_;
}
pub unsafe fn l_Lake_BuildTrace_withCaption(
    mut v_caption_2332_: *mut LeanObject,
    mut v_self_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inputs_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_2335_: u64 = 0;
    let mut v_mtime_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2339_: u8 = 0;
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inputs_2334_ = lean_ctor_get(v_self_2333_, 1);
                v_hash_2335_ = lean_ctor_get_uint64(
                    v_self_2333_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_2336_ = lean_ctor_get(v_self_2333_, 2);
                v_isSharedCheck_2343_ = (!lean_is_exclusive(v_self_2333_)) as u8;
                if v_isSharedCheck_2343_ == 0 {
                    v_unused_2344_ = lean_ctor_get(v_self_2333_, 0);
                    lean_dec(v_unused_2344_);
                    v___x_2338_ = v_self_2333_;
                    v_isShared_2339_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mtime_2336_);
                    lean_inc(v_inputs_2334_);
                    lean_dec(v_self_2333_);
                    v___x_2338_ = lean_box(0);
                    v_isShared_2339_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2339_ == 0 {
                    lean_ctor_set(v___x_2338_, 0, v_caption_2332_);
                    v___x_2341_ = v___x_2338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_caption_2332_);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_inputs_2334_);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_mtime_2336_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2342_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_hash_2335_,
                    );
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildTrace_withoutInputs(
    mut v_self_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_caption_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_2349_: u64 = 0;
    let mut v_mtime_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_unused_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_caption_2348_ = lean_ctor_get(v_self_2347_, 0);
                v_hash_2349_ = lean_ctor_get_uint64(
                    v_self_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_2350_ = lean_ctor_get(v_self_2347_, 2);
                v_isSharedCheck_2358_ = (!lean_is_exclusive(v_self_2347_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v_unused_2359_ = lean_ctor_get(v_self_2347_, 1);
                    lean_dec(v_unused_2359_);
                    v___x_2352_ = v_self_2347_;
                    v_isShared_2353_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mtime_2350_);
                    lean_inc(v_caption_2348_);
                    lean_dec(v_self_2347_);
                    v___x_2352_ = lean_box(0);
                    v_isShared_2353_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2354_ = l_Lake_BuildTrace_withoutInputs___closed__0;
                if v_isShared_2353_ == 0 {
                    lean_ctor_set(v___x_2352_, 1, v___x_2354_);
                    v___x_2356_ = v___x_2352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_caption_2348_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_mtime_2350_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2357_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_hash_2349_,
                    );
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildTrace_ofHash(
    mut v_hash_2360_: u64,
    mut v_caption_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2364_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_2364_, 0, v_caption_2361_);
    lean_ctor_set(v___x_2364_, 1, v___x_2362_);
    lean_ctor_set(v___x_2364_, 2, v___x_2363_);
    lean_ctor_set_uint64(
        v___x_2364_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_hash_2360_,
    );
    return v___x_2364_;
}
pub unsafe fn l_Lake_BuildTrace_ofHash___boxed(
    mut v_hash_2365_: *mut LeanObject,
    mut v_caption_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_boxed_2367_: u64 = 0;
    let mut v_res_2368_: *mut LeanObject = core::ptr::null_mut();
    v_hash_boxed_2367_ = lean_unbox_uint64(v_hash_2365_);
    lean_dec_ref(v_hash_2365_);
    v_res_2368_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_2367_, v_caption_2366_);
    return v_res_2368_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeHash___lam__0(mut v_hash_2370_: u64) -> *mut LeanObject {
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lake_BuildTrace_instCoeHash___lam__0___closed__0;
    v___x_2372_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2374_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_2374_, 0, v___x_2371_);
    lean_ctor_set(v___x_2374_, 1, v___x_2372_);
    lean_ctor_set(v___x_2374_, 2, v___x_2373_);
    lean_ctor_set_uint64(
        v___x_2374_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_hash_2370_,
    );
    return v___x_2374_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeHash___lam__0___boxed(
    mut v_hash_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_boxed_2376_: u64 = 0;
    let mut v_res_2377_: *mut LeanObject = core::ptr::null_mut();
    v_hash_boxed_2376_ = lean_unbox_uint64(v_hash_2375_);
    lean_dec_ref(v_hash_2375_);
    v_res_2377_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_2376_);
    return v_res_2377_;
}
pub unsafe fn l_Lake_BuildTrace_ofMTime(
    mut v_mtime_2380_: *mut LeanObject,
    mut v_caption_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u64 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    v___x_2382_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2383_ = 1723u64;
    v___x_2384_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_2384_, 0, v_caption_2381_);
    lean_ctor_set(v___x_2384_, 1, v___x_2382_);
    lean_ctor_set(v___x_2384_, 2, v_mtime_2380_);
    lean_ctor_set_uint64(
        v___x_2384_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeMTime___lam__0(
    mut v_mtime_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u64 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0;
    v___x_2388_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2389_ = 1723u64;
    v___x_2390_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_2390_, 0, v___x_2387_);
    lean_ctor_set(v___x_2390_, 1, v___x_2388_);
    lean_ctor_set(v___x_2390_, 2, v_mtime_2386_);
    lean_ctor_set_uint64(
        v___x_2390_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2389_,
    );
    return v___x_2390_;
}
pub unsafe fn l_Lake_BuildTrace_nil(mut v_caption_2393_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: u64 = 0;
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2395_ = 1723u64;
    v___x_2396_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2397_ = lean_alloc_ctor(0, 3, (8) as u32);
    lean_ctor_set(v___x_2397_, 0, v_caption_2393_);
    lean_ctor_set(v___x_2397_, 1, v___x_2394_);
    lean_ctor_set(v___x_2397_, 2, v___x_2396_);
    lean_ctor_set_uint64(
        v___x_2397_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2395_,
    );
    return v___x_2397_;
}
pub unsafe fn _init_l_Lake_BuildTrace_instNilTrace___closed__1() -> *mut LeanObject {
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    v___x_2399_ = l_Lake_BuildTrace_instNilTrace___closed__0;
    v___x_2400_ = l_Lake_BuildTrace_nil(v___x_2399_);
    return v___x_2400_;
}
pub unsafe fn _init_l_Lake_BuildTrace_instNilTrace() -> *mut LeanObject {
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    v___x_2401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_BuildTrace_instNilTrace___closed__1),
        core::ptr::addr_of_mut!(l_Lake_BuildTrace_instNilTrace___closed__1_once),
        _init_l_Lake_BuildTrace_instNilTrace___closed__1,
    );
    return v___x_2401_;
}
pub unsafe fn l_Lake_BuildTrace_compute___redArg(
    mut v_inst_2402_: *mut LeanObject,
    mut v_inst_2403_: *mut LeanObject,
    mut v_inst_2404_: *mut LeanObject,
    mut v_inst_2405_: *mut LeanObject,
    mut v_info_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u64 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut v_a_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_a_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_info_2406_);
                v___x_2408_ = lean_apply_1(v_inst_2403_, v_info_2406_);
                v___x_2409_ = lean_apply_3(v_inst_2404_, lean_box(0), v___x_2408_, lean_box(0));
                if lean_obj_tag(v___x_2409_) == 0 {
                    v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
                    lean_inc(v_a_2410_);
                    lean_dec_ref_known(v___x_2409_, 1);
                    lean_inc(v_info_2406_);
                    v___x_2411_ = lean_apply_2(v_inst_2405_, v_info_2406_, lean_box(0));
                    if lean_obj_tag(v___x_2411_) == 0 {
                        v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
                        v_isSharedCheck_2423_ = (!lean_is_exclusive(v___x_2411_)) as u8;
                        if v_isSharedCheck_2423_ == 0 {
                            v___x_2414_ = v___x_2411_;
                            v_isShared_2415_ = v_isSharedCheck_2423_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2412_);
                            lean_dec(v___x_2411_);
                            v___x_2414_ = lean_box(0);
                            v_isShared_2415_ = v_isSharedCheck_2423_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2410_);
                        lean_dec(v_info_2406_);
                        lean_dec_ref(v_inst_2402_);
                        v_a_2424_ = lean_ctor_get(v___x_2411_, 0);
                        v_isSharedCheck_2431_ = (!lean_is_exclusive(v___x_2411_)) as u8;
                        if v_isSharedCheck_2431_ == 0 {
                            v___x_2426_ = v___x_2411_;
                            v_isShared_2427_ = v_isSharedCheck_2431_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2424_);
                            lean_dec(v___x_2411_);
                            v___x_2426_ = lean_box(0);
                            v_isShared_2427_ = v_isSharedCheck_2431_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_info_2406_);
                    lean_dec_ref(v_inst_2405_);
                    lean_dec_ref(v_inst_2402_);
                    v_a_2432_ = lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2439_ = (!lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2439_ == 0 {
                        v___x_2434_ = v___x_2409_;
                        v_isShared_2435_ = v_isSharedCheck_2439_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2432_);
                        lean_dec(v___x_2409_);
                        v___x_2434_ = lean_box(0);
                        v_isShared_2435_ = v_isSharedCheck_2439_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2416_ = lean_apply_1(v_inst_2402_, v_info_2406_);
                v___x_2417_ = l_Lake_BuildTrace_withoutInputs___closed__0;
                v___x_2418_ = lean_alloc_ctor(0, 3, (8) as u32);
                lean_ctor_set(v___x_2418_, 0, v___x_2416_);
                lean_ctor_set(v___x_2418_, 1, v___x_2417_);
                lean_ctor_set(v___x_2418_, 2, v_a_2412_);
                v___x_2419_ = lean_unbox_uint64(v_a_2410_);
                lean_dec(v_a_2410_);
                lean_ctor_set_uint64(
                    v___x_2418_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2419_,
                );
                if v_isShared_2415_ == 0 {
                    lean_ctor_set(v___x_2414_, 0, v___x_2418_);
                    v___x_2421_ = v___x_2414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2418_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2421_;
            }
            3 => {
                if v_isShared_2427_ == 0 {
                    v___x_2429_ = v___x_2426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
                    v___x_2429_ = v_reuseFailAlloc_2430_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2429_;
            }
            5 => {
                if v_isShared_2435_ == 0 {
                    v___x_2437_ = v___x_2434_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
                    v___x_2437_ = v_reuseFailAlloc_2438_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildTrace_compute___redArg___boxed(
    mut v_inst_2440_: *mut LeanObject,
    mut v_inst_2441_: *mut LeanObject,
    mut v_inst_2442_: *mut LeanObject,
    mut v_inst_2443_: *mut LeanObject,
    mut v_info_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Lake_BuildTrace_compute___redArg(
        v_inst_2440_,
        v_inst_2441_,
        v_inst_2442_,
        v_inst_2443_,
        v_info_2444_,
    );
    return v_res_2446_;
}
pub unsafe fn l_Lake_BuildTrace_compute(
    mut v_00_u03b1_2447_: *mut LeanObject,
    mut v_m_2448_: *mut LeanObject,
    mut v_inst_2449_: *mut LeanObject,
    mut v_inst_2450_: *mut LeanObject,
    mut v_inst_2451_: *mut LeanObject,
    mut v_inst_2452_: *mut LeanObject,
    mut v_info_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lake_BuildTrace_compute___redArg(
        v_inst_2449_,
        v_inst_2450_,
        v_inst_2451_,
        v_inst_2452_,
        v_info_2453_,
    );
    return v___x_2455_;
}
pub unsafe fn l_Lake_BuildTrace_compute___boxed(
    mut v_00_u03b1_2456_: *mut LeanObject,
    mut v_m_2457_: *mut LeanObject,
    mut v_inst_2458_: *mut LeanObject,
    mut v_inst_2459_: *mut LeanObject,
    mut v_inst_2460_: *mut LeanObject,
    mut v_inst_2461_: *mut LeanObject,
    mut v_info_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2464_: *mut LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Lake_BuildTrace_compute(
        v_00_u03b1_2456_,
        v_m_2457_,
        v_inst_2458_,
        v_inst_2459_,
        v_inst_2460_,
        v_inst_2461_,
        v_info_2462_,
    );
    return v_res_2464_;
}
pub unsafe fn l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(
    mut v_inst_2465_: *mut LeanObject,
    mut v_inst_2466_: *mut LeanObject,
    mut v_inst_2467_: *mut LeanObject,
    mut v_inst_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = lean_alloc_closure(
        l_Lake_BuildTrace_compute___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___x_2469_, 0, lean_box(0));
    lean_closure_set(v___x_2469_, 1, lean_box(0));
    lean_closure_set(v___x_2469_, 2, v_inst_2465_);
    lean_closure_set(v___x_2469_, 3, v_inst_2466_);
    lean_closure_set(v___x_2469_, 4, v_inst_2467_);
    lean_closure_set(v___x_2469_, 5, v_inst_2468_);
    return v___x_2469_;
}
pub unsafe fn l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(
    mut v_00_u03b1_2470_: *mut LeanObject,
    mut v_m_2471_: *mut LeanObject,
    mut v_inst_2472_: *mut LeanObject,
    mut v_inst_2473_: *mut LeanObject,
    mut v_inst_2474_: *mut LeanObject,
    mut v_inst_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = lean_alloc_closure(
        l_Lake_BuildTrace_compute___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___x_2476_, 0, lean_box(0));
    lean_closure_set(v___x_2476_, 1, lean_box(0));
    lean_closure_set(v___x_2476_, 2, v_inst_2472_);
    lean_closure_set(v___x_2476_, 3, v_inst_2473_);
    lean_closure_set(v___x_2476_, 4, v_inst_2474_);
    lean_closure_set(v___x_2476_, 5, v_inst_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lake_BuildTrace_mix(
    mut v_t1_2477_: *mut LeanObject,
    mut v_t2_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_caption_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inputs_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_2481_: u64 = 0;
    let mut v_mtime_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v_hash_2486_: u64 = 0;
    let mut v_mtime_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u64 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_caption_2479_ = lean_ctor_get(v_t1_2477_, 0);
                v_inputs_2480_ = lean_ctor_get(v_t1_2477_, 1);
                v_hash_2481_ = lean_ctor_get_uint64(
                    v_t1_2477_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_2482_ = lean_ctor_get(v_t1_2477_, 2);
                v_isSharedCheck_2497_ = (!lean_is_exclusive(v_t1_2477_)) as u8;
                if v_isSharedCheck_2497_ == 0 {
                    v___x_2484_ = v_t1_2477_;
                    v_isShared_2485_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mtime_2482_);
                    lean_inc(v_inputs_2480_);
                    lean_inc(v_caption_2479_);
                    lean_dec(v_t1_2477_);
                    v___x_2484_ = lean_box(0);
                    v_isShared_2485_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hash_2486_ = lean_ctor_get_uint64(
                    v_t2_2478_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_2487_ = lean_ctor_get(v_t2_2478_, 2);
                lean_inc_ref(v_mtime_2487_);
                v___x_2488_ = lean_array_push(v_inputs_2480_, v_t2_2478_);
                v___x_2489_ = lean_uint64_mix_hash(v_hash_2481_, v_hash_2486_);
                v___x_2490_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_2482_, v_mtime_2487_);
                if v___x_2490_ == 2 {
                    lean_dec_ref(v_mtime_2487_);
                    if v_isShared_2485_ == 0 {
                        lean_ctor_set(v___x_2484_, 1, v___x_2488_);
                        v___x_2492_ = v___x_2484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 3, (8) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_caption_2479_);
                        lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2488_);
                        lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_mtime_2482_);
                        v___x_2492_ = v_reuseFailAlloc_2493_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mtime_2482_);
                    if v_isShared_2485_ == 0 {
                        lean_ctor_set(v___x_2484_, 2, v_mtime_2487_);
                        lean_ctor_set(v___x_2484_, 1, v___x_2488_);
                        v___x_2495_ = v___x_2484_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 3, (8) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_caption_2479_);
                        lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2488_);
                        lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_mtime_2487_);
                        v___x_2495_ = v_reuseFailAlloc_2496_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint64(
                    v___x_2492_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2489_,
                );
                return v___x_2492_;
            }
            3 => {
                lean_ctor_set_uint64(
                    v___x_2495_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2489_,
                );
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash___redArg(
    mut v_inst_2500_: *mut LeanObject,
    mut v_info_2501_: *mut LeanObject,
    mut v_hash_2502_: u64,
    mut v_self_2503_: *mut LeanObject,
) -> u8 {
    let mut v_hash_2505_: u64 = 0;
    let mut v___x_2506_: u8 = 0;
    v_hash_2505_ = lean_ctor_get_uint64(
        v_self_2503_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v___x_2506_ = lean_uint64_dec_eq(v_hash_2502_, v_hash_2505_);
    if v___x_2506_ == 0 {
        lean_dec(v_info_2501_);
        lean_dec_ref(v_inst_2500_);
        return v___x_2506_;
    } else {
        let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: u8 = 0;
        v___x_2507_ = lean_apply_2(v_inst_2500_, v_info_2501_, lean_box(0));
        v___x_2508_ = (lean_unbox(v___x_2507_) as u8);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(
    mut v_inst_2509_: *mut LeanObject,
    mut v_info_2510_: *mut LeanObject,
    mut v_hash_2511_: *mut LeanObject,
    mut v_self_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_boxed_2514_: u64 = 0;
    let mut v_res_2515_: u8 = 0;
    let mut v_r_2516_: *mut LeanObject = core::ptr::null_mut();
    v_hash_boxed_2514_ = lean_unbox_uint64(v_hash_2511_);
    lean_dec_ref(v_hash_2511_);
    v_res_2515_ = l_Lake_BuildTrace_checkAgainstHash___redArg(
        v_inst_2509_,
        v_info_2510_,
        v_hash_boxed_2514_,
        v_self_2512_,
    );
    lean_dec_ref(v_self_2512_);
    v_r_2516_ = lean_box((v_res_2515_) as usize);
    return v_r_2516_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash(
    mut v_i_2517_: *mut LeanObject,
    mut v_inst_2518_: *mut LeanObject,
    mut v_info_2519_: *mut LeanObject,
    mut v_hash_2520_: u64,
    mut v_self_2521_: *mut LeanObject,
) -> u8 {
    let mut v___x_2523_: u8 = 0;
    v___x_2523_ = l_Lake_BuildTrace_checkAgainstHash___redArg(
        v_inst_2518_,
        v_info_2519_,
        v_hash_2520_,
        v_self_2521_,
    );
    return v___x_2523_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash___boxed(
    mut v_i_2524_: *mut LeanObject,
    mut v_inst_2525_: *mut LeanObject,
    mut v_info_2526_: *mut LeanObject,
    mut v_hash_2527_: *mut LeanObject,
    mut v_self_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_boxed_2530_: u64 = 0;
    let mut v_res_2531_: u8 = 0;
    let mut v_r_2532_: *mut LeanObject = core::ptr::null_mut();
    v_hash_boxed_2530_ = lean_unbox_uint64(v_hash_2527_);
    lean_dec_ref(v_hash_2527_);
    v_res_2531_ = l_Lake_BuildTrace_checkAgainstHash(
        v_i_2524_,
        v_inst_2525_,
        v_info_2526_,
        v_hash_boxed_2530_,
        v_self_2528_,
    );
    lean_dec_ref(v_self_2528_);
    v_r_2532_ = lean_box((v_res_2531_) as usize);
    return v_r_2532_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___redArg(
    mut v_inst_2533_: *mut LeanObject,
    mut v_info_2534_: *mut LeanObject,
    mut v_self_2535_: *mut LeanObject,
) -> u8 {
    let mut v_mtime_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    v_mtime_2537_ = lean_ctor_get(v_self_2535_, 2);
    v___x_2538_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2533_, v_info_2534_, v_mtime_2537_);
    return v___x_2538_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(
    mut v_inst_2539_: *mut LeanObject,
    mut v_info_2540_: *mut LeanObject,
    mut v_self_2541_: *mut LeanObject,
    mut v_a_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2543_: u8 = 0;
    let mut v_r_2544_: *mut LeanObject = core::ptr::null_mut();
    v_res_2543_ =
        l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_2539_, v_info_2540_, v_self_2541_);
    lean_dec_ref(v_self_2541_);
    v_r_2544_ = lean_box((v_res_2543_) as usize);
    return v_r_2544_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime(
    mut v_i_2545_: *mut LeanObject,
    mut v_inst_2546_: *mut LeanObject,
    mut v_info_2547_: *mut LeanObject,
    mut v_self_2548_: *mut LeanObject,
) -> u8 {
    let mut v_mtime_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    v_mtime_2550_ = lean_ctor_get(v_self_2548_, 2);
    v___x_2551_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2546_, v_info_2547_, v_mtime_2550_);
    return v___x_2551_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___boxed(
    mut v_i_2552_: *mut LeanObject,
    mut v_inst_2553_: *mut LeanObject,
    mut v_info_2554_: *mut LeanObject,
    mut v_self_2555_: *mut LeanObject,
    mut v_a_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: u8 = 0;
    let mut v_r_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ =
        l_Lake_BuildTrace_checkAgainstTime(v_i_2552_, v_inst_2553_, v_info_2554_, v_self_2555_);
    lean_dec_ref(v_self_2555_);
    v_r_2558_ = lean_box((v_res_2557_) as usize);
    return v_r_2558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Hash_nil = _init_l_Lake_Hash_nil();
    l_Lake_Hash_instNilTrace = _init_l_Lake_Hash_instNilTrace();
    l_Lake_MTime_instOfNat = _init_l_Lake_MTime_instOfNat();
    lean_mark_persistent(l_Lake_MTime_instOfNat);
    l_Lake_MTime_instLT = _init_l_Lake_MTime_instLT();
    lean_mark_persistent(l_Lake_MTime_instLT);
    l_Lake_MTime_instLE = _init_l_Lake_MTime_instLE();
    lean_mark_persistent(l_Lake_MTime_instLE);
    l_Lake_MTime_instNilTrace = _init_l_Lake_MTime_instNilTrace();
    lean_mark_persistent(l_Lake_MTime_instNilTrace);
    l_Lake_BuildTrace_instNilTrace = _init_l_Lake_BuildTrace_instNilTrace();
    lean_mark_persistent(l_Lake_BuildTrace_instNilTrace);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Trace(builtin);
}
