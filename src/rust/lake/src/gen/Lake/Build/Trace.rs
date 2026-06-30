// Lean compiler output
// Module: Lake.Build.Trace
// Imports: Lean.Data.Json Init.Data.Nat.Fold Init.Data.Nat.Fold Lake.Util.String Init.Data.String.Search Init.Data.String.Extra Init.Data.Option.Coe
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_byte_array_hash,
    lean_int_dec_le, lean_io_metadata, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_nat_to_int, lean_string_append, lean_string_get_byte_fast, lean_string_hash,
    lean_string_length, lean_string_utf8_byte_size, lean_uint8_dec_le, lean_uint8_sub,
    lean_uint8_to_uint64, lean_uint64_add, lean_uint64_dec_eq, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_to_nat, lean_usize_of_nat,
};
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
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
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
pub static l_Lake_instCheckExistsFilePath___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_System_FilePath_pathExists___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCheckExistsFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCheckExistsFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCheckExistsFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCheckExistsFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_mixTraceArray___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_mixTraceArray___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_mixTraceArray___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_mixTraceArray___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_mixTraceArray___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mixTraceArray___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instComputeTraceListOfMonad___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprHash_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprHash_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprHash_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprHash_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprHash_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprHash_repr___redArg___closed__8_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprHash_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprHash_repr___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprHash_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprHash_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprHash_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprHash_repr___redArg___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash_repr___redArg___closed__12_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprHash_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprHash___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprHash_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprHash___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instReprHash: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprHash___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Hash_instHashable___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Hash_instHashable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Hash_instHashable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_instHashable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_nil: u64 = 0;
pub static mut l_Lake_Hash_instNilTrace: u64 = 0;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__3_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_ofJsonNumber_x3f___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_ofJsonNumber_x3f___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Hash_ofJsonNumber_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Hash_instMixTrace___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Hash_mix___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Hash_instMixTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instMixTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_instMixTrace: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instMixTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_instToString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Hash_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Hash_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Hash_ofBool___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Hash_ofBool___closed__0: u64 = 0;
static mut l_Lake_Hash_ofBool___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Hash_ofBool___closed__1: u64 = 0;
pub static l_Lake_Hash_instToJson___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Hash_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Hash_instToJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToJson___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_instToJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instToJson___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__0_value: leanh::LeanStringObject<42> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101,
            99, 116, 101, 100, 32, 104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 115,
            116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__2_value: leanh::LeanStringObject<55> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 55,
        m_capacity: 55,
        m_length: 54,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101,
            99, 116, 101, 100, 32, 104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 115,
            116, 114, 105, 110, 103, 32, 111, 102, 32, 108, 101, 110, 103, 116, 104, 32, 49, 54, 0,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__4_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Hash_fromJson_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__5_value: leanh::LeanStringObject<40> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 104, 97, 115, 104, 58, 32, 101, 120, 112, 101,
            99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32, 110, 117, 109,
            98, 101, 114, 0,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_fromJson_x3f___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Hash_fromJson_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_fromJson_x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Hash_instFromJson___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Hash_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Hash_instFromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Hash_instFromJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Hash_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instComputeHashFilePathIO___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_computeBinFileHash___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instComputeHashFilePathIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashFilePathIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instComputeHashFilePathIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashFilePathIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instCoeTextFilePathFilePath___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instCoeTextFilePathFilePath___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instCoeTextFilePathFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instCoeTextFilePathFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instComputeHashTextFilePathIO___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_computeTextFileHash___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instComputeHashTextFilePathIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashTextFilePathIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instComputeHashTextFilePathIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instComputeHashTextFilePathIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instToStringTextFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeTextFilePathFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_computeArrayHash___redArg___boxed__const__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [1723 as *mut leanh::LeanObject],
};
pub static mut l_Lake_computeArrayHash___redArg___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_computeArrayHash___redArg___boxed__const__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_MTime_instOfNat___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_MTime_instOfNat___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_MTime_instOfNat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_MTime_instBEq___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MTime_instBEq___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MTime_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instBEq: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_MTime_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MTime_instRepr___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MTime_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instRepr___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instRepr___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_MTime_instOrd___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MTime_instOrd___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MTime_instOrd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instOrd___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instOrd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instOrd___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instLT: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MTime_instLE: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_MTime_instMin___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MTime_instMin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MTime_instMin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMin___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instMin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMin___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_MTime_instMax___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MTime_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MTime_instMax___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instMax: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_MTime_instNilTrace: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MTime_instMixTrace: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MTime_instMax___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instGetMTimeFilePath___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_getFileMTime___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instGetMTimeFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instGetMTimeFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instGetMTimeTextFilePath___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instGetMTimeTextFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instGetMTimeTextFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeTextFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instGetMTimeTextFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instGetMTimeTextFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__2_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprHash_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__6_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__11_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildTrace_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildTrace_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildTrace___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprBuildTrace_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBuildTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprBuildTrace: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_withoutInputs___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_BuildTrace_withoutInputs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_withoutInputs___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_BuildTrace_instCoeHash___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_instCoeHash___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_BuildTrace_instCoeHash___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instCoeHash___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildTrace_instCoeHash: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeHash___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_instCoeMTime___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_BuildTrace_instCoeMTime___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instCoeMTime___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildTrace_instCoeMTime: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instCoeMTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildTrace_instNilTrace___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_BuildTrace_instNilTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instNilTrace___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_BuildTrace_instNilTrace___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_BuildTrace_instNilTrace___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_BuildTrace_instNilTrace: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_BuildTrace_instMixTrace___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_BuildTrace_mix as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildTrace_instMixTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instMixTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildTrace_instMixTrace: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildTrace_instMixTrace___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_computeTrace___redArg(
    mut v_inst_1282_: *mut leanh::LeanObject,
    mut v_inst_1283_: *mut leanh::LeanObject,
    mut v_a_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = leanh::lean_apply_1(v_inst_1282_, v_a_1284_);
    v___x_1286_ = leanh::lean_apply_2(v_inst_1283_, leanh::lean_box(0), v___x_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lake_computeTrace(
    mut v_00_u03b1_1287_: *mut leanh::LeanObject,
    mut v_m_1288_: *mut leanh::LeanObject,
    mut v_00_u03c4_1289_: *mut leanh::LeanObject,
    mut v_n_1290_: *mut leanh::LeanObject,
    mut v_inst_1291_: *mut leanh::LeanObject,
    mut v_inst_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = leanh::lean_apply_1(v_inst_1291_, v_a_1293_);
    v___x_1295_ = leanh::lean_apply_2(v_inst_1292_, leanh::lean_box(0), v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___redArg(
    mut v_inst_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_1296_);
    return v_inst_1296_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___redArg___boxed(
    mut v_inst_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lake_inhabitedOfNilTrace___redArg(v_inst_1297_);
    leanh::lean_dec(v_inst_1297_);
    return v_res_1298_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace(
    mut v_00_u03b1_1299_: *mut leanh::LeanObject,
    mut v_inst_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_1300_);
    return v_inst_1300_;
}
pub unsafe fn l_Lake_inhabitedOfNilTrace___boxed(
    mut v_00_u03b1_1301_: *mut leanh::LeanObject,
    mut v_inst_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Lake_inhabitedOfNilTrace(v_00_u03b1_1301_, v_inst_1302_);
    leanh::lean_dec(v_inst_1302_);
    return v_res_1303_;
}
pub unsafe fn l_Lake_mixTraceList___redArg(
    mut v_inst_1304_: *mut leanh::LeanObject,
    mut v_inst_1305_: *mut leanh::LeanObject,
    mut v_traces_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1307_ = l_List_foldl___redArg(v_inst_1304_, v_inst_1305_, v_traces_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Lake_mixTraceList(
    mut v_00_u03c4_1308_: *mut leanh::LeanObject,
    mut v_inst_1309_: *mut leanh::LeanObject,
    mut v_inst_1310_: *mut leanh::LeanObject,
    mut v_traces_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_List_foldl___redArg(v_inst_1309_, v_inst_1310_, v_traces_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Lake_mixTraceArray___redArg___lam__0(
    mut v_inst_1313_: *mut leanh::LeanObject,
    mut v_x1_1314_: *mut leanh::LeanObject,
    mut v_x2_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1316_ = leanh::lean_apply_2(v_inst_1313_, v_x1_1314_, v_x2_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Lake_mixTraceArray___redArg(
    mut v_inst_1336_: *mut leanh::LeanObject,
    mut v_inst_1337_: *mut leanh::LeanObject,
    mut v_traces_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    v___x_1339_ = leanh::lean_unsigned_to_nat(0);
    v___x_1340_ = lean_array_get_size(v_traces_1338_);
    v___x_1341_ = l_Lake_mixTraceArray___redArg___closed__9;
    v___x_1342_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
    if v___x_1342_ == 0 {
        leanh::lean_dec_ref(v_traces_1338_);
        leanh::lean_dec(v_inst_1336_);
        return v_inst_1337_;
    } else {
        let mut v___f_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: u8 = 0;
        v___f_1343_ = leanh::lean_alloc_closure(
            l_Lake_mixTraceArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1343_, 0, v_inst_1336_);
        v___x_1344_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
        if v___x_1344_ == 0 {
            if v___x_1342_ == 0 {
                leanh::lean_dec_ref(v___f_1343_);
                leanh::lean_dec_ref(v_traces_1338_);
                return v_inst_1337_;
            } else {
                let mut v___x_1345_: usize = 0;
                let mut v___x_1346_: usize = 0;
                let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1345_ = 0usize;
                v___x_1346_ = lean_usize_of_nat(v___x_1340_);
                v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1348_ = 0usize;
            v___x_1349_ = lean_usize_of_nat(v___x_1340_);
            v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03c4_1351_: *mut leanh::LeanObject,
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_inst_1353_: *mut leanh::LeanObject,
    mut v_traces_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lake_mixTraceArray___redArg(v_inst_1352_, v_inst_1353_, v_traces_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Lake_computeListTrace___redArg___lam__0(
    mut v_inst_1356_: *mut leanh::LeanObject,
    mut v_ts_1357_: *mut leanh::LeanObject,
    mut v_toPure_1358_: *mut leanh::LeanObject,
    mut v_____do__lift_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = leanh::lean_apply_2(v_inst_1356_, v_ts_1357_, v_____do__lift_1359_);
    v___x_1361_ =
        leanh::lean_apply_2(v_toPure_1358_, leanh::lean_box(0), v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn l_Lake_computeListTrace___redArg___lam__1(
    mut v_inst_1362_: *mut leanh::LeanObject,
    mut v_toPure_1363_: *mut leanh::LeanObject,
    mut v_inst_1364_: *mut leanh::LeanObject,
    mut v_inst_1365_: *mut leanh::LeanObject,
    mut v_toBind_1366_: *mut leanh::LeanObject,
    mut v_ts_1367_: *mut leanh::LeanObject,
    mut v_t_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1369_ = leanh::lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1369_, 0, v_inst_1362_);
    leanh::lean_closure_set(v___f_1369_, 1, v_ts_1367_);
    leanh::lean_closure_set(v___f_1369_, 2, v_toPure_1363_);
    v___x_1370_ = leanh::lean_apply_1(v_inst_1364_, v_t_1368_);
    v___x_1371_ = leanh::lean_apply_2(v_inst_1365_, leanh::lean_box(0), v___x_1370_);
    v___x_1372_ = leanh::lean_apply_4(
        v_toBind_1366_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1371_,
        v___f_1369_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lake_computeListTrace___redArg(
    mut v_inst_1373_: *mut leanh::LeanObject,
    mut v_inst_1374_: *mut leanh::LeanObject,
    mut v_inst_1375_: *mut leanh::LeanObject,
    mut v_inst_1376_: *mut leanh::LeanObject,
    mut v_inst_1377_: *mut leanh::LeanObject,
    mut v_as_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1379_ = leanh::lean_ctor_get(v_inst_1377_, 0);
    v_toBind_1380_ = leanh::lean_ctor_get(v_inst_1377_, 1);
    v_toPure_1381_ = leanh::lean_ctor_get(v_toApplicative_1379_, 1);
    leanh::lean_inc(v_toBind_1380_);
    leanh::lean_inc(v_toPure_1381_);
    v___f_1382_ = leanh::lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_1382_, 0, v_inst_1373_);
    leanh::lean_closure_set(v___f_1382_, 1, v_toPure_1381_);
    leanh::lean_closure_set(v___f_1382_, 2, v_inst_1375_);
    leanh::lean_closure_set(v___f_1382_, 3, v_inst_1376_);
    leanh::lean_closure_set(v___f_1382_, 4, v_toBind_1380_);
    v___x_1383_ = l_List_foldlM___redArg(v_inst_1377_, v___f_1382_, v_inst_1374_, v_as_1378_);
    return v___x_1383_;
}
pub unsafe fn l_Lake_computeListTrace(
    mut v_00_u03c4_1384_: *mut leanh::LeanObject,
    mut v_00_u03b1_1385_: *mut leanh::LeanObject,
    mut v_m_1386_: *mut leanh::LeanObject,
    mut v_inst_1387_: *mut leanh::LeanObject,
    mut v_inst_1388_: *mut leanh::LeanObject,
    mut v_inst_1389_: *mut leanh::LeanObject,
    mut v_n_1390_: *mut leanh::LeanObject,
    mut v_inst_1391_: *mut leanh::LeanObject,
    mut v_inst_1392_: *mut leanh::LeanObject,
    mut v_as_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1394_ = leanh::lean_ctor_get(v_inst_1392_, 0);
    v_toBind_1395_ = leanh::lean_ctor_get(v_inst_1392_, 1);
    v_toPure_1396_ = leanh::lean_ctor_get(v_toApplicative_1394_, 1);
    leanh::lean_inc(v_toBind_1395_);
    leanh::lean_inc(v_toPure_1396_);
    v___f_1397_ = leanh::lean_alloc_closure(
        l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_1397_, 0, v_inst_1387_);
    leanh::lean_closure_set(v___f_1397_, 1, v_toPure_1396_);
    leanh::lean_closure_set(v___f_1397_, 2, v_inst_1389_);
    leanh::lean_closure_set(v___f_1397_, 3, v_inst_1391_);
    leanh::lean_closure_set(v___f_1397_, 4, v_toBind_1395_);
    v___x_1398_ = l_List_foldlM___redArg(v_inst_1392_, v___f_1397_, v_inst_1388_, v_as_1393_);
    return v___x_1398_;
}
pub unsafe fn l_Lake_instComputeTraceListOfMonad___redArg(
    mut v_inst_1400_: *mut leanh::LeanObject,
    mut v_inst_1401_: *mut leanh::LeanObject,
    mut v_inst_1402_: *mut leanh::LeanObject,
    mut v_inst_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1404_ = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
    v___x_1405_ =
        leanh::lean_alloc_closure(l_Lake_computeListTrace as *mut core::ffi::c_void, 10, 9);
    leanh::lean_closure_set(v___x_1405_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1405_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1405_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1405_, 3, v_inst_1400_);
    leanh::lean_closure_set(v___x_1405_, 4, v_inst_1401_);
    leanh::lean_closure_set(v___x_1405_, 5, v_inst_1402_);
    leanh::lean_closure_set(v___x_1405_, 6, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1405_, 7, v___f_1404_);
    leanh::lean_closure_set(v___x_1405_, 8, v_inst_1403_);
    return v___x_1405_;
}
pub unsafe fn l_Lake_instComputeTraceListOfMonad(
    mut v_00_u03c4_1406_: *mut leanh::LeanObject,
    mut v_00_u03b1_1407_: *mut leanh::LeanObject,
    mut v_m_1408_: *mut leanh::LeanObject,
    mut v_inst_1409_: *mut leanh::LeanObject,
    mut v_inst_1410_: *mut leanh::LeanObject,
    mut v_inst_1411_: *mut leanh::LeanObject,
    mut v_inst_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = l_Lake_instComputeTraceListOfMonad___redArg(
        v_inst_1409_,
        v_inst_1410_,
        v_inst_1411_,
        v_inst_1412_,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lake_computeArrayTrace___redArg(
    mut v_inst_1414_: *mut leanh::LeanObject,
    mut v_inst_1415_: *mut leanh::LeanObject,
    mut v_inst_1416_: *mut leanh::LeanObject,
    mut v_inst_1417_: *mut leanh::LeanObject,
    mut v_inst_1418_: *mut leanh::LeanObject,
    mut v_as_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    v_toApplicative_1420_ = leanh::lean_ctor_get(v_inst_1418_, 0);
    v_toBind_1421_ = leanh::lean_ctor_get(v_inst_1418_, 1);
    v_toPure_1422_ = leanh::lean_ctor_get(v_toApplicative_1420_, 1);
    v___x_1423_ = leanh::lean_unsigned_to_nat(0);
    v___x_1424_ = lean_array_get_size(v_as_1419_);
    v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
    if v___x_1425_ == 0 {
        let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_1422_);
        leanh::lean_dec_ref(v_as_1419_);
        leanh::lean_dec_ref(v_inst_1418_);
        leanh::lean_dec(v_inst_1417_);
        leanh::lean_dec(v_inst_1416_);
        leanh::lean_dec(v_inst_1414_);
        v___x_1426_ =
            leanh::lean_apply_2(v_toPure_1422_, leanh::lean_box(0), v_inst_1415_);
        return v___x_1426_;
    } else {
        let mut v___f_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: u8 = 0;
        leanh::lean_inc(v_toBind_1421_);
        leanh::lean_inc(v_toPure_1422_);
        v___f_1427_ = leanh::lean_alloc_closure(
            l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
            7,
            5,
        );
        leanh::lean_closure_set(v___f_1427_, 0, v_inst_1414_);
        leanh::lean_closure_set(v___f_1427_, 1, v_toPure_1422_);
        leanh::lean_closure_set(v___f_1427_, 2, v_inst_1416_);
        leanh::lean_closure_set(v___f_1427_, 3, v_inst_1417_);
        leanh::lean_closure_set(v___f_1427_, 4, v_toBind_1421_);
        v___x_1428_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
        if v___x_1428_ == 0 {
            if v___x_1425_ == 0 {
                let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_toPure_1422_);
                leanh::lean_dec_ref(v___f_1427_);
                leanh::lean_dec_ref(v_as_1419_);
                leanh::lean_dec_ref(v_inst_1418_);
                v___x_1429_ = leanh::lean_apply_2(
                    v_toPure_1422_,
                    leanh::lean_box(0),
                    v_inst_1415_,
                );
                return v___x_1429_;
            } else {
                let mut v___x_1430_: usize = 0;
                let mut v___x_1431_: usize = 0;
                let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1430_ = 0usize;
                v___x_1431_ = lean_usize_of_nat(v___x_1424_);
                v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1433_ = 0usize;
            v___x_1434_ = lean_usize_of_nat(v___x_1424_);
            v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03c4_1436_: *mut leanh::LeanObject,
    mut v_00_u03b1_1437_: *mut leanh::LeanObject,
    mut v_m_1438_: *mut leanh::LeanObject,
    mut v_inst_1439_: *mut leanh::LeanObject,
    mut v_inst_1440_: *mut leanh::LeanObject,
    mut v_inst_1441_: *mut leanh::LeanObject,
    mut v_n_1442_: *mut leanh::LeanObject,
    mut v_inst_1443_: *mut leanh::LeanObject,
    mut v_inst_1444_: *mut leanh::LeanObject,
    mut v_as_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    v_toApplicative_1446_ = leanh::lean_ctor_get(v_inst_1444_, 0);
    v_toBind_1447_ = leanh::lean_ctor_get(v_inst_1444_, 1);
    v_toPure_1448_ = leanh::lean_ctor_get(v_toApplicative_1446_, 1);
    v___x_1449_ = leanh::lean_unsigned_to_nat(0);
    v___x_1450_ = lean_array_get_size(v_as_1445_);
    v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
    if v___x_1451_ == 0 {
        let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_1448_);
        leanh::lean_dec_ref(v_as_1445_);
        leanh::lean_dec_ref(v_inst_1444_);
        leanh::lean_dec(v_inst_1443_);
        leanh::lean_dec(v_inst_1441_);
        leanh::lean_dec(v_inst_1439_);
        v___x_1452_ =
            leanh::lean_apply_2(v_toPure_1448_, leanh::lean_box(0), v_inst_1440_);
        return v___x_1452_;
    } else {
        let mut v___f_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: u8 = 0;
        leanh::lean_inc(v_toBind_1447_);
        leanh::lean_inc(v_toPure_1448_);
        v___f_1453_ = leanh::lean_alloc_closure(
            l_Lake_computeListTrace___redArg___lam__1 as *mut core::ffi::c_void,
            7,
            5,
        );
        leanh::lean_closure_set(v___f_1453_, 0, v_inst_1439_);
        leanh::lean_closure_set(v___f_1453_, 1, v_toPure_1448_);
        leanh::lean_closure_set(v___f_1453_, 2, v_inst_1441_);
        leanh::lean_closure_set(v___f_1453_, 3, v_inst_1443_);
        leanh::lean_closure_set(v___f_1453_, 4, v_toBind_1447_);
        v___x_1454_ = lean_nat_dec_le(v___x_1450_, v___x_1450_);
        if v___x_1454_ == 0 {
            if v___x_1451_ == 0 {
                let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_toPure_1448_);
                leanh::lean_dec_ref(v___f_1453_);
                leanh::lean_dec_ref(v_as_1445_);
                leanh::lean_dec_ref(v_inst_1444_);
                v___x_1455_ = leanh::lean_apply_2(
                    v_toPure_1448_,
                    leanh::lean_box(0),
                    v_inst_1440_,
                );
                return v___x_1455_;
            } else {
                let mut v___x_1456_: usize = 0;
                let mut v___x_1457_: usize = 0;
                let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1456_ = 0usize;
                v___x_1457_ = lean_usize_of_nat(v___x_1450_);
                v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1459_ = 0usize;
            v___x_1460_ = lean_usize_of_nat(v___x_1450_);
            v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_1462_: *mut leanh::LeanObject,
    mut v_inst_1463_: *mut leanh::LeanObject,
    mut v_inst_1464_: *mut leanh::LeanObject,
    mut v_inst_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1466_ = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
    v___x_1467_ =
        leanh::lean_alloc_closure(l_Lake_computeArrayTrace as *mut core::ffi::c_void, 10, 9);
    leanh::lean_closure_set(v___x_1467_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 3, v_inst_1462_);
    leanh::lean_closure_set(v___x_1467_, 4, v_inst_1463_);
    leanh::lean_closure_set(v___x_1467_, 5, v_inst_1464_);
    leanh::lean_closure_set(v___x_1467_, 6, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 7, v___f_1466_);
    leanh::lean_closure_set(v___x_1467_, 8, v_inst_1465_);
    return v___x_1467_;
}
pub unsafe fn l_Lake_instComputeTraceArrayOfMonad(
    mut v_00_u03c4_1468_: *mut leanh::LeanObject,
    mut v_00_u03b1_1469_: *mut leanh::LeanObject,
    mut v_m_1470_: *mut leanh::LeanObject,
    mut v_inst_1471_: *mut leanh::LeanObject,
    mut v_inst_1472_: *mut leanh::LeanObject,
    mut v_inst_1473_: *mut leanh::LeanObject,
    mut v_inst_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lake_instComputeTraceArrayOfMonad___redArg(
        v_inst_1471_,
        v_inst_1472_,
        v_inst_1473_,
        v_inst_1474_,
    );
    return v___x_1475_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(
    mut v_a_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = lean_nat_to_int(v_a_1476_);
    return v___x_1477_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = leanh::lean_unsigned_to_nat(7);
    v___x_1492_ = lean_nat_to_int(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lake_instReprHash_repr___redArg___closed__0;
    v___x_1495_ = lean_string_length(v___x_1494_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lake_instReprHash_repr___redArg___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__9_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__9,
    );
    v___x_1497_ = lean_nat_to_int(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_instReprHash_repr___redArg(
    mut v_x_1502_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Lake_instReprHash_repr___redArg___closed__6;
    v___x_1504_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__7_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__7,
    );
    v___x_1505_ = lean_uint64_to_nat(v_x_1502_);
    v___x_1506_ = l_Nat_reprFast(v___x_1505_);
    v___x_1507_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    v___x_1508_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1508_, 0, v___x_1504_);
    leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
    v___x_1509_ = 0;
    v___x_1510_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
    leanh::lean_ctor_set_uint8(
        v___x_1510_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1509_,
    );
    v___x_1511_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1511_, 0, v___x_1503_);
    leanh::lean_ctor_set(v___x_1511_, 1, v___x_1510_);
    v___x_1512_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__10,
    );
    v___x_1513_ = l_Lake_instReprHash_repr___redArg___closed__11;
    v___x_1514_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    leanh::lean_ctor_set(v___x_1514_, 1, v___x_1511_);
    v___x_1515_ = l_Lake_instReprHash_repr___redArg___closed__12;
    v___x_1516_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1516_, 0, v___x_1514_);
    leanh::lean_ctor_set(v___x_1516_, 1, v___x_1515_);
    v___x_1517_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1517_, 0, v___x_1512_);
    leanh::lean_ctor_set(v___x_1517_, 1, v___x_1516_);
    v___x_1518_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
    leanh::lean_ctor_set_uint8(
        v___x_1518_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1509_,
    );
    return v___x_1518_;
}
pub unsafe fn l_Lake_instReprHash_repr___redArg___boxed(
    mut v_x_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_147__boxed_1520_: u64 = 0;
    let mut v_res_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_147__boxed_1520_ = leanh::lean_unbox_uint64(v_x_1519_);
    leanh::lean_dec_ref(v_x_1519_);
    v_res_1521_ = l_Lake_instReprHash_repr___redArg(v_x_147__boxed_1520_);
    return v_res_1521_;
}
pub unsafe fn l_Lake_instReprHash_repr(
    mut v_x_1522_: u64,
    mut v_prec_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lake_instReprHash_repr___redArg(v_x_1522_);
    return v___x_1524_;
}
pub unsafe fn l_Lake_instReprHash_repr___boxed(
    mut v_x_1525_: *mut leanh::LeanObject,
    mut v_prec_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_206__boxed_1527_: u64 = 0;
    let mut v_res_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_206__boxed_1527_ = leanh::lean_unbox_uint64(v_x_1525_);
    leanh::lean_dec_ref(v_x_1525_);
    v_res_1528_ = l_Lake_instReprHash_repr(v_x_206__boxed_1527_, v_prec_1526_);
    leanh::lean_dec(v_prec_1526_);
    return v_res_1528_;
}
pub unsafe fn l_Lake_instDecidableEqHash_decEq(mut v_x_1531_: u64, mut v_x_1532_: u64) -> u8 {
    let mut v___x_1533_: u8 = 0;
    v___x_1533_ = lean_uint64_dec_eq(v_x_1531_, v_x_1532_);
    return v___x_1533_;
}
pub unsafe fn l_Lake_instDecidableEqHash_decEq___boxed(
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_x_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_25__boxed_1536_: u64 = 0;
    let mut v_x_26__boxed_1537_: u64 = 0;
    let mut v_res_1538_: u8 = 0;
    let mut v_r_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_1536_ = leanh::lean_unbox_uint64(v_x_1534_);
    leanh::lean_dec_ref(v_x_1534_);
    v_x_26__boxed_1537_ = leanh::lean_unbox_uint64(v_x_1535_);
    leanh::lean_dec_ref(v_x_1535_);
    v_res_1538_ = l_Lake_instDecidableEqHash_decEq(v_x_25__boxed_1536_, v_x_26__boxed_1537_);
    v_r_1539_ = leanh::lean_box((v_res_1538_) as usize);
    return v_r_1539_;
}
pub unsafe fn l_Lake_instDecidableEqHash(mut v_x_1540_: u64, mut v_x_1541_: u64) -> u8 {
    let mut v___x_1542_: u8 = 0;
    v___x_1542_ = lean_uint64_dec_eq(v_x_1540_, v_x_1541_);
    return v___x_1542_;
}
pub unsafe fn l_Lake_instDecidableEqHash___boxed(
    mut v_x_1543_: *mut leanh::LeanObject,
    mut v_x_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6__boxed_1545_: u64 = 0;
    let mut v_x_7__boxed_1546_: u64 = 0;
    let mut v_res_1547_: u8 = 0;
    let mut v_r_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6__boxed_1545_ = leanh::lean_unbox_uint64(v_x_1543_);
    leanh::lean_dec_ref(v_x_1543_);
    v_x_7__boxed_1546_ = leanh::lean_unbox_uint64(v_x_1544_);
    leanh::lean_dec_ref(v_x_1544_);
    v_res_1547_ = l_Lake_instDecidableEqHash(v_x_6__boxed_1545_, v_x_7__boxed_1546_);
    v_r_1548_ = leanh::lean_box((v_res_1547_) as usize);
    return v_r_1548_;
}
pub unsafe fn l_Lake_Hash_instHashable___lam__0(mut v_self_1549_: u64) -> u64 {
    return v_self_1549_;
}
pub unsafe fn l_Lake_Hash_instHashable___lam__0___boxed(
    mut v_self_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_self_boxed_1551_: u64 = 0;
    let mut v_res_1552_: u64 = 0;
    let mut v_r_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_self_boxed_1551_ = leanh::lean_unbox_uint64(v_self_1550_);
    leanh::lean_dec_ref(v_self_1550_);
    v_res_1552_ = l_Lake_Hash_instHashable___lam__0(v_self_boxed_1551_);
    v_r_1553_ = leanh::lean_box_uint64(v_res_1552_);
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
pub unsafe fn l_Lake_Hash_ofNat(mut v_n_1558_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1559_: u64 = 0;
    v___x_1559_ = lean_uint64_of_nat(v_n_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_Hash_ofNat___boxed(
    mut v_n_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: u64 = 0;
    let mut v_r_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lake_Hash_ofNat(v_n_1560_);
    leanh::lean_dec(v_n_1560_);
    v_r_1562_ = leanh::lean_box_uint64(v_res_1561_);
    return v_r_1562_;
}
pub unsafe fn _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_1566_;
}
pub unsafe fn _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = leanh::lean_unsigned_to_nat(0);
    v___x_1571_ = lean_nat_to_int(v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lake_Hash_ofJsonNumber_x3f(
    mut v_n_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mantissa_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1576_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u64 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1573_ = leanh::lean_ctor_get(v_n_1572_, 0);
                v_exponent_1574_ = leanh::lean_ctor_get(v_n_1572_, 1);
                v___x_1585_ = leanh::lean_unsigned_to_nat(0);
                v___x_1586_ = lean_nat_dec_eq(v_exponent_1574_, v___x_1585_);
                if v___x_1586_ == 0 {
                    v___y_1576_ = v___x_1586_;
                    state = 1;
                    continue;
                } else {
                    v___x_1587_ = leanh::lean_obj_once(
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
                    v___x_1579_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__2),
                        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__2_once),
                        _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2,
                    );
                    v___x_1580_ = lean_nat_dec_lt(v___x_1578_, v___x_1579_);
                    if v___x_1580_ == 0 {
                        leanh::lean_dec(v___x_1578_);
                        v___x_1581_ = l_Lake_Hash_ofJsonNumber_x3f___closed__4;
                        return v___x_1581_;
                    } else {
                        v___x_1582_ = lean_uint64_of_nat(v___x_1578_);
                        leanh::lean_dec(v___x_1578_);
                        v___x_1583_ = leanh::lean_box_uint64(v___x_1582_);
                        v___x_1584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1584_, 0, v___x_1583_);
                        return v___x_1584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Hash_ofJsonNumber_x3f___boxed(
    mut v_n_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1589_);
    leanh::lean_dec_ref(v_n_1589_);
    return v_res_1590_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
    mut v_s_1591_: *mut leanh::LeanObject,
    mut v_n_1592_: *mut leanh::LeanObject,
    mut v_j_1593_: *mut leanh::LeanObject,
    mut v_a_1594_: u64,
) -> u64 {
    let mut v_zero_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1596_: u8 = 0;
    let mut v_one_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_zero_1595_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1596_ = lean_nat_dec_eq(v_j_1593_, v_zero_1595_);
                if v_isZero_1596_ == 1 {
                    leanh::lean_dec(v_j_1593_);
                    return v_a_1594_;
                } else {
                    v_one_1597_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1598_ = lean_nat_sub(v_j_1593_, v_one_1597_);
                    v___x_1599_ = lean_nat_sub(v_n_1592_, v_j_1593_);
                    leanh::lean_dec(v_j_1593_);
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
    mut v_s_1626_: *mut leanh::LeanObject,
    mut v_n_1627_: *mut leanh::LeanObject,
    mut v_j_1628_: *mut leanh::LeanObject,
    mut v_a_1629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_252__boxed_1630_: u64 = 0;
    let mut v_res_1631_: u64 = 0;
    let mut v_r_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_252__boxed_1630_ = leanh::lean_unbox_uint64(v_a_1629_);
    leanh::lean_dec_ref(v_a_1629_);
    v_res_1631_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(
            v_s_1626_,
            v_n_1627_,
            v_j_1628_,
            v_a_252__boxed_1630_,
        );
    leanh::lean_dec(v_n_1627_);
    leanh::lean_dec_ref(v_s_1626_);
    v_r_1632_ = leanh::lean_box_uint64(v_res_1631_);
    return v_r_1632_;
}
pub unsafe fn l_Lake_Hash_ofHex(mut v_s_1633_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn l_Lake_Hash_ofHex___boxed(
    mut v_s_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: u64 = 0;
    let mut v_r_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lake_Hash_ofHex(v_s_1637_);
    leanh::lean_dec_ref(v_s_1637_);
    v_r_1639_ = leanh::lean_box_uint64(v_res_1638_);
    return v_r_1639_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(
    mut v_s_1640_: *mut leanh::LeanObject,
    mut v_n_1641_: *mut leanh::LeanObject,
    mut v_j_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
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
    mut v_s_1646_: *mut leanh::LeanObject,
    mut v_n_1647_: *mut leanh::LeanObject,
    mut v_j_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_316__boxed_1651_: u64 = 0;
    let mut v_res_1652_: u64 = 0;
    let mut v_r_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_316__boxed_1651_ = leanh::lean_unbox_uint64(v_a_1650_);
    leanh::lean_dec_ref(v_a_1650_);
    v_res_1652_ =
        l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(
            v_s_1646_,
            v_n_1647_,
            v_j_1648_,
            v_a_1649_,
            v_a_316__boxed_1651_,
        );
    leanh::lean_dec(v_n_1647_);
    leanh::lean_dec_ref(v_s_1646_);
    v_r_1653_ = leanh::lean_box_uint64(v_res_1652_);
    return v_r_1653_;
}
pub unsafe fn l_Lake_Hash_ofHex_x3f(
    mut v_s_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1656_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u64 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_string_utf8_byte_size(v_s_1654_);
                v___x_1662_ = leanh::lean_unsigned_to_nat(16);
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
                    v___x_1657_ = leanh::lean_box(0);
                    return v___x_1657_;
                } else {
                    v___x_1658_ = l_Lake_Hash_ofHex(v_s_1654_);
                    v___x_1659_ = leanh::lean_box_uint64(v___x_1658_);
                    v___x_1660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1660_, 0, v___x_1659_);
                    return v___x_1660_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Hash_ofHex_x3f___boxed(
    mut v_s_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lake_Hash_ofHex_x3f(v_s_1665_);
    leanh::lean_dec_ref(v_s_1665_);
    return v_res_1666_;
}
pub unsafe fn l_Lake_Hash_hex(mut v_self_1667_: u64) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lake_lowerHexUInt64(v_self_1667_);
    return v___x_1668_;
}
pub unsafe fn l_Lake_Hash_hex___boxed(
    mut v_self_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_self_boxed_1670_: u64 = 0;
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_self_boxed_1670_ = leanh::lean_unbox_uint64(v_self_1669_);
    leanh::lean_dec_ref(v_self_1669_);
    v_res_1671_ = l_Lake_Hash_hex(v_self_boxed_1670_);
    return v_res_1671_;
}
pub unsafe fn l_Lake_Hash_ofDecimal_x3f(
    mut v_s_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: u64 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1673_ = leanh::lean_unsigned_to_nat(0);
                v___x_1674_ = lean_string_utf8_byte_size(v_s_1672_);
                v___x_1675_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1675_, 0, v_s_1672_);
                leanh::lean_ctor_set(v___x_1675_, 1, v___x_1673_);
                leanh::lean_ctor_set(v___x_1675_, 2, v___x_1674_);
                v___x_1676_ = l_String_Slice_toNat_x3f(v___x_1675_);
                leanh::lean_dec_ref_known(v___x_1675_, 3);
                if leanh::lean_obj_tag(v___x_1676_) == 0 {
                    v___x_1677_ = leanh::lean_box(0);
                    return v___x_1677_;
                } else {
                    v_val_1678_ = leanh::lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1680_ = v___x_1676_;
                        v_isShared_1681_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1678_);
                        leanh::lean_dec(v___x_1676_);
                        v___x_1680_ = leanh::lean_box(0);
                        v_isShared_1681_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1682_ = lean_uint64_of_nat(v_val_1678_);
                leanh::lean_dec(v_val_1678_);
                v___x_1683_ = leanh::lean_box_uint64(v___x_1682_);
                if v_isShared_1681_ == 0 {
                    leanh::lean_ctor_set(v___x_1680_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
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
pub unsafe fn l_Lake_Hash_ofString_x3f(
    mut v_s_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lake_Hash_ofHex_x3f(v_s_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lake_Hash_ofString_x3f___boxed(
    mut v_s_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Lake_Hash_ofString_x3f(v_s_1690_);
    leanh::lean_dec_ref(v_s_1690_);
    return v_res_1691_;
}
pub unsafe fn l_Lake_Hash_load_x3f(
    mut v_hashFile_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_IO_FS_readFile(v_hashFile_1692_);
    if leanh::lean_obj_tag(v___x_1694_) == 0 {
        let mut v_a_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1695_ = leanh::lean_ctor_get(v___x_1694_, 0);
        leanh::lean_inc(v_a_1695_);
        leanh::lean_dec_ref_known(v___x_1694_, 1);
        v___x_1696_ = l_Lake_Hash_ofHex_x3f(v_a_1695_);
        leanh::lean_dec(v_a_1695_);
        return v___x_1696_;
    } else {
        let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1694_, 1);
        v___x_1697_ = leanh::lean_box(0);
        return v___x_1697_;
    }
}
pub unsafe fn l_Lake_Hash_load_x3f___boxed(
    mut v_hashFile_1698_: *mut leanh::LeanObject,
    mut v_a_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_Lake_Hash_load_x3f(v_hashFile_1698_);
    leanh::lean_dec_ref(v_hashFile_1698_);
    return v_res_1700_;
}
pub unsafe fn l_Lake_Hash_mix(mut v_h1_1701_: u64, mut v_h2_1702_: u64) -> u64 {
    let mut v___x_1703_: u64 = 0;
    v___x_1703_ = lean_uint64_mix_hash(v_h1_1701_, v_h2_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Lake_Hash_mix___boxed(
    mut v_h1_1704_: *mut leanh::LeanObject,
    mut v_h2_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_h1_boxed_1706_: u64 = 0;
    let mut v_h2_boxed_1707_: u64 = 0;
    let mut v_res_1708_: u64 = 0;
    let mut v_r_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_h1_boxed_1706_ = leanh::lean_unbox_uint64(v_h1_1704_);
    leanh::lean_dec_ref(v_h1_1704_);
    v_h2_boxed_1707_ = leanh::lean_unbox_uint64(v_h2_1705_);
    leanh::lean_dec_ref(v_h2_1705_);
    v_res_1708_ = l_Lake_Hash_mix(v_h1_boxed_1706_, v_h2_boxed_1707_);
    v_r_1709_ = leanh::lean_box_uint64(v_res_1708_);
    return v_r_1709_;
}
pub unsafe fn l_Lake_Hash_toString(mut v_self_1712_: u64) -> *mut leanh::LeanObject {
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lake_lowerHexUInt64(v_self_1712_);
    return v___x_1713_;
}
pub unsafe fn l_Lake_Hash_toString___boxed(
    mut v_self_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_self_boxed_1715_: u64 = 0;
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_self_boxed_1715_ = leanh::lean_unbox_uint64(v_self_1714_);
    leanh::lean_dec_ref(v_self_1714_);
    v_res_1716_ = l_Lake_Hash_toString(v_self_boxed_1715_);
    return v_res_1716_;
}
pub unsafe fn l_Lake_Hash_ofHashable___redArg(
    mut v_inst_1719_: *mut leanh::LeanObject,
    mut v_a_1720_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1721_: u64 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: u64 = 0;
    let mut v___x_1724_: u64 = 0;
    v___x_1721_ = 1723u64;
    v___x_1722_ = leanh::lean_apply_1(v_inst_1719_, v_a_1720_);
    v___x_1723_ = leanh::lean_unbox_uint64(v___x_1722_);
    leanh::lean_dec_ref(v___x_1722_);
    v___x_1724_ = lean_uint64_mix_hash(v___x_1721_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lake_Hash_ofHashable___redArg___boxed(
    mut v_inst_1725_: *mut leanh::LeanObject,
    mut v_a_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1727_: u64 = 0;
    let mut v_r_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1727_ = l_Lake_Hash_ofHashable___redArg(v_inst_1725_, v_a_1726_);
    v_r_1728_ = leanh::lean_box_uint64(v_res_1727_);
    return v_r_1728_;
}
pub unsafe fn l_Lake_Hash_ofHashable(
    mut v_00_u03b1_1729_: *mut leanh::LeanObject,
    mut v_inst_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1732_: u64 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u64 = 0;
    let mut v___x_1735_: u64 = 0;
    v___x_1732_ = 1723u64;
    v___x_1733_ = leanh::lean_apply_1(v_inst_1730_, v_a_1731_);
    v___x_1734_ = leanh::lean_unbox_uint64(v___x_1733_);
    leanh::lean_dec_ref(v___x_1733_);
    v___x_1735_ = lean_uint64_mix_hash(v___x_1732_, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Lake_Hash_ofHashable___boxed(
    mut v_00_u03b1_1736_: *mut leanh::LeanObject,
    mut v_inst_1737_: *mut leanh::LeanObject,
    mut v_a_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1739_: u64 = 0;
    let mut v_r_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lake_Hash_ofHashable(v_00_u03b1_1736_, v_inst_1737_, v_a_1738_);
    v_r_1740_ = leanh::lean_box_uint64(v_res_1739_);
    return v_r_1740_;
}
pub unsafe fn l_Lake_Hash_ofString(mut v_str_1741_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1742_: u64 = 0;
    let mut v___x_1743_: u64 = 0;
    let mut v___x_1744_: u64 = 0;
    v___x_1742_ = 1723u64;
    v___x_1743_ = lean_string_hash(v_str_1741_);
    v___x_1744_ = lean_uint64_mix_hash(v___x_1742_, v___x_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Lake_Hash_ofString___boxed(
    mut v_str_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: u64 = 0;
    let mut v_r_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lake_Hash_ofString(v_str_1745_);
    leanh::lean_dec_ref(v_str_1745_);
    v_r_1747_ = leanh::lean_box_uint64(v_res_1746_);
    return v_r_1747_;
}
pub unsafe fn l_Lake_Hash_ofText(mut v_str_1748_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: u64 = 0;
    v___x_1749_ = l_String_crlfToLf(v_str_1748_);
    v___x_1750_ = 1723u64;
    v___x_1751_ = lean_string_hash(v___x_1749_);
    leanh::lean_dec_ref(v___x_1749_);
    v___x_1752_ = lean_uint64_mix_hash(v___x_1750_, v___x_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Lake_Hash_ofText___boxed(
    mut v_str_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1754_: u64 = 0;
    let mut v_r_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Lake_Hash_ofText(v_str_1753_);
    leanh::lean_dec_ref(v_str_1753_);
    v_r_1755_ = leanh::lean_box_uint64(v_res_1754_);
    return v_r_1755_;
}
pub unsafe fn l_Lake_Hash_ofByteArray(mut v_bytes_1756_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1757_: u64 = 0;
    let mut v___x_1758_: u64 = 0;
    let mut v___x_1759_: u64 = 0;
    v___x_1757_ = 1723u64;
    v___x_1758_ = lean_byte_array_hash(v_bytes_1756_);
    v___x_1759_ = lean_uint64_mix_hash(v___x_1757_, v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Lake_Hash_ofByteArray___boxed(
    mut v_bytes_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1761_: u64 = 0;
    let mut v_r_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1761_ = l_Lake_Hash_ofByteArray(v_bytes_1760_);
    leanh::lean_dec_ref(v_bytes_1760_);
    v_r_1762_ = leanh::lean_box_uint64(v_res_1761_);
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
        v___x_1770_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__0),
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__0_once),
            _init_l_Lake_Hash_ofBool___closed__0,
        );
        return v___x_1770_;
    } else {
        let mut v___x_1771_: u64 = 0;
        v___x_1771_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__1),
            core::ptr::addr_of_mut!(l_Lake_Hash_ofBool___closed__1_once),
            _init_l_Lake_Hash_ofBool___closed__1,
        );
        return v___x_1771_;
    }
}
pub unsafe fn l_Lake_Hash_ofBool___boxed(
    mut v_b_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1773_: u8 = 0;
    let mut v_res_1774_: u64 = 0;
    let mut v_r_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1773_ = (leanh::lean_unbox(v_b_1772_) as u8);
    v_res_1774_ = l_Lake_Hash_ofBool(v_b_boxed_1773_);
    v_r_1775_ = leanh::lean_box_uint64(v_res_1774_);
    return v_r_1775_;
}
pub unsafe fn l_Lake_Hash_toJson(mut v_self_1776_: u64) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lake_lowerHexUInt64(v_self_1776_);
    v___x_1778_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lake_Hash_toJson___boxed(
    mut v_self_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_self_boxed_1780_: u64 = 0;
    let mut v_res_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_self_boxed_1780_ = leanh::lean_unbox_uint64(v_self_1779_);
    leanh::lean_dec_ref(v_self_1779_);
    v_res_1781_ = l_Lake_Hash_toJson(v_self_boxed_1780_);
    return v_res_1781_;
}
pub unsafe fn l_Lake_Hash_fromJson_x3f(
    mut v_json_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1798_: u8 = 0;
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u64 = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_n_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_json_1794_) {
                3 => {
                    v_s_1795_ = leanh::lean_ctor_get(v_json_1794_, 0);
                    v_isSharedCheck_1810_ = (!leanh::lean_is_exclusive(v_json_1794_)) as u8;
                    if v_isSharedCheck_1810_ == 0 {
                        v___x_1797_ = v_json_1794_;
                        v_isShared_1798_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1795_);
                        leanh::lean_dec(v_json_1794_);
                        v___x_1797_ = leanh::lean_box(0);
                        v_isShared_1798_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_n_1811_ = leanh::lean_ctor_get(v_json_1794_, 0);
                    leanh::lean_inc_ref(v_n_1811_);
                    leanh::lean_dec_ref_known(v_json_1794_, 1);
                    v___x_1812_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1811_);
                    leanh::lean_dec_ref(v_n_1811_);
                    if leanh::lean_obj_tag(v___x_1812_) == 0 {
                        v_a_1813_ = leanh::lean_ctor_get(v___x_1812_, 0);
                        v_isSharedCheck_1822_ =
                            (!leanh::lean_is_exclusive(v___x_1812_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v___x_1815_ = v___x_1812_;
                            v_isShared_1816_ = v_isSharedCheck_1822_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1813_);
                            leanh::lean_dec(v___x_1812_);
                            v___x_1815_ = leanh::lean_box(0);
                            v_isShared_1816_ = v_isSharedCheck_1822_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_1812_;
                    }
                }
                _ => {
                    leanh::lean_dec(v_json_1794_);
                    v___x_1823_ = l_Lake_Hash_fromJson_x3f___closed__6;
                    return v___x_1823_;
                }
            },
            1 => {
                v___x_1799_ = l_Lake_isHex(v_s_1795_);
                if v___x_1799_ == 0 {
                    leanh::lean_del_object(v___x_1797_);
                    leanh::lean_dec_ref(v_s_1795_);
                    v___x_1800_ = l_Lake_Hash_fromJson_x3f___closed__1;
                    return v___x_1800_;
                } else {
                    v___x_1801_ = lean_string_utf8_byte_size(v_s_1795_);
                    v___x_1802_ = leanh::lean_unsigned_to_nat(16);
                    v___x_1803_ = lean_nat_dec_eq(v___x_1801_, v___x_1802_);
                    if v___x_1803_ == 0 {
                        leanh::lean_del_object(v___x_1797_);
                        leanh::lean_dec_ref(v_s_1795_);
                        v___x_1804_ = l_Lake_Hash_fromJson_x3f___closed__3;
                        return v___x_1804_;
                    } else {
                        v___x_1805_ = l_Lake_Hash_ofHex(v_s_1795_);
                        leanh::lean_dec_ref(v_s_1795_);
                        v___x_1806_ = leanh::lean_box_uint64(v___x_1805_);
                        if v_isShared_1798_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1797_, 1);
                            leanh::lean_ctor_set(v___x_1797_, 0, v___x_1806_);
                            v___x_1808_ = v___x_1797_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1809_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
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
                leanh::lean_dec(v_a_1813_);
                if v_isShared_1816_ == 0 {
                    leanh::lean_ctor_set(v___x_1815_, 0, v___x_1818_);
                    v___x_1820_ = v___x_1815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
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
    mut v_inst_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_1826_);
    return v_inst_1826_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(
    mut v_inst_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_1827_);
    leanh::lean_dec(v_inst_1827_);
    return v_res_1828_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash(
    mut v_00_u03b1_1829_: *mut leanh::LeanObject,
    mut v_m_1830_: *mut leanh::LeanObject,
    mut v_inst_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_1831_);
    return v_inst_1831_;
}
pub unsafe fn l_Lake_instComputeTraceHashOfComputeHash___boxed(
    mut v_00_u03b1_1832_: *mut leanh::LeanObject,
    mut v_m_1833_: *mut leanh::LeanObject,
    mut v_inst_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ =
        l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_1832_, v_m_1833_, v_inst_1834_);
    leanh::lean_dec(v_inst_1834_);
    return v_res_1835_;
}
pub unsafe fn l_Lake_pureHash___redArg(
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u64 = 0;
    v___x_1838_ = leanh::lean_apply_1(v_inst_1836_, v_a_1837_);
    v___x_1839_ = leanh::lean_unbox_uint64(v___x_1838_);
    leanh::lean_dec_ref(v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l_Lake_pureHash___redArg___boxed(
    mut v_inst_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1842_: u64 = 0;
    let mut v_r_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lake_pureHash___redArg(v_inst_1840_, v_a_1841_);
    v_r_1843_ = leanh::lean_box_uint64(v_res_1842_);
    return v_r_1843_;
}
pub unsafe fn l_Lake_pureHash(
    mut v_00_u03b1_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u64 = 0;
    v___x_1847_ = leanh::lean_apply_1(v_inst_1845_, v_a_1846_);
    v___x_1848_ = leanh::lean_unbox_uint64(v___x_1847_);
    leanh::lean_dec_ref(v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Lake_pureHash___boxed(
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_inst_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1852_: u64 = 0;
    let mut v_r_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Lake_pureHash(v_00_u03b1_1849_, v_inst_1850_, v_a_1851_);
    v_r_1853_ = leanh::lean_box_uint64(v_res_1852_);
    return v_r_1853_;
}
pub unsafe fn l_Lake_computeHash___redArg(
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = leanh::lean_apply_1(v_inst_1854_, v_a_1856_);
    v___x_1858_ = leanh::lean_apply_2(v_inst_1855_, leanh::lean_box(0), v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn l_Lake_computeHash(
    mut v_00_u03b1_1859_: *mut leanh::LeanObject,
    mut v_m_1860_: *mut leanh::LeanObject,
    mut v_n_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_inst_1863_: *mut leanh::LeanObject,
    mut v_a_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = leanh::lean_apply_1(v_inst_1862_, v_a_1864_);
    v___x_1866_ = leanh::lean_apply_2(v_inst_1863_, leanh::lean_box(0), v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Lake_instComputeHashIdOfHashable___redArg(
    mut v_inst_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = leanh::lean_alloc_closure(
        l_Lake_Hash_ofHashable___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1868_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1868_, 1, v_inst_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Lake_instComputeHashIdOfHashable(
    mut v_00_u03b1_1869_: *mut leanh::LeanObject,
    mut v_inst_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = leanh::lean_alloc_closure(
        l_Lake_Hash_ofHashable___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1871_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1871_, 1, v_inst_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lake_computeBinFileHash(
    mut v_file_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1879_: u64 = 0;
    let mut v___x_1880_: u64 = 0;
    let mut v___x_1881_: u64 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_a_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1874_ = l_IO_FS_readBinFile(v_file_1872_);
                if leanh::lean_obj_tag(v___x_1874_) == 0 {
                    v_a_1875_ = leanh::lean_ctor_get(v___x_1874_, 0);
                    v_isSharedCheck_1886_ = (!leanh::lean_is_exclusive(v___x_1874_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v___x_1877_ = v___x_1874_;
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1875_);
                        leanh::lean_dec(v___x_1874_);
                        v___x_1877_ = leanh::lean_box(0);
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1887_ = leanh::lean_ctor_get(v___x_1874_, 0);
                    v_isSharedCheck_1894_ = (!leanh::lean_is_exclusive(v___x_1874_)) as u8;
                    if v_isSharedCheck_1894_ == 0 {
                        v___x_1889_ = v___x_1874_;
                        v_isShared_1890_ = v_isSharedCheck_1894_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1887_);
                        leanh::lean_dec(v___x_1874_);
                        v___x_1889_ = leanh::lean_box(0);
                        v_isShared_1890_ = v_isSharedCheck_1894_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1879_ = 1723u64;
                v___x_1880_ = lean_byte_array_hash(v_a_1875_);
                leanh::lean_dec(v_a_1875_);
                v___x_1881_ = lean_uint64_mix_hash(v___x_1879_, v___x_1880_);
                v___x_1882_ = leanh::lean_box_uint64(v___x_1881_);
                if v_isShared_1878_ == 0 {
                    leanh::lean_ctor_set(v___x_1877_, 0, v___x_1882_);
                    v___x_1884_ = v___x_1877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
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
                    v_reuseFailAlloc_1893_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
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
    mut v_file_1895_: *mut leanh::LeanObject,
    mut v_a_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Lake_computeBinFileHash(v_file_1895_);
    leanh::lean_dec_ref(v_file_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Lake_computeTextFileHash(
    mut v_file_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u64 = 0;
    let mut v___x_1909_: u64 = 0;
    let mut v___x_1910_: u64 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_a_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1902_ = l_IO_FS_readFile(v_file_1900_);
                if leanh::lean_obj_tag(v___x_1902_) == 0 {
                    v_a_1903_ = leanh::lean_ctor_get(v___x_1902_, 0);
                    v_isSharedCheck_1915_ = (!leanh::lean_is_exclusive(v___x_1902_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1905_ = v___x_1902_;
                        v_isShared_1906_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1903_);
                        leanh::lean_dec(v___x_1902_);
                        v___x_1905_ = leanh::lean_box(0);
                        v_isShared_1906_ = v_isSharedCheck_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1916_ = leanh::lean_ctor_get(v___x_1902_, 0);
                    v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v___x_1902_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1902_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1916_);
                        leanh::lean_dec(v___x_1902_);
                        v___x_1918_ = leanh::lean_box(0);
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1907_ = l_String_crlfToLf(v_a_1903_);
                leanh::lean_dec(v_a_1903_);
                v___x_1908_ = 1723u64;
                v___x_1909_ = lean_string_hash(v___x_1907_);
                leanh::lean_dec_ref(v___x_1907_);
                v___x_1910_ = lean_uint64_mix_hash(v___x_1908_, v___x_1909_);
                v___x_1911_ = leanh::lean_box_uint64(v___x_1910_);
                if v_isShared_1906_ == 0 {
                    leanh::lean_ctor_set(v___x_1905_, 0, v___x_1911_);
                    v___x_1913_ = v___x_1905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
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
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
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
    mut v_file_1924_: *mut leanh::LeanObject,
    mut v_a_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Lake_computeTextFileHash(v_file_1924_);
    leanh::lean_dec_ref(v_file_1924_);
    return v_res_1926_;
}
pub unsafe fn l_Lake_instCoeTextFilePathFilePath___lam__0(
    mut v_x_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_1927_);
    return v_x_1927_;
}
pub unsafe fn l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(
    mut v_x_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_1928_);
    leanh::lean_dec_ref(v_x_1928_);
    return v_res_1929_;
}
pub unsafe fn l_Lake_computeFileHash(
    mut v_file_1935_: *mut leanh::LeanObject,
    mut v_text_1936_: u8,
) -> *mut leanh::LeanObject {
    if v_text_1936_ == 0 {
        let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1938_ = l_Lake_computeBinFileHash(v_file_1935_);
        return v___x_1938_;
    } else {
        let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1939_ = l_Lake_computeTextFileHash(v_file_1935_);
        return v___x_1939_;
    }
}
pub unsafe fn l_Lake_computeFileHash___boxed(
    mut v_file_1940_: *mut leanh::LeanObject,
    mut v_text_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_text_boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_text_boxed_1943_ = (leanh::lean_unbox(v_text_1941_) as u8);
    v_res_1944_ = l_Lake_computeFileHash(v_file_1940_, v_text_boxed_1943_);
    leanh::lean_dec_ref(v_file_1940_);
    return v_res_1944_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__0(
    mut v_ts_1945_: u64,
    mut v_toPure_1946_: *mut leanh::LeanObject,
    mut v_____do__lift_1947_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1948_: u64 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_uint64_mix_hash(v_ts_1945_, v_____do__lift_1947_);
    v___x_1949_ = leanh::lean_box_uint64(v___x_1948_);
    v___x_1950_ =
        leanh::lean_apply_2(v_toPure_1946_, leanh::lean_box(0), v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__0___boxed(
    mut v_ts_1951_: *mut leanh::LeanObject,
    mut v_toPure_1952_: *mut leanh::LeanObject,
    mut v_____do__lift_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ts_boxed_1954_: u64 = 0;
    let mut v_____do__lift_97__boxed_1955_: u64 = 0;
    let mut v_res_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ts_boxed_1954_ = leanh::lean_unbox_uint64(v_ts_1951_);
    leanh::lean_dec_ref(v_ts_1951_);
    v_____do__lift_97__boxed_1955_ = leanh::lean_unbox_uint64(v_____do__lift_1953_);
    leanh::lean_dec_ref(v_____do__lift_1953_);
    v_res_1956_ = l_Lake_computeArrayHash___redArg___lam__0(
        v_ts_boxed_1954_,
        v_toPure_1952_,
        v_____do__lift_97__boxed_1955_,
    );
    return v_res_1956_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__1(
    mut v_toPure_1957_: *mut leanh::LeanObject,
    mut v_inst_1958_: *mut leanh::LeanObject,
    mut v_toBind_1959_: *mut leanh::LeanObject,
    mut v_ts_1960_: u64,
    mut v_t_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = leanh::lean_box_uint64(v_ts_1960_);
    v___f_1963_ = leanh::lean_alloc_closure(
        l_Lake_computeArrayHash___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1963_, 0, v___x_1962_);
    leanh::lean_closure_set(v___f_1963_, 1, v_toPure_1957_);
    v___x_1964_ = leanh::lean_apply_1(v_inst_1958_, v_t_1961_);
    v___x_1965_ = leanh::lean_apply_4(
        v_toBind_1959_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1964_,
        v___f_1963_,
    );
    return v___x_1965_;
}
pub unsafe fn l_Lake_computeArrayHash___redArg___lam__1___boxed(
    mut v_toPure_1966_: *mut leanh::LeanObject,
    mut v_inst_1967_: *mut leanh::LeanObject,
    mut v_toBind_1968_: *mut leanh::LeanObject,
    mut v_ts_1969_: *mut leanh::LeanObject,
    mut v_t_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ts_boxed_1971_: u64 = 0;
    let mut v_res_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ts_boxed_1971_ = leanh::lean_unbox_uint64(v_ts_1969_);
    leanh::lean_dec_ref(v_ts_1969_);
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
    mut v_inst_1975_: *mut leanh::LeanObject,
    mut v_inst_1976_: *mut leanh::LeanObject,
    mut v_as_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    v_toApplicative_1978_ = leanh::lean_ctor_get(v_inst_1976_, 0);
    v_toBind_1979_ = leanh::lean_ctor_get(v_inst_1976_, 1);
    v_toPure_1980_ = leanh::lean_ctor_get(v_toApplicative_1978_, 1);
    v___x_1981_ = leanh::lean_unsigned_to_nat(0);
    v___x_1982_ = lean_array_get_size(v_as_1977_);
    v___x_1983_ = lean_nat_dec_lt(v___x_1981_, v___x_1982_);
    if v___x_1983_ == 0 {
        let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_1980_);
        leanh::lean_dec_ref(v_as_1977_);
        leanh::lean_dec_ref(v_inst_1976_);
        leanh::lean_dec(v_inst_1975_);
        v___x_1984_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
        v___x_1985_ =
            leanh::lean_apply_2(v_toPure_1980_, leanh::lean_box(0), v___x_1984_);
        return v___x_1985_;
    } else {
        let mut v___f_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: u8 = 0;
        leanh::lean_inc(v_toBind_1979_);
        leanh::lean_inc(v_toPure_1980_);
        v___f_1986_ = leanh::lean_alloc_closure(
            l_Lake_computeArrayHash___redArg___lam__1___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        leanh::lean_closure_set(v___f_1986_, 0, v_toPure_1980_);
        leanh::lean_closure_set(v___f_1986_, 1, v_inst_1975_);
        leanh::lean_closure_set(v___f_1986_, 2, v_toBind_1979_);
        v___x_1987_ = lean_nat_dec_le(v___x_1982_, v___x_1982_);
        if v___x_1987_ == 0 {
            if v___x_1983_ == 0 {
                let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_toPure_1980_);
                leanh::lean_dec_ref(v___f_1986_);
                leanh::lean_dec_ref(v_as_1977_);
                leanh::lean_dec_ref(v_inst_1976_);
                v___x_1988_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_1989_ = leanh::lean_apply_2(
                    v_toPure_1980_,
                    leanh::lean_box(0),
                    v___x_1988_,
                );
                return v___x_1989_;
            } else {
                let mut v___x_1990_: usize = 0;
                let mut v___x_1991_: usize = 0;
                let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1990_ = 0usize;
                v___x_1991_ = lean_usize_of_nat(v___x_1982_);
                v___x_1992_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1994_ = 0usize;
            v___x_1995_ = lean_usize_of_nat(v___x_1982_);
            v___x_1996_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
            v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_00_u03b1_1998_: *mut leanh::LeanObject,
    mut v_m_1999_: *mut leanh::LeanObject,
    mut v_inst_2000_: *mut leanh::LeanObject,
    mut v_inst_2001_: *mut leanh::LeanObject,
    mut v_as_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    v_toApplicative_2003_ = leanh::lean_ctor_get(v_inst_2001_, 0);
    v_toBind_2004_ = leanh::lean_ctor_get(v_inst_2001_, 1);
    v_toPure_2005_ = leanh::lean_ctor_get(v_toApplicative_2003_, 1);
    v___x_2006_ = leanh::lean_unsigned_to_nat(0);
    v___x_2007_ = lean_array_get_size(v_as_2002_);
    v___x_2008_ = lean_nat_dec_lt(v___x_2006_, v___x_2007_);
    if v___x_2008_ == 0 {
        let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_2005_);
        leanh::lean_dec_ref(v_as_2002_);
        leanh::lean_dec_ref(v_inst_2001_);
        leanh::lean_dec(v_inst_2000_);
        v___x_2009_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
        v___x_2010_ =
            leanh::lean_apply_2(v_toPure_2005_, leanh::lean_box(0), v___x_2009_);
        return v___x_2010_;
    } else {
        let mut v___f_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: u8 = 0;
        leanh::lean_inc(v_toBind_2004_);
        leanh::lean_inc(v_toPure_2005_);
        v___f_2011_ = leanh::lean_alloc_closure(
            l_Lake_computeArrayHash___redArg___lam__1___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        leanh::lean_closure_set(v___f_2011_, 0, v_toPure_2005_);
        leanh::lean_closure_set(v___f_2011_, 1, v_inst_2000_);
        leanh::lean_closure_set(v___f_2011_, 2, v_toBind_2004_);
        v___x_2012_ = lean_nat_dec_le(v___x_2007_, v___x_2007_);
        if v___x_2012_ == 0 {
            if v___x_2008_ == 0 {
                let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_toPure_2005_);
                leanh::lean_dec_ref(v___f_2011_);
                leanh::lean_dec_ref(v_as_2002_);
                leanh::lean_dec_ref(v_inst_2001_);
                v___x_2013_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_2014_ = leanh::lean_apply_2(
                    v_toPure_2005_,
                    leanh::lean_box(0),
                    v___x_2013_,
                );
                return v___x_2014_;
            } else {
                let mut v___x_2015_: usize = 0;
                let mut v___x_2016_: usize = 0;
                let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2015_ = 0usize;
                v___x_2016_ = lean_usize_of_nat(v___x_2007_);
                v___x_2017_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
                v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
            let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2019_ = 0usize;
            v___x_2020_ = lean_usize_of_nat(v___x_2007_);
            v___x_2021_ = l_Lake_computeArrayHash___redArg___boxed__const__1;
            v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
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
    mut v_inst_2023_: *mut leanh::LeanObject,
    mut v_inst_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ =
        leanh::lean_alloc_closure(l_Lake_computeArrayHash as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_2025_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2025_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2025_, 2, v_inst_2023_);
    leanh::lean_closure_set(v___x_2025_, 3, v_inst_2024_);
    return v___x_2025_;
}
pub unsafe fn l_Lake_instComputeHashArrayOfMonad(
    mut v_00_u03b1_2026_: *mut leanh::LeanObject,
    mut v_m_2027_: *mut leanh::LeanObject,
    mut v_inst_2028_: *mut leanh::LeanObject,
    mut v_inst_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ =
        leanh::lean_alloc_closure(l_Lake_computeArrayHash as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_2030_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2030_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2030_, 2, v_inst_2028_);
    leanh::lean_closure_set(v___x_2030_, 3, v_inst_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lake_MTime_instOfNat___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2031_: u32 = 0;
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = 0;
    v___x_2032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Hash_ofJsonNumber_x3f___closed__5_once),
        _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5,
    );
    v___x_2033_ = leanh::lean_alloc_ctor(0, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_2033_, 0, v___x_2032_);
    leanh::lean_ctor_set_uint32(
        v___x_2033_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2031_,
    );
    return v___x_2033_;
}
pub unsafe fn _init_l_Lake_MTime_instOfNat() -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    return v___x_2034_;
}
pub unsafe fn l_Lake_MTime_instBEq___aux__1(
    mut v_x_2035_: *mut leanh::LeanObject,
    mut v_x_2036_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2037_: u8 = 0;
    v___x_2037_ = l_IO_FS_instBEqSystemTime_beq(v_x_2035_, v_x_2036_);
    return v___x_2037_;
}
pub unsafe fn l_Lake_MTime_instBEq___aux__1___boxed(
    mut v_x_2038_: *mut leanh::LeanObject,
    mut v_x_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2040_: u8 = 0;
    let mut v_r_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ = l_Lake_MTime_instBEq___aux__1(v_x_2038_, v_x_2039_);
    leanh::lean_dec_ref(v_x_2039_);
    leanh::lean_dec_ref(v_x_2038_);
    v_r_2041_ = leanh::lean_box((v_res_2040_) as usize);
    return v_r_2041_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___redArg(
    mut v_x_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2044_);
    return v___x_2045_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___redArg___boxed(
    mut v_x_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_2046_);
    leanh::lean_dec_ref(v_x_2046_);
    return v_res_2047_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1(
    mut v_x_2048_: *mut leanh::LeanObject,
    mut v_prec_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_2048_);
    return v___x_2050_;
}
pub unsafe fn l_Lake_MTime_instRepr___aux__1___boxed(
    mut v_x_2051_: *mut leanh::LeanObject,
    mut v_prec_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lake_MTime_instRepr___aux__1(v_x_2051_, v_prec_2052_);
    leanh::lean_dec(v_prec_2052_);
    leanh::lean_dec_ref(v_x_2051_);
    return v_res_2053_;
}
pub unsafe fn l_Lake_MTime_instOrd___aux__1(
    mut v_x_2056_: *mut leanh::LeanObject,
    mut v_x_2057_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2058_: u8 = 0;
    v___x_2058_ = l_IO_FS_instOrdSystemTime_ord(v_x_2056_, v_x_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Lake_MTime_instOrd___aux__1___boxed(
    mut v_x_2059_: *mut leanh::LeanObject,
    mut v_x_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2061_: u8 = 0;
    let mut v_r_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2061_ = l_Lake_MTime_instOrd___aux__1(v_x_2059_, v_x_2060_);
    leanh::lean_dec_ref(v_x_2060_);
    leanh::lean_dec_ref(v_x_2059_);
    v_r_2062_ = leanh::lean_box((v_res_2061_) as usize);
    return v_r_2062_;
}
pub unsafe fn _init_l_Lake_MTime_instLT() -> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = leanh::lean_box(0);
    return v___x_2065_;
}
pub unsafe fn _init_l_Lake_MTime_instLE() -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = leanh::lean_box(0);
    return v___x_2066_;
}
pub unsafe fn l_Lake_MTime_instMin___lam__0(
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_y_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2069_: u8 = 0;
    v___x_2069_ = l_IO_FS_instOrdSystemTime_ord(v_x_2067_, v_y_2068_);
    if v___x_2069_ == 2 {
        leanh::lean_inc_ref(v_y_2068_);
        return v_y_2068_;
    } else {
        leanh::lean_inc_ref(v_x_2067_);
        return v_x_2067_;
    }
}
pub unsafe fn l_Lake_MTime_instMin___lam__0___boxed(
    mut v_x_2070_: *mut leanh::LeanObject,
    mut v_y_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Lake_MTime_instMin___lam__0(v_x_2070_, v_y_2071_);
    leanh::lean_dec_ref(v_y_2071_);
    leanh::lean_dec_ref(v_x_2070_);
    return v_res_2072_;
}
pub unsafe fn l_Lake_MTime_instMax___lam__0(
    mut v_x_2075_: *mut leanh::LeanObject,
    mut v_y_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2077_: u8 = 0;
    v___x_2077_ = l_IO_FS_instOrdSystemTime_ord(v_x_2075_, v_y_2076_);
    if v___x_2077_ == 2 {
        leanh::lean_inc_ref(v_x_2075_);
        return v_x_2075_;
    } else {
        leanh::lean_inc_ref(v_y_2076_);
        return v_y_2076_;
    }
}
pub unsafe fn l_Lake_MTime_instMax___lam__0___boxed(
    mut v_x_2078_: *mut leanh::LeanObject,
    mut v_y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lake_MTime_instMax___lam__0(v_x_2078_, v_y_2079_);
    leanh::lean_dec_ref(v_y_2079_);
    leanh::lean_dec_ref(v_x_2078_);
    return v_res_2080_;
}
pub unsafe fn _init_l_Lake_MTime_instNilTrace() -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    return v___x_2083_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(
    mut v_inst_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_2085_);
    return v_inst_2085_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(
    mut v_inst_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2087_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(
        v_inst_2086_,
    );
    leanh::lean_dec_ref(v_inst_2086_);
    return v_res_2087_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(
    mut v_00_u03b1_2088_: *mut leanh::LeanObject,
    mut v_inst_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_2089_);
    return v_inst_2089_;
}
pub unsafe fn l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(
    mut v_00_u03b1_2090_: *mut leanh::LeanObject,
    mut v_inst_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(
        v_00_u03b1_2090_,
        v_inst_2091_,
    );
    leanh::lean_dec_ref(v_inst_2091_);
    return v_res_2092_;
}
pub unsafe fn l_Lake_getFileMTime(
    mut v_file_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v_modified_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_a_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2108_: u8 = 0;
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2095_ = lean_io_metadata(v_file_2093_);
                if leanh::lean_obj_tag(v___x_2095_) == 0 {
                    v_a_2096_ = leanh::lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2104_ = (!leanh::lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2104_ == 0 {
                        v___x_2098_ = v___x_2095_;
                        v_isShared_2099_ = v_isSharedCheck_2104_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2096_);
                        leanh::lean_dec(v___x_2095_);
                        v___x_2098_ = leanh::lean_box(0);
                        v_isShared_2099_ = v_isSharedCheck_2104_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2105_ = leanh::lean_ctor_get(v___x_2095_, 0);
                    v_isSharedCheck_2112_ = (!leanh::lean_is_exclusive(v___x_2095_)) as u8;
                    if v_isSharedCheck_2112_ == 0 {
                        v___x_2107_ = v___x_2095_;
                        v_isShared_2108_ = v_isSharedCheck_2112_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2105_);
                        leanh::lean_dec(v___x_2095_);
                        v___x_2107_ = leanh::lean_box(0);
                        v_isShared_2108_ = v_isSharedCheck_2112_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_modified_2100_ = leanh::lean_ctor_get(v_a_2096_, 1);
                leanh::lean_inc_ref(v_modified_2100_);
                leanh::lean_dec(v_a_2096_);
                if v_isShared_2099_ == 0 {
                    leanh::lean_ctor_set(v___x_2098_, 0, v_modified_2100_);
                    v___x_2102_ = v___x_2098_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_modified_2100_);
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
                    v_reuseFailAlloc_2111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
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
    mut v_file_2113_: *mut leanh::LeanObject,
    mut v_a_2114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2115_ = l_Lake_getFileMTime(v_file_2113_);
    leanh::lean_dec_ref(v_file_2113_);
    return v_res_2115_;
}
pub unsafe fn l_Lake_instGetMTimeTextFilePath___lam__0(
    mut v_x_2118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v_modified_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut v_a_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2120_ = lean_io_metadata(v_x_2118_);
                if leanh::lean_obj_tag(v___x_2120_) == 0 {
                    v_a_2121_ = leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2129_ = (!leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2123_ = v___x_2120_;
                        v_isShared_2124_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2121_);
                        leanh::lean_dec(v___x_2120_);
                        v___x_2123_ = leanh::lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2130_ = leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2137_ = (!leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2137_ == 0 {
                        v___x_2132_ = v___x_2120_;
                        v_isShared_2133_ = v_isSharedCheck_2137_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2130_);
                        leanh::lean_dec(v___x_2120_);
                        v___x_2132_ = leanh::lean_box(0);
                        v_isShared_2133_ = v_isSharedCheck_2137_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_modified_2125_ = leanh::lean_ctor_get(v_a_2121_, 1);
                leanh::lean_inc_ref(v_modified_2125_);
                leanh::lean_dec(v_a_2121_);
                if v_isShared_2124_ == 0 {
                    leanh::lean_ctor_set(v___x_2123_, 0, v_modified_2125_);
                    v___x_2127_ = v___x_2123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_modified_2125_);
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
                    v_reuseFailAlloc_2136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
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
    mut v_x_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_2138_);
    leanh::lean_dec_ref(v_x_2138_);
    return v_res_2140_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate___redArg(
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_info_2144_: *mut leanh::LeanObject,
    mut v_self_2145_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2147_ = leanh::lean_apply_2(v_inst_2143_, v_info_2144_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_2147_) == 0 {
        let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: u8 = 0;
        v_a_2148_ = leanh::lean_ctor_get(v___x_2147_, 0);
        leanh::lean_inc(v_a_2148_);
        leanh::lean_dec_ref_known(v___x_2147_, 1);
        v___x_2149_ = l_IO_FS_instOrdSystemTime_ord(v_self_2145_, v_a_2148_);
        leanh::lean_dec(v_a_2148_);
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
        leanh::lean_dec_ref_known(v___x_2147_, 1);
        v___x_2152_ = 0;
        return v___x_2152_;
    }
}
pub unsafe fn l_Lake_MTime_checkUpToDate___redArg___boxed(
    mut v_inst_2153_: *mut leanh::LeanObject,
    mut v_info_2154_: *mut leanh::LeanObject,
    mut v_self_2155_: *mut leanh::LeanObject,
    mut v_a_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2153_, v_info_2154_, v_self_2155_);
    leanh::lean_dec_ref(v_self_2155_);
    v_r_2158_ = leanh::lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate(
    mut v_i_2159_: *mut leanh::LeanObject,
    mut v_inst_2160_: *mut leanh::LeanObject,
    mut v_info_2161_: *mut leanh::LeanObject,
    mut v_self_2162_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2164_: u8 = 0;
    v___x_2164_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2160_, v_info_2161_, v_self_2162_);
    return v___x_2164_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate___boxed(
    mut v_i_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_info_2167_: *mut leanh::LeanObject,
    mut v_self_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2170_: u8 = 0;
    let mut v_r_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2170_ = l_Lake_MTime_checkUpToDate(v_i_2165_, v_inst_2166_, v_info_2167_, v_self_2168_);
    leanh::lean_dec_ref(v_self_2168_);
    v_r_2171_ = leanh::lean_box((v_res_2170_) as usize);
    return v_r_2171_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2181_ = leanh::lean_unsigned_to_nat(11);
    v___x_2182_ = lean_nat_to_int(v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2189_ = leanh::lean_unsigned_to_nat(10);
    v___x_2190_ = lean_nat_to_int(v___x_2189_);
    return v___x_2190_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(
    mut v_x_2194_: *mut leanh::LeanObject,
    mut v_x_2195_: *mut leanh::LeanObject,
    mut v_x_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2196_) == 0 {
                    leanh::lean_dec(v_x_2194_);
                    return v_x_2195_;
                } else {
                    v_head_2197_ = leanh::lean_ctor_get(v_x_2196_, 0);
                    v_tail_2198_ = leanh::lean_ctor_get(v_x_2196_, 1);
                    v_isSharedCheck_2208_ = (!leanh::lean_is_exclusive(v_x_2196_)) as u8;
                    if v_isSharedCheck_2208_ == 0 {
                        v___x_2200_ = v_x_2196_;
                        v_isShared_2201_ = v_isSharedCheck_2208_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2198_);
                        leanh::lean_inc(v_head_2197_);
                        leanh::lean_dec(v_x_2196_);
                        v___x_2200_ = leanh::lean_box(0);
                        v_isShared_2201_ = v_isSharedCheck_2208_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2194_);
                if v_isShared_2201_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2200_, 5);
                    leanh::lean_ctor_set(v___x_2200_, 1, v_x_2194_);
                    leanh::lean_ctor_set(v___x_2200_, 0, v_x_2195_);
                    v___x_2203_ = v___x_2200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2207_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_x_2195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_x_2194_);
                    v___x_2203_ = v_reuseFailAlloc_2207_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2204_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2197_);
                v___x_2205_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2205_, 0, v___x_2203_);
                leanh::lean_ctor_set(v___x_2205_, 1, v___x_2204_);
                v___x_2206_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_2194_, v___x_2205_, v_tail_2198_);
                return v___x_2206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(
    mut v_x_2209_: *mut leanh::LeanObject,
    mut v_x_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2209_) == 0 {
        let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2210_);
        v___x_2211_ = leanh::lean_box(0);
        return v___x_2211_;
    } else {
        let mut v_tail_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2212_ = leanh::lean_ctor_get(v_x_2209_, 1);
        if leanh::lean_obj_tag(v_tail_2212_) == 0 {
            let mut v_head_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2210_);
            v_head_2213_ = leanh::lean_ctor_get(v_x_2209_, 0);
            leanh::lean_inc(v_head_2213_);
            leanh::lean_dec_ref_known(v_x_2209_, 2);
            v___x_2214_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2213_);
            return v___x_2214_;
        } else {
            let mut v_head_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2212_);
            v_head_2215_ = leanh::lean_ctor_get(v_x_2209_, 0);
            leanh::lean_inc(v_head_2215_);
            leanh::lean_dec_ref_known(v_x_2209_, 2);
            v___x_2216_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2215_);
            v___x_2217_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_2210_, v___x_2216_, v_tail_2212_);
            return v___x_2217_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2219_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0;
    v___x_2220_ = lean_string_length(v___x_2219_);
    return v___x_2220_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ = leanh::lean_obj_once(
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
    mut v_xs_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    v___x_2232_ = lean_array_get_size(v_xs_2231_);
    v___x_2233_ = leanh::lean_unsigned_to_nat(0);
    v___x_2234_ = lean_nat_dec_eq(v___x_2232_, v___x_2233_);
    if v___x_2234_ == 0 {
        let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2235_ = lean_array_to_list(v_xs_2231_);
        v___x_2236_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3;
        v___x_2237_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_2235_, v___x_2236_);
        v___x_2238_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6,
        );
        v___x_2239_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7;
        v___x_2240_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2240_, 0, v___x_2239_);
        leanh::lean_ctor_set(v___x_2240_, 1, v___x_2237_);
        v___x_2241_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8;
        v___x_2242_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2242_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2242_, 1, v___x_2241_);
        v___x_2243_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2243_, 0, v___x_2238_);
        leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
        v___x_2244_ = l_Std_Format_fill(v___x_2243_);
        return v___x_2244_;
    } else {
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2231_);
        v___x_2245_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10;
        return v___x_2245_;
    }
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = leanh::lean_unsigned_to_nat(8);
    v___x_2250_ = lean_nat_to_int(v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = leanh::lean_unsigned_to_nat(9);
    v___x_2255_ = lean_nat_to_int(v___x_2254_);
    return v___x_2255_;
}
pub unsafe fn l_Lake_instReprBuildTrace_repr___redArg(
    mut v_x_2256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_caption_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputs_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_2259_: u64 = 0;
    let mut v_mtime_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_caption_2257_ = leanh::lean_ctor_get(v_x_2256_, 0);
    leanh::lean_inc_ref(v_caption_2257_);
    v_inputs_2258_ = leanh::lean_ctor_get(v_x_2256_, 1);
    leanh::lean_inc_ref(v_inputs_2258_);
    v_hash_2259_ = leanh::lean_ctor_get_uint64(
        v_x_2256_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_mtime_2260_ = leanh::lean_ctor_get(v_x_2256_, 2);
    leanh::lean_inc_ref(v_mtime_2260_);
    leanh::lean_dec_ref(v_x_2256_);
    v___x_2261_ = l_Lake_instReprHash_repr___redArg___closed__5;
    v___x_2262_ = l_Lake_instReprBuildTrace_repr___redArg___closed__3;
    v___x_2263_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__4_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4,
    );
    v___x_2264_ = l_String_quote(v_caption_2257_);
    v___x_2265_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2265_, 0, v___x_2264_);
    v___x_2266_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2263_);
    leanh::lean_ctor_set(v___x_2266_, 1, v___x_2265_);
    v___x_2267_ = 0;
    v___x_2268_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2266_);
    leanh::lean_ctor_set_uint8(
        v___x_2268_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2269_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2262_);
    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
    v___x_2270_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2;
    v___x_2271_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2271_, 0, v___x_2269_);
    leanh::lean_ctor_set(v___x_2271_, 1, v___x_2270_);
    v___x_2272_ = leanh::lean_box(1);
    v___x_2273_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2273_, 0, v___x_2271_);
    leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
    v___x_2274_ = l_Lake_instReprBuildTrace_repr___redArg___closed__6;
    v___x_2275_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2275_, 0, v___x_2273_);
    leanh::lean_ctor_set(v___x_2275_, 1, v___x_2274_);
    v___x_2276_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
    leanh::lean_ctor_set(v___x_2276_, 1, v___x_2261_);
    v___x_2277_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__7_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7,
    );
    v___x_2278_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_2258_);
    v___x_2279_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2280_, 0, v___x_2279_);
    leanh::lean_ctor_set_uint8(
        v___x_2280_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2281_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2281_, 0, v___x_2276_);
    leanh::lean_ctor_set(v___x_2281_, 1, v___x_2280_);
    v___x_2282_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    leanh::lean_ctor_set(v___x_2282_, 1, v___x_2270_);
    v___x_2283_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    leanh::lean_ctor_set(v___x_2283_, 1, v___x_2272_);
    v___x_2284_ = l_Lake_instReprBuildTrace_repr___redArg___closed__9;
    v___x_2285_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2285_, 0, v___x_2283_);
    leanh::lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    v___x_2286_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    leanh::lean_ctor_set(v___x_2286_, 1, v___x_2261_);
    v___x_2287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__10_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10,
    );
    v___x_2288_ = l_Lake_instReprHash_repr___redArg(v_hash_2259_);
    v___x_2289_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2289_, 0, v___x_2287_);
    leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
    v___x_2290_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2290_, 0, v___x_2289_);
    leanh::lean_ctor_set_uint8(
        v___x_2290_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2291_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2291_, 0, v___x_2286_);
    leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
    v___x_2292_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    leanh::lean_ctor_set(v___x_2292_, 1, v___x_2270_);
    v___x_2293_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
    leanh::lean_ctor_set(v___x_2293_, 1, v___x_2272_);
    v___x_2294_ = l_Lake_instReprBuildTrace_repr___redArg___closed__12;
    v___x_2295_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2293_);
    leanh::lean_ctor_set(v___x_2295_, 1, v___x_2294_);
    v___x_2296_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2296_, 0, v___x_2295_);
    leanh::lean_ctor_set(v___x_2296_, 1, v___x_2261_);
    v___x_2297_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instReprBuildTrace_repr___redArg___closed__13_once),
        _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13,
    );
    v___x_2298_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_2260_);
    leanh::lean_dec_ref(v_mtime_2260_);
    v___x_2299_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2299_, 0, v___x_2297_);
    leanh::lean_ctor_set(v___x_2299_, 1, v___x_2298_);
    v___x_2300_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    leanh::lean_ctor_set_uint8(
        v___x_2300_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    v___x_2301_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2296_);
    leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
    v___x_2302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprHash_repr___redArg___closed__10_once),
        _init_l_Lake_instReprHash_repr___redArg___closed__10,
    );
    v___x_2303_ = l_Lake_instReprHash_repr___redArg___closed__11;
    v___x_2304_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2304_, 0, v___x_2303_);
    leanh::lean_ctor_set(v___x_2304_, 1, v___x_2301_);
    v___x_2305_ = l_Lake_instReprHash_repr___redArg___closed__12;
    v___x_2306_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2306_, 0, v___x_2304_);
    leanh::lean_ctor_set(v___x_2306_, 1, v___x_2305_);
    v___x_2307_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2307_, 0, v___x_2302_);
    leanh::lean_ctor_set(v___x_2307_, 1, v___x_2306_);
    v___x_2308_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    leanh::lean_ctor_set_uint8(
        v___x_2308_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2267_,
    );
    return v___x_2308_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_2309_: *mut leanh::LeanObject,
    mut v_x_2310_: *mut leanh::LeanObject,
    mut v_x_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2311_) == 0 {
                    leanh::lean_dec(v_x_2309_);
                    return v_x_2310_;
                } else {
                    v_head_2312_ = leanh::lean_ctor_get(v_x_2311_, 0);
                    v_tail_2313_ = leanh::lean_ctor_get(v_x_2311_, 1);
                    v_isSharedCheck_2323_ = (!leanh::lean_is_exclusive(v_x_2311_)) as u8;
                    if v_isSharedCheck_2323_ == 0 {
                        v___x_2315_ = v_x_2311_;
                        v_isShared_2316_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2313_);
                        leanh::lean_inc(v_head_2312_);
                        leanh::lean_dec(v_x_2311_);
                        v___x_2315_ = leanh::lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2309_);
                if v_isShared_2316_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2315_, 5);
                    leanh::lean_ctor_set(v___x_2315_, 1, v_x_2309_);
                    leanh::lean_ctor_set(v___x_2315_, 0, v_x_2310_);
                    v___x_2318_ = v___x_2315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_x_2310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_x_2309_);
                    v___x_2318_ = v_reuseFailAlloc_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2319_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_2312_);
                v___x_2320_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2320_, 0, v___x_2318_);
                leanh::lean_ctor_set(v___x_2320_, 1, v___x_2319_);
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
    mut v_x_2324_: *mut leanh::LeanObject,
    mut v_prec_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2326_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_2324_);
    return v___x_2326_;
}
pub unsafe fn l_Lake_instReprBuildTrace_repr___boxed(
    mut v_x_2327_: *mut leanh::LeanObject,
    mut v_prec_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lake_instReprBuildTrace_repr(v_x_2327_, v_prec_2328_);
    leanh::lean_dec(v_prec_2328_);
    return v_res_2329_;
}
pub unsafe fn l_Lake_BuildTrace_withCaption(
    mut v_caption_2332_: *mut leanh::LeanObject,
    mut v_self_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inputs_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_2335_: u64 = 0;
    let mut v_mtime_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2339_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inputs_2334_ = leanh::lean_ctor_get(v_self_2333_, 1);
                v_hash_2335_ = leanh::lean_ctor_get_uint64(
                    v_self_2333_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_2336_ = leanh::lean_ctor_get(v_self_2333_, 2);
                v_isSharedCheck_2343_ = (!leanh::lean_is_exclusive(v_self_2333_)) as u8;
                if v_isSharedCheck_2343_ == 0 {
                    v_unused_2344_ = leanh::lean_ctor_get(v_self_2333_, 0);
                    leanh::lean_dec(v_unused_2344_);
                    v___x_2338_ = v_self_2333_;
                    v_isShared_2339_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_mtime_2336_);
                    leanh::lean_inc(v_inputs_2334_);
                    leanh::lean_dec(v_self_2333_);
                    v___x_2338_ = leanh::lean_box(0);
                    v_isShared_2339_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2339_ == 0 {
                    leanh::lean_ctor_set(v___x_2338_, 0, v_caption_2332_);
                    v___x_2341_ = v___x_2338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_caption_2332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_inputs_2334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_mtime_2336_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2342_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
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
    mut v_self_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_caption_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_2349_: u64 = 0;
    let mut v_mtime_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_unused_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_caption_2348_ = leanh::lean_ctor_get(v_self_2347_, 0);
                v_hash_2349_ = leanh::lean_ctor_get_uint64(
                    v_self_2347_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_2350_ = leanh::lean_ctor_get(v_self_2347_, 2);
                v_isSharedCheck_2358_ = (!leanh::lean_is_exclusive(v_self_2347_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v_unused_2359_ = leanh::lean_ctor_get(v_self_2347_, 1);
                    leanh::lean_dec(v_unused_2359_);
                    v___x_2352_ = v_self_2347_;
                    v_isShared_2353_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_mtime_2350_);
                    leanh::lean_inc(v_caption_2348_);
                    leanh::lean_dec(v_self_2347_);
                    v___x_2352_ = leanh::lean_box(0);
                    v_isShared_2353_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2354_ = l_Lake_BuildTrace_withoutInputs___closed__0;
                if v_isShared_2353_ == 0 {
                    leanh::lean_ctor_set(v___x_2352_, 1, v___x_2354_);
                    v___x_2356_ = v___x_2352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_caption_2348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_mtime_2350_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2357_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
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
    mut v_caption_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2364_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
    leanh::lean_ctor_set(v___x_2364_, 0, v_caption_2361_);
    leanh::lean_ctor_set(v___x_2364_, 1, v___x_2362_);
    leanh::lean_ctor_set(v___x_2364_, 2, v___x_2363_);
    leanh::lean_ctor_set_uint64(
        v___x_2364_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_hash_2360_,
    );
    return v___x_2364_;
}
pub unsafe fn l_Lake_BuildTrace_ofHash___boxed(
    mut v_hash_2365_: *mut leanh::LeanObject,
    mut v_caption_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hash_boxed_2367_: u64 = 0;
    let mut v_res_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_2367_ = leanh::lean_unbox_uint64(v_hash_2365_);
    leanh::lean_dec_ref(v_hash_2365_);
    v_res_2368_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_2367_, v_caption_2366_);
    return v_res_2368_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeHash___lam__0(
    mut v_hash_2370_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lake_BuildTrace_instCoeHash___lam__0___closed__0;
    v___x_2372_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2374_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
    leanh::lean_ctor_set(v___x_2374_, 0, v___x_2371_);
    leanh::lean_ctor_set(v___x_2374_, 1, v___x_2372_);
    leanh::lean_ctor_set(v___x_2374_, 2, v___x_2373_);
    leanh::lean_ctor_set_uint64(
        v___x_2374_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_hash_2370_,
    );
    return v___x_2374_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeHash___lam__0___boxed(
    mut v_hash_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hash_boxed_2376_: u64 = 0;
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_2376_ = leanh::lean_unbox_uint64(v_hash_2375_);
    leanh::lean_dec_ref(v_hash_2375_);
    v_res_2377_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_2376_);
    return v_res_2377_;
}
pub unsafe fn l_Lake_BuildTrace_ofMTime(
    mut v_mtime_2380_: *mut leanh::LeanObject,
    mut v_caption_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: u64 = 0;
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2383_ = 1723u64;
    v___x_2384_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
    leanh::lean_ctor_set(v___x_2384_, 0, v_caption_2381_);
    leanh::lean_ctor_set(v___x_2384_, 1, v___x_2382_);
    leanh::lean_ctor_set(v___x_2384_, 2, v_mtime_2380_);
    leanh::lean_ctor_set_uint64(
        v___x_2384_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lake_BuildTrace_instCoeMTime___lam__0(
    mut v_mtime_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u64 = 0;
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0;
    v___x_2388_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2389_ = 1723u64;
    v___x_2390_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
    leanh::lean_ctor_set(v___x_2390_, 0, v___x_2387_);
    leanh::lean_ctor_set(v___x_2390_, 1, v___x_2388_);
    leanh::lean_ctor_set(v___x_2390_, 2, v_mtime_2386_);
    leanh::lean_ctor_set_uint64(
        v___x_2390_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2389_,
    );
    return v___x_2390_;
}
pub unsafe fn l_Lake_BuildTrace_nil(
    mut v_caption_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: u64 = 0;
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Lake_BuildTrace_withoutInputs___closed__0;
    v___x_2395_ = 1723u64;
    v___x_2396_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0),
        core::ptr::addr_of_mut!(l_Lake_MTime_instOfNat___closed__0_once),
        _init_l_Lake_MTime_instOfNat___closed__0,
    );
    v___x_2397_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
    leanh::lean_ctor_set(v___x_2397_, 0, v_caption_2393_);
    leanh::lean_ctor_set(v___x_2397_, 1, v___x_2394_);
    leanh::lean_ctor_set(v___x_2397_, 2, v___x_2396_);
    leanh::lean_ctor_set_uint64(
        v___x_2397_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2395_,
    );
    return v___x_2397_;
}
pub unsafe fn _init_l_Lake_BuildTrace_instNilTrace___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2399_ = l_Lake_BuildTrace_instNilTrace___closed__0;
    v___x_2400_ = l_Lake_BuildTrace_nil(v___x_2399_);
    return v___x_2400_;
}
pub unsafe fn _init_l_Lake_BuildTrace_instNilTrace() -> *mut leanh::LeanObject {
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_BuildTrace_instNilTrace___closed__1),
        core::ptr::addr_of_mut!(l_Lake_BuildTrace_instNilTrace___closed__1_once),
        _init_l_Lake_BuildTrace_instNilTrace___closed__1,
    );
    return v___x_2401_;
}
pub unsafe fn l_Lake_BuildTrace_compute___redArg(
    mut v_inst_2402_: *mut leanh::LeanObject,
    mut v_inst_2403_: *mut leanh::LeanObject,
    mut v_inst_2404_: *mut leanh::LeanObject,
    mut v_inst_2405_: *mut leanh::LeanObject,
    mut v_info_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u64 = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut v_a_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_a_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2435_: u8 = 0;
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_info_2406_);
                v___x_2408_ = leanh::lean_apply_1(v_inst_2403_, v_info_2406_);
                v___x_2409_ = leanh::lean_apply_3(
                    v_inst_2404_,
                    leanh::lean_box(0),
                    v___x_2408_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2409_) == 0 {
                    v_a_2410_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    leanh::lean_inc(v_a_2410_);
                    leanh::lean_dec_ref_known(v___x_2409_, 1);
                    leanh::lean_inc(v_info_2406_);
                    v___x_2411_ = leanh::lean_apply_2(
                        v_inst_2405_,
                        v_info_2406_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2411_) == 0 {
                        v_a_2412_ = leanh::lean_ctor_get(v___x_2411_, 0);
                        v_isSharedCheck_2423_ =
                            (!leanh::lean_is_exclusive(v___x_2411_)) as u8;
                        if v_isSharedCheck_2423_ == 0 {
                            v___x_2414_ = v___x_2411_;
                            v_isShared_2415_ = v_isSharedCheck_2423_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2412_);
                            leanh::lean_dec(v___x_2411_);
                            v___x_2414_ = leanh::lean_box(0);
                            v_isShared_2415_ = v_isSharedCheck_2423_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2410_);
                        leanh::lean_dec(v_info_2406_);
                        leanh::lean_dec_ref(v_inst_2402_);
                        v_a_2424_ = leanh::lean_ctor_get(v___x_2411_, 0);
                        v_isSharedCheck_2431_ =
                            (!leanh::lean_is_exclusive(v___x_2411_)) as u8;
                        if v_isSharedCheck_2431_ == 0 {
                            v___x_2426_ = v___x_2411_;
                            v_isShared_2427_ = v_isSharedCheck_2431_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2424_);
                            leanh::lean_dec(v___x_2411_);
                            v___x_2426_ = leanh::lean_box(0);
                            v_isShared_2427_ = v_isSharedCheck_2431_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_info_2406_);
                    leanh::lean_dec_ref(v_inst_2405_);
                    leanh::lean_dec_ref(v_inst_2402_);
                    v_a_2432_ = leanh::lean_ctor_get(v___x_2409_, 0);
                    v_isSharedCheck_2439_ = (!leanh::lean_is_exclusive(v___x_2409_)) as u8;
                    if v_isSharedCheck_2439_ == 0 {
                        v___x_2434_ = v___x_2409_;
                        v_isShared_2435_ = v_isSharedCheck_2439_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2432_);
                        leanh::lean_dec(v___x_2409_);
                        v___x_2434_ = leanh::lean_box(0);
                        v_isShared_2435_ = v_isSharedCheck_2439_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2416_ = leanh::lean_apply_1(v_inst_2402_, v_info_2406_);
                v___x_2417_ = l_Lake_BuildTrace_withoutInputs___closed__0;
                v___x_2418_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
                leanh::lean_ctor_set(v___x_2418_, 0, v___x_2416_);
                leanh::lean_ctor_set(v___x_2418_, 1, v___x_2417_);
                leanh::lean_ctor_set(v___x_2418_, 2, v_a_2412_);
                v___x_2419_ = leanh::lean_unbox_uint64(v_a_2410_);
                leanh::lean_dec(v_a_2410_);
                leanh::lean_ctor_set_uint64(
                    v___x_2418_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2419_,
                );
                if v_isShared_2415_ == 0 {
                    leanh::lean_ctor_set(v___x_2414_, 0, v___x_2418_);
                    v___x_2421_ = v___x_2414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2418_);
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
                    v_reuseFailAlloc_2430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
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
                    v_reuseFailAlloc_2438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
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
    mut v_inst_2440_: *mut leanh::LeanObject,
    mut v_inst_2441_: *mut leanh::LeanObject,
    mut v_inst_2442_: *mut leanh::LeanObject,
    mut v_inst_2443_: *mut leanh::LeanObject,
    mut v_info_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2447_: *mut leanh::LeanObject,
    mut v_m_2448_: *mut leanh::LeanObject,
    mut v_inst_2449_: *mut leanh::LeanObject,
    mut v_inst_2450_: *mut leanh::LeanObject,
    mut v_inst_2451_: *mut leanh::LeanObject,
    mut v_inst_2452_: *mut leanh::LeanObject,
    mut v_info_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2456_: *mut leanh::LeanObject,
    mut v_m_2457_: *mut leanh::LeanObject,
    mut v_inst_2458_: *mut leanh::LeanObject,
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_inst_2460_: *mut leanh::LeanObject,
    mut v_inst_2461_: *mut leanh::LeanObject,
    mut v_info_2462_: *mut leanh::LeanObject,
    mut v_a_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_2465_: *mut leanh::LeanObject,
    mut v_inst_2466_: *mut leanh::LeanObject,
    mut v_inst_2467_: *mut leanh::LeanObject,
    mut v_inst_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = leanh::lean_alloc_closure(
        l_Lake_BuildTrace_compute___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_2469_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2469_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2469_, 2, v_inst_2465_);
    leanh::lean_closure_set(v___x_2469_, 3, v_inst_2466_);
    leanh::lean_closure_set(v___x_2469_, 4, v_inst_2467_);
    leanh::lean_closure_set(v___x_2469_, 5, v_inst_2468_);
    return v___x_2469_;
}
pub unsafe fn l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(
    mut v_00_u03b1_2470_: *mut leanh::LeanObject,
    mut v_m_2471_: *mut leanh::LeanObject,
    mut v_inst_2472_: *mut leanh::LeanObject,
    mut v_inst_2473_: *mut leanh::LeanObject,
    mut v_inst_2474_: *mut leanh::LeanObject,
    mut v_inst_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = leanh::lean_alloc_closure(
        l_Lake_BuildTrace_compute___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    leanh::lean_closure_set(v___x_2476_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2476_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2476_, 2, v_inst_2472_);
    leanh::lean_closure_set(v___x_2476_, 3, v_inst_2473_);
    leanh::lean_closure_set(v___x_2476_, 4, v_inst_2474_);
    leanh::lean_closure_set(v___x_2476_, 5, v_inst_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lake_BuildTrace_mix(
    mut v_t1_2477_: *mut leanh::LeanObject,
    mut v_t2_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_caption_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputs_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_2481_: u64 = 0;
    let mut v_mtime_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v_hash_2486_: u64 = 0;
    let mut v_mtime_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u64 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_caption_2479_ = leanh::lean_ctor_get(v_t1_2477_, 0);
                v_inputs_2480_ = leanh::lean_ctor_get(v_t1_2477_, 1);
                v_hash_2481_ = leanh::lean_ctor_get_uint64(
                    v_t1_2477_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_2482_ = leanh::lean_ctor_get(v_t1_2477_, 2);
                v_isSharedCheck_2497_ = (!leanh::lean_is_exclusive(v_t1_2477_)) as u8;
                if v_isSharedCheck_2497_ == 0 {
                    v___x_2484_ = v_t1_2477_;
                    v_isShared_2485_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_mtime_2482_);
                    leanh::lean_inc(v_inputs_2480_);
                    leanh::lean_inc(v_caption_2479_);
                    leanh::lean_dec(v_t1_2477_);
                    v___x_2484_ = leanh::lean_box(0);
                    v_isShared_2485_ = v_isSharedCheck_2497_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hash_2486_ = leanh::lean_ctor_get_uint64(
                    v_t2_2478_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_2487_ = leanh::lean_ctor_get(v_t2_2478_, 2);
                leanh::lean_inc_ref(v_mtime_2487_);
                v___x_2488_ = lean_array_push(v_inputs_2480_, v_t2_2478_);
                v___x_2489_ = lean_uint64_mix_hash(v_hash_2481_, v_hash_2486_);
                v___x_2490_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_2482_, v_mtime_2487_);
                if v___x_2490_ == 2 {
                    leanh::lean_dec_ref(v_mtime_2487_);
                    if v_isShared_2485_ == 0 {
                        leanh::lean_ctor_set(v___x_2484_, 1, v___x_2488_);
                        v___x_2492_ = v___x_2484_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2493_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_caption_2479_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2488_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_mtime_2482_);
                        v___x_2492_ = v_reuseFailAlloc_2493_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mtime_2482_);
                    if v_isShared_2485_ == 0 {
                        leanh::lean_ctor_set(v___x_2484_, 2, v_mtime_2487_);
                        leanh::lean_ctor_set(v___x_2484_, 1, v___x_2488_);
                        v___x_2495_ = v___x_2484_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(0, 3, (8) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_caption_2479_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2488_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_mtime_2487_);
                        v___x_2495_ = v_reuseFailAlloc_2496_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint64(
                    v___x_2492_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2489_,
                );
                return v___x_2492_;
            }
            3 => {
                leanh::lean_ctor_set_uint64(
                    v___x_2495_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2489_,
                );
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash___redArg(
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_info_2501_: *mut leanh::LeanObject,
    mut v_hash_2502_: u64,
    mut v_self_2503_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_hash_2505_: u64 = 0;
    let mut v___x_2506_: u8 = 0;
    v_hash_2505_ = leanh::lean_ctor_get_uint64(
        v_self_2503_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_2506_ = lean_uint64_dec_eq(v_hash_2502_, v_hash_2505_);
    if v___x_2506_ == 0 {
        leanh::lean_dec(v_info_2501_);
        leanh::lean_dec_ref(v_inst_2500_);
        return v___x_2506_;
    } else {
        let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: u8 = 0;
        v___x_2507_ =
            leanh::lean_apply_2(v_inst_2500_, v_info_2501_, leanh::lean_box(0));
        v___x_2508_ = (leanh::lean_unbox(v___x_2507_) as u8);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(
    mut v_inst_2509_: *mut leanh::LeanObject,
    mut v_info_2510_: *mut leanh::LeanObject,
    mut v_hash_2511_: *mut leanh::LeanObject,
    mut v_self_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hash_boxed_2514_: u64 = 0;
    let mut v_res_2515_: u8 = 0;
    let mut v_r_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_2514_ = leanh::lean_unbox_uint64(v_hash_2511_);
    leanh::lean_dec_ref(v_hash_2511_);
    v_res_2515_ = l_Lake_BuildTrace_checkAgainstHash___redArg(
        v_inst_2509_,
        v_info_2510_,
        v_hash_boxed_2514_,
        v_self_2512_,
    );
    leanh::lean_dec_ref(v_self_2512_);
    v_r_2516_ = leanh::lean_box((v_res_2515_) as usize);
    return v_r_2516_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstHash(
    mut v_i_2517_: *mut leanh::LeanObject,
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_info_2519_: *mut leanh::LeanObject,
    mut v_hash_2520_: u64,
    mut v_self_2521_: *mut leanh::LeanObject,
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
    mut v_i_2524_: *mut leanh::LeanObject,
    mut v_inst_2525_: *mut leanh::LeanObject,
    mut v_info_2526_: *mut leanh::LeanObject,
    mut v_hash_2527_: *mut leanh::LeanObject,
    mut v_self_2528_: *mut leanh::LeanObject,
    mut v_a_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hash_boxed_2530_: u64 = 0;
    let mut v_res_2531_: u8 = 0;
    let mut v_r_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hash_boxed_2530_ = leanh::lean_unbox_uint64(v_hash_2527_);
    leanh::lean_dec_ref(v_hash_2527_);
    v_res_2531_ = l_Lake_BuildTrace_checkAgainstHash(
        v_i_2524_,
        v_inst_2525_,
        v_info_2526_,
        v_hash_boxed_2530_,
        v_self_2528_,
    );
    leanh::lean_dec_ref(v_self_2528_);
    v_r_2532_ = leanh::lean_box((v_res_2531_) as usize);
    return v_r_2532_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___redArg(
    mut v_inst_2533_: *mut leanh::LeanObject,
    mut v_info_2534_: *mut leanh::LeanObject,
    mut v_self_2535_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_mtime_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    v_mtime_2537_ = leanh::lean_ctor_get(v_self_2535_, 2);
    v___x_2538_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2533_, v_info_2534_, v_mtime_2537_);
    return v___x_2538_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_info_2540_: *mut leanh::LeanObject,
    mut v_self_2541_: *mut leanh::LeanObject,
    mut v_a_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2543_: u8 = 0;
    let mut v_r_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ =
        l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_2539_, v_info_2540_, v_self_2541_);
    leanh::lean_dec_ref(v_self_2541_);
    v_r_2544_ = leanh::lean_box((v_res_2543_) as usize);
    return v_r_2544_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime(
    mut v_i_2545_: *mut leanh::LeanObject,
    mut v_inst_2546_: *mut leanh::LeanObject,
    mut v_info_2547_: *mut leanh::LeanObject,
    mut v_self_2548_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_mtime_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    v_mtime_2550_ = leanh::lean_ctor_get(v_self_2548_, 2);
    v___x_2551_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_2546_, v_info_2547_, v_mtime_2550_);
    return v___x_2551_;
}
pub unsafe fn l_Lake_BuildTrace_checkAgainstTime___boxed(
    mut v_i_2552_: *mut leanh::LeanObject,
    mut v_inst_2553_: *mut leanh::LeanObject,
    mut v_info_2554_: *mut leanh::LeanObject,
    mut v_self_2555_: *mut leanh::LeanObject,
    mut v_a_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2557_: u8 = 0;
    let mut v_r_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2557_ =
        l_Lake_BuildTrace_checkAgainstTime(v_i_2552_, v_inst_2553_, v_info_2554_, v_self_2555_);
    leanh::lean_dec_ref(v_self_2555_);
    v_r_2558_ = leanh::lean_box((v_res_2557_) as usize);
    return v_r_2558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Trace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_Hash_nil = _init_l_Lake_Hash_nil();
    l_Lake_Hash_instNilTrace = _init_l_Lake_Hash_instNilTrace();
    l_Lake_MTime_instOfNat = _init_l_Lake_MTime_instOfNat();
    leanh::lean_mark_persistent(l_Lake_MTime_instOfNat);
    l_Lake_MTime_instLT = _init_l_Lake_MTime_instLT();
    leanh::lean_mark_persistent(l_Lake_MTime_instLT);
    l_Lake_MTime_instLE = _init_l_Lake_MTime_instLE();
    leanh::lean_mark_persistent(l_Lake_MTime_instLE);
    l_Lake_MTime_instNilTrace = _init_l_Lake_MTime_instNilTrace();
    leanh::lean_mark_persistent(l_Lake_MTime_instNilTrace);
    l_Lake_BuildTrace_instNilTrace = _init_l_Lake_BuildTrace_instNilTrace();
    leanh::lean_mark_persistent(l_Lake_BuildTrace_instNilTrace);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Trace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Trace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Trace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Trace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Trace(builtin);
}