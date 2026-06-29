// Lean compiler output
// Module: Init.Data.String.Slice
// Imports: Init.Data.String.Pattern Init.Data.Ord.Basic Init.Data.Iterators.Combinators.FilterMap Init.Data.String.ToSlice Init.Data.String.Subslice Init.Data.String.Iter.Basic Init.Data.String.Iterate Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.Option.Lemmas Init.Data.String.Termination Init.Omega
use crate::r#gen::Init::Data::Char::Basic::l_Char_isWhitespace___boxed;
use crate::r#gen::Init::Data::Int::Basic::{l_Int_instInhabited, l_Int_negOfNat};
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x3f, l_String_Slice_Pos_nextn, l_String_Slice_slice_x21,
};
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prev_x3f, l_String_Slice_Pos_prevn, l_String_Slice_posLE,
};
use crate::r#gen::Init::Data::String::Iter::Basic::{
    initialize_Init_Data_String_Iter_Basic, runtime_initialize_Init_Data_String_Iter_Basic,
};
use crate::r#gen::Init::Data::String::Iterate::{
    initialize_Init_Data_String_Iterate, l_String_Slice_positions,
    runtime_initialize_Init_Data_String_Iterate,
};
use crate::r#gen::Init::Data::String::Pattern::Pred::{
    l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool,
    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool,
};
use crate::r#gen::Init::Data::String::Pattern::{
    initialize_Init_Data_String_Pattern, runtime_initialize_Init_Data_String_Pattern,
};
use crate::r#gen::Init::Data::String::Subslice::{
    initialize_Init_Data_String_Subslice, l_String_Slice_subslice_x21,
    runtime_initialize_Init_Data_String_Subslice,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Data::String::ToSlice::{
    initialize_Init_Data_String_ToSlice, runtime_initialize_Init_Data_String_ToSlice,
};
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::String::Slice::{lean_slice_dec_lt, lean_slice_hash};
use crate::lean_imports_rs::Init::Data::UInt::Basic::lean_uint8_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_nat,
};
pub static l_String_Slice_instHAppend___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_instHAppend___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instHAppend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instHAppend___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instHAppend: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instHAppend___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instBEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instBEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instHashable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instOrd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_replace___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_replace___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_replace___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_replace___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_replace___redArg___closed__1_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_String_Slice_replace___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_replace___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_trimAsciiStart___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Char_isWhitespace___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_trimAsciiStart___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_trimAsciiStart___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_trimAsciiStart___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_trimAsciiStart___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_find_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_find_x3f___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_String_Slice_find_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_find_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_contains___redArg___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_String_Slice_contains___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_contains___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_contains___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_contains___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_String_Slice_contains___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_contains___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_trimAsciiEnd___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_trimAsciiEnd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_isNat___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_String_Slice_isNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_isNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_toNat_x21___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 83, 108,
            105, 99, 101, 0,
        ],
    };
static mut l_String_Slice_toNat_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_toNat_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_toNat_x21___closed__1_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 116, 111, 78, 97, 116, 33,
            0,
        ],
    };
static mut l_String_Slice_toNat_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_toNat_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_toNat_x21___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [78, 97, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0],
    };
static mut l_String_Slice_toNat_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_toNat_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_toNat_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_toNat_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_toInt_x21___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [73, 110, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0],
    };
static mut l_String_Slice_toInt_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_toInt_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instToFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_instToFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_instToFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instToFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Slice_instHAppend___lam__0(
    mut v_s_3385_: *mut crate::leanh::LeanObject,
    mut v_t_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3387_ = crate::leanh::lean_ctor_get(v_t_3386_, 0);
    v_startInclusive_3388_ = crate::leanh::lean_ctor_get(v_t_3386_, 1);
    v_endExclusive_3389_ = crate::leanh::lean_ctor_get(v_t_3386_, 2);
    v___x_3390_ =
        lean_string_utf8_extract(v_str_3387_, v_startInclusive_3388_, v_endExclusive_3389_);
    v___x_3391_ = lean_string_append(v_s_3385_, v___x_3390_);
    crate::leanh::lean_dec_ref(v___x_3390_);
    return v___x_3391_;
}
pub unsafe fn l_String_Slice_instHAppend___lam__0___boxed(
    mut v_s_3392_: *mut crate::leanh::LeanObject,
    mut v_t_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3394_ = l_String_Slice_instHAppend___lam__0(v_s_3392_, v_t_3393_);
    crate::leanh::lean_dec_ref(v_t_3393_);
    return v_res_3394_;
}
pub unsafe fn l_String_Slice_beq(
    mut v_s1_3397_: *mut crate::leanh::LeanObject,
    mut v_s2_3398_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    v_str_3399_ = crate::leanh::lean_ctor_get(v_s1_3397_, 0);
    v_startInclusive_3400_ = crate::leanh::lean_ctor_get(v_s1_3397_, 1);
    v_endExclusive_3401_ = crate::leanh::lean_ctor_get(v_s1_3397_, 2);
    v_str_3402_ = crate::leanh::lean_ctor_get(v_s2_3398_, 0);
    v_startInclusive_3403_ = crate::leanh::lean_ctor_get(v_s2_3398_, 1);
    v_endExclusive_3404_ = crate::leanh::lean_ctor_get(v_s2_3398_, 2);
    v___x_3405_ = lean_nat_sub(v_endExclusive_3401_, v_startInclusive_3400_);
    v___x_3406_ = lean_nat_sub(v_endExclusive_3404_, v_startInclusive_3403_);
    v___x_3407_ = lean_nat_dec_eq(v___x_3405_, v___x_3406_);
    crate::leanh::lean_dec(v___x_3406_);
    if v___x_3407_ == 0 {
        crate::leanh::lean_dec(v___x_3405_);
        return v___x_3407_;
    } else {
        let mut v___x_3408_: u8 = 0;
        v___x_3408_ = lean_string_memcmp(
            v_str_3399_,
            v_str_3402_,
            v_startInclusive_3400_,
            v_startInclusive_3403_,
            v___x_3405_,
        );
        crate::leanh::lean_dec(v___x_3405_);
        return v___x_3408_;
    }
}
pub unsafe fn l_String_Slice_beq___boxed(
    mut v_s1_3409_: *mut crate::leanh::LeanObject,
    mut v_s2_3410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3411_: u8 = 0;
    let mut v_r_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_String_Slice_beq(v_s1_3409_, v_s2_3410_);
    crate::leanh::lean_dec_ref(v_s2_3410_);
    crate::leanh::lean_dec_ref(v_s1_3409_);
    v_r_3412_ = crate::leanh::lean_box((v_res_3411_) as usize);
    return v_r_3412_;
}
pub unsafe fn l_String_Slice_toString(
    mut v_s_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3416_ = crate::leanh::lean_ctor_get(v_s_3415_, 0);
    v_startInclusive_3417_ = crate::leanh::lean_ctor_get(v_s_3415_, 1);
    v_endExclusive_3418_ = crate::leanh::lean_ctor_get(v_s_3415_, 2);
    v___x_3419_ =
        lean_string_utf8_extract(v_str_3416_, v_startInclusive_3417_, v_endExclusive_3418_);
    return v___x_3419_;
}
pub unsafe fn l_String_Slice_toString___boxed(
    mut v_s_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_String_Slice_toString(v_s_3420_);
    crate::leanh::lean_dec_ref(v_s_3420_);
    return v_res_3421_;
}
pub unsafe fn l_String_Slice_hash___boxed(
    mut v_s_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3426_: u64 = 0;
    let mut v_r_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = lean_slice_hash(v_s_3425_);
    crate::leanh::lean_dec_ref(v_s_3425_);
    v_r_3427_ = crate::leanh::lean_box_uint64(v_res_3426_);
    return v_r_3427_;
}
pub unsafe fn _init_l_String_Slice_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = crate::leanh::lean_box(0);
    return v___x_3430_;
}
pub unsafe fn l_String_Slice_instDecidableLt___boxed(
    mut v_x_3433_: *mut crate::leanh::LeanObject,
    mut v_y_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3435_: u8 = 0;
    let mut v_r_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3435_ = lean_slice_dec_lt(v_x_3433_, v_y_3434_);
    crate::leanh::lean_dec_ref(v_y_3434_);
    crate::leanh::lean_dec_ref(v_x_3433_);
    v_r_3436_ = crate::leanh::lean_box((v_res_3435_) as usize);
    return v_r_3436_;
}
pub unsafe fn l_String_Slice_instOrd___lam__0(
    mut v_x_3437_: *mut crate::leanh::LeanObject,
    mut v_y_3438_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3439_: u8 = 0;
    v___x_3439_ = lean_slice_dec_lt(v_x_3437_, v_y_3438_);
    if v___x_3439_ == 0 {
        let mut v___x_3440_: u8 = 0;
        v___x_3440_ = l_String_Slice_beq(v_x_3437_, v_y_3438_);
        if v___x_3440_ == 0 {
            let mut v___x_3441_: u8 = 0;
            v___x_3441_ = 2;
            return v___x_3441_;
        } else {
            let mut v___x_3442_: u8 = 0;
            v___x_3442_ = 1;
            return v___x_3442_;
        }
    } else {
        let mut v___x_3443_: u8 = 0;
        v___x_3443_ = 0;
        return v___x_3443_;
    }
}
pub unsafe fn l_String_Slice_instOrd___lam__0___boxed(
    mut v_x_3444_: *mut crate::leanh::LeanObject,
    mut v_y_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3446_: u8 = 0;
    let mut v_r_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_String_Slice_instOrd___lam__0(v_x_3444_, v_y_3445_);
    crate::leanh::lean_dec_ref(v_y_3445_);
    crate::leanh::lean_dec_ref(v_x_3444_);
    v_r_3447_ = crate::leanh::lean_box((v_res_3446_) as usize);
    return v_r_3447_;
}
pub unsafe fn _init_l_String_Slice_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = crate::leanh::lean_box(0);
    return v___x_3450_;
}
pub unsafe fn l_String_Slice_instDecidableLE(
    mut v_x_3451_: *mut crate::leanh::LeanObject,
    mut v_y_3452_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3453_: u8 = 0;
    v___x_3453_ = lean_slice_dec_lt(v_x_3451_, v_y_3452_);
    if v___x_3453_ == 0 {
        let mut v___x_3454_: u8 = 0;
        v___x_3454_ = 1;
        return v___x_3454_;
    } else {
        let mut v___x_3455_: u8 = 0;
        v___x_3455_ = 0;
        return v___x_3455_;
    }
}
pub unsafe fn l_String_Slice_instDecidableLE___boxed(
    mut v_x_3456_: *mut crate::leanh::LeanObject,
    mut v_y_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3458_: u8 = 0;
    let mut v_r_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_String_Slice_instDecidableLE(v_x_3456_, v_y_3457_);
    crate::leanh::lean_dec_ref(v_y_3457_);
    crate::leanh::lean_dec_ref(v_x_3456_);
    v_r_3459_ = crate::leanh::lean_box((v_res_3458_) as usize);
    return v_r_3459_;
}
pub unsafe fn l_String_Slice_startsWith___redArg(
    mut v_s_3460_: *mut crate::leanh::LeanObject,
    mut v_inst_3461_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startsWith_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    v_startsWith_3462_ = crate::leanh::lean_ctor_get(v_inst_3461_, 2);
    crate::leanh::lean_inc_ref(v_startsWith_3462_);
    crate::leanh::lean_dec_ref(v_inst_3461_);
    v___x_3463_ = crate::leanh::lean_apply_1(v_startsWith_3462_, v_s_3460_);
    v___x_3464_ = (crate::leanh::lean_unbox(v___x_3463_) as u8);
    return v___x_3464_;
}
pub unsafe fn l_String_Slice_startsWith___redArg___boxed(
    mut v_s_3465_: *mut crate::leanh::LeanObject,
    mut v_inst_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3467_: u8 = 0;
    let mut v_r_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_String_Slice_startsWith___redArg(v_s_3465_, v_inst_3466_);
    v_r_3468_ = crate::leanh::lean_box((v_res_3467_) as usize);
    return v_r_3468_;
}
pub unsafe fn l_String_Slice_startsWith(
    mut v_00_u03c1_3469_: *mut crate::leanh::LeanObject,
    mut v_s_3470_: *mut crate::leanh::LeanObject,
    mut v_pat_3471_: *mut crate::leanh::LeanObject,
    mut v_inst_3472_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startsWith_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    v_startsWith_3473_ = crate::leanh::lean_ctor_get(v_inst_3472_, 2);
    crate::leanh::lean_inc_ref(v_startsWith_3473_);
    crate::leanh::lean_dec_ref(v_inst_3472_);
    v___x_3474_ = crate::leanh::lean_apply_1(v_startsWith_3473_, v_s_3470_);
    v___x_3475_ = (crate::leanh::lean_unbox(v___x_3474_) as u8);
    return v___x_3475_;
}
pub unsafe fn l_String_Slice_startsWith___boxed(
    mut v_00_u03c1_3476_: *mut crate::leanh::LeanObject,
    mut v_s_3477_: *mut crate::leanh::LeanObject,
    mut v_pat_3478_: *mut crate::leanh::LeanObject,
    mut v_inst_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: u8 = 0;
    let mut v_r_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_String_Slice_startsWith(v_00_u03c1_3476_, v_s_3477_, v_pat_3478_, v_inst_3479_);
    crate::leanh::lean_dec(v_pat_3478_);
    v_r_3481_ = crate::leanh::lean_box((v_res_3480_) as usize);
    return v_r_3481_;
}
pub unsafe fn l_String_Slice_SplitIterator_ctorIdx___redArg(
    mut v_x_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3482_) == 0 {
        let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3483_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3483_;
    } else {
        let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3484_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3484_;
    }
}
pub unsafe fn l_String_Slice_SplitIterator_ctorIdx___redArg___boxed(
    mut v_x_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3486_ = l_String_Slice_SplitIterator_ctorIdx___redArg(v_x_3485_);
    crate::leanh::lean_dec(v_x_3485_);
    return v_res_3486_;
}
pub unsafe fn l_String_Slice_SplitIterator_ctorIdx(
    mut v_00_u03c3_3487_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3488_: *mut crate::leanh::LeanObject,
    mut v_pat_3489_: *mut crate::leanh::LeanObject,
    mut v_s_3490_: *mut crate::leanh::LeanObject,
    mut v_inst_3491_: *mut crate::leanh::LeanObject,
    mut v_x_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3493_ = l_String_Slice_SplitIterator_ctorIdx___redArg(v_x_3492_);
    return v___x_3493_;
}
pub unsafe fn l_String_Slice_SplitIterator_ctorIdx___boxed(
    mut v_00_u03c3_3494_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3495_: *mut crate::leanh::LeanObject,
    mut v_pat_3496_: *mut crate::leanh::LeanObject,
    mut v_s_3497_: *mut crate::leanh::LeanObject,
    mut v_inst_3498_: *mut crate::leanh::LeanObject,
    mut v_x_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_String_Slice_SplitIterator_ctorIdx(
        v_00_u03c3_3494_,
        v_00_u03c1_3495_,
        v_pat_3496_,
        v_s_3497_,
        v_inst_3498_,
        v_x_3499_,
    );
    crate::leanh::lean_dec(v_x_3499_);
    crate::leanh::lean_dec(v_inst_3498_);
    crate::leanh::lean_dec_ref(v_s_3497_);
    crate::leanh::lean_dec(v_pat_3496_);
    return v_res_3500_;
}
pub unsafe fn l_String_Slice_SplitIterator_ctorElim___redArg(
    mut v_t_3501_: *mut crate::leanh::LeanObject,
    mut v_k_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3501_) == 0 {
        let mut v_currPos_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_currPos_3503_ = crate::leanh::lean_ctor_get(v_t_3501_, 0);
        crate::leanh::lean_inc(v_currPos_3503_);
        v_searcher_3504_ = crate::leanh::lean_ctor_get(v_t_3501_, 1);
        crate::leanh::lean_inc(v_searcher_3504_);
        crate::leanh::lean_dec_ref_known(v_t_3501_, 2);
        v___x_3505_ = crate::leanh::lean_apply_2(v_k_3502_, v_currPos_3503_, v_searcher_3504_);
        return v___x_3505_;
    } else {
        return v_k_3502_;
    }
}
pub unsafe fn l_String_Slice_SplitIterator_ctorElim(
    mut v_00_u03c3_3506_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3507_: *mut crate::leanh::LeanObject,
    mut v_pat_3508_: *mut crate::leanh::LeanObject,
    mut v_s_3509_: *mut crate::leanh::LeanObject,
    mut v_inst_3510_: *mut crate::leanh::LeanObject,
    mut v_motive_3511_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3512_: *mut crate::leanh::LeanObject,
    mut v_t_3513_: *mut crate::leanh::LeanObject,
    mut v_h_3514_: *mut crate::leanh::LeanObject,
    mut v_k_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_3513_, v_k_3515_);
    return v___x_3516_;
}
pub unsafe fn l_String_Slice_SplitIterator_ctorElim___boxed(
    mut v_00_u03c3_3517_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3518_: *mut crate::leanh::LeanObject,
    mut v_pat_3519_: *mut crate::leanh::LeanObject,
    mut v_s_3520_: *mut crate::leanh::LeanObject,
    mut v_inst_3521_: *mut crate::leanh::LeanObject,
    mut v_motive_3522_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3523_: *mut crate::leanh::LeanObject,
    mut v_t_3524_: *mut crate::leanh::LeanObject,
    mut v_h_3525_: *mut crate::leanh::LeanObject,
    mut v_k_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_String_Slice_SplitIterator_ctorElim(
        v_00_u03c3_3517_,
        v_00_u03c1_3518_,
        v_pat_3519_,
        v_s_3520_,
        v_inst_3521_,
        v_motive_3522_,
        v_ctorIdx_3523_,
        v_t_3524_,
        v_h_3525_,
        v_k_3526_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3523_);
    crate::leanh::lean_dec(v_inst_3521_);
    crate::leanh::lean_dec_ref(v_s_3520_);
    crate::leanh::lean_dec(v_pat_3519_);
    return v_res_3527_;
}
pub unsafe fn l_String_Slice_SplitIterator_operating_elim___redArg(
    mut v_t_3528_: *mut crate::leanh::LeanObject,
    mut v_operating_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3530_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_3528_, v_operating_3529_);
    return v___x_3530_;
}
pub unsafe fn l_String_Slice_SplitIterator_operating_elim(
    mut v_00_u03c3_3531_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3532_: *mut crate::leanh::LeanObject,
    mut v_pat_3533_: *mut crate::leanh::LeanObject,
    mut v_s_3534_: *mut crate::leanh::LeanObject,
    mut v_inst_3535_: *mut crate::leanh::LeanObject,
    mut v_motive_3536_: *mut crate::leanh::LeanObject,
    mut v_t_3537_: *mut crate::leanh::LeanObject,
    mut v_h_3538_: *mut crate::leanh::LeanObject,
    mut v_operating_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_3537_, v_operating_3539_);
    return v___x_3540_;
}
pub unsafe fn l_String_Slice_SplitIterator_operating_elim___boxed(
    mut v_00_u03c3_3541_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3542_: *mut crate::leanh::LeanObject,
    mut v_pat_3543_: *mut crate::leanh::LeanObject,
    mut v_s_3544_: *mut crate::leanh::LeanObject,
    mut v_inst_3545_: *mut crate::leanh::LeanObject,
    mut v_motive_3546_: *mut crate::leanh::LeanObject,
    mut v_t_3547_: *mut crate::leanh::LeanObject,
    mut v_h_3548_: *mut crate::leanh::LeanObject,
    mut v_operating_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l_String_Slice_SplitIterator_operating_elim(
        v_00_u03c3_3541_,
        v_00_u03c1_3542_,
        v_pat_3543_,
        v_s_3544_,
        v_inst_3545_,
        v_motive_3546_,
        v_t_3547_,
        v_h_3548_,
        v_operating_3549_,
    );
    crate::leanh::lean_dec(v_inst_3545_);
    crate::leanh::lean_dec_ref(v_s_3544_);
    crate::leanh::lean_dec(v_pat_3543_);
    return v_res_3550_;
}
pub unsafe fn l_String_Slice_SplitIterator_atEnd_elim___redArg(
    mut v_t_3551_: *mut crate::leanh::LeanObject,
    mut v_atEnd_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_3551_, v_atEnd_3552_);
    return v___x_3553_;
}
pub unsafe fn l_String_Slice_SplitIterator_atEnd_elim(
    mut v_00_u03c3_3554_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3555_: *mut crate::leanh::LeanObject,
    mut v_pat_3556_: *mut crate::leanh::LeanObject,
    mut v_s_3557_: *mut crate::leanh::LeanObject,
    mut v_inst_3558_: *mut crate::leanh::LeanObject,
    mut v_motive_3559_: *mut crate::leanh::LeanObject,
    mut v_t_3560_: *mut crate::leanh::LeanObject,
    mut v_h_3561_: *mut crate::leanh::LeanObject,
    mut v_atEnd_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3563_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_3560_, v_atEnd_3562_);
    return v___x_3563_;
}
pub unsafe fn l_String_Slice_SplitIterator_atEnd_elim___boxed(
    mut v_00_u03c3_3564_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3565_: *mut crate::leanh::LeanObject,
    mut v_pat_3566_: *mut crate::leanh::LeanObject,
    mut v_s_3567_: *mut crate::leanh::LeanObject,
    mut v_inst_3568_: *mut crate::leanh::LeanObject,
    mut v_motive_3569_: *mut crate::leanh::LeanObject,
    mut v_t_3570_: *mut crate::leanh::LeanObject,
    mut v_h_3571_: *mut crate::leanh::LeanObject,
    mut v_atEnd_3572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3573_ = l_String_Slice_SplitIterator_atEnd_elim(
        v_00_u03c3_3564_,
        v_00_u03c1_3565_,
        v_pat_3566_,
        v_s_3567_,
        v_inst_3568_,
        v_motive_3569_,
        v_t_3570_,
        v_h_3571_,
        v_atEnd_3572_,
    );
    crate::leanh::lean_dec(v_inst_3568_);
    crate::leanh::lean_dec_ref(v_s_3567_);
    crate::leanh::lean_dec(v_pat_3566_);
    return v_res_3573_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitIterator_default(
    mut v_00_u03c3_3574_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3575_: *mut crate::leanh::LeanObject,
    mut v_pat_3576_: *mut crate::leanh::LeanObject,
    mut v_s_3577_: *mut crate::leanh::LeanObject,
    mut v_inst_3578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = crate::leanh::lean_box(1);
    return v___x_3579_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitIterator_default___boxed(
    mut v_00_u03c3_3580_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_3581_: *mut crate::leanh::LeanObject,
    mut v_pat_3582_: *mut crate::leanh::LeanObject,
    mut v_s_3583_: *mut crate::leanh::LeanObject,
    mut v_inst_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ = l_String_Slice_instInhabitedSplitIterator_default(
        v_00_u03c3_3580_,
        v_00_u03c1_3581_,
        v_pat_3582_,
        v_s_3583_,
        v_inst_3584_,
    );
    crate::leanh::lean_dec(v_inst_3584_);
    crate::leanh::lean_dec_ref(v_s_3583_);
    crate::leanh::lean_dec(v_pat_3582_);
    return v_res_3585_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitIterator(
    mut v_a_3586_: *mut crate::leanh::LeanObject,
    mut v_a_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3591_ = crate::leanh::lean_box(1);
    return v___x_3591_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitIterator___boxed(
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_String_Slice_instInhabitedSplitIterator(
        v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_,
    );
    crate::leanh::lean_dec(v_a_3596_);
    crate::leanh::lean_dec_ref(v_a_3595_);
    crate::leanh::lean_dec(v_a_3594_);
    return v_res_3597_;
}
pub unsafe fn l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(
    mut v_x_3598_: u8,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___boxed(
    mut v_x_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3600_: u8 = 0;
    let mut v_res_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3600_ = (crate::leanh::lean_unbox(v_x_3599_) as u8);
    v_res_3601_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(v_x_boxed_3600_);
    return v_res_3601_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(
    mut v_inst_3602_: *mut crate::leanh::LeanObject,
    mut v_s_3603_: *mut crate::leanh::LeanObject,
    mut v_x_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currPos_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3609_: u8 = 0;
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v_startPos_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_unused_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_startInclusive_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3604_) == 0 {
                    v_currPos_3605_ = crate::leanh::lean_ctor_get(v_x_3604_, 0);
                    v_searcher_3606_ = crate::leanh::lean_ctor_get(v_x_3604_, 1);
                    v_isSharedCheck_3649_ = (!crate::leanh::lean_is_exclusive(v_x_3604_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v___x_3608_ = v_x_3604_;
                        v_isShared_3609_ = v_isSharedCheck_3649_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_3606_);
                        crate::leanh::lean_inc(v_currPos_3605_);
                        crate::leanh::lean_dec(v_x_3604_);
                        v___x_3608_ = crate::leanh::lean_box(0);
                        v_isShared_3609_ = v_isSharedCheck_3649_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_3603_);
                    crate::leanh::lean_dec(v_inst_3602_);
                    v___x_3650_ = crate::leanh::lean_box(2);
                    return v___x_3650_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_3603_);
                v___x_3610_ = crate::leanh::lean_apply_2(v_inst_3602_, v_s_3603_, v_searcher_3606_);
                match crate::leanh::lean_obj_tag(v___x_3610_) {
                    0 => {
                        v_out_3611_ = crate::leanh::lean_ctor_get(v___x_3610_, 1);
                        crate::leanh::lean_inc(v_out_3611_);
                        if crate::leanh::lean_obj_tag(v_out_3611_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_3611_, 2);
                            crate::leanh::lean_dec_ref(v_s_3603_);
                            v_it_3612_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                            crate::leanh::lean_inc(v_it_3612_);
                            crate::leanh::lean_dec_ref_known(v___x_3610_, 2);
                            if v_isShared_3609_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3608_, 1, v_it_3612_);
                                v___x_3614_ = v___x_3608_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3616_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3616_,
                                    0,
                                    v_currPos_3605_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_it_3612_);
                                v___x_3614_ = v_reuseFailAlloc_3616_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_3617_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                            v_isSharedCheck_3630_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                            if v_isSharedCheck_3630_ == 0 {
                                v_unused_3631_ = crate::leanh::lean_ctor_get(v___x_3610_, 1);
                                crate::leanh::lean_dec(v_unused_3631_);
                                v___x_3619_ = v___x_3610_;
                                v_isShared_3620_ = v_isSharedCheck_3630_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_3617_);
                                crate::leanh::lean_dec(v___x_3610_);
                                v___x_3619_ = crate::leanh::lean_box(0);
                                v_isShared_3620_ = v_isSharedCheck_3630_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_3603_);
                        v_it_3632_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                        v_isSharedCheck_3642_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                        if v_isSharedCheck_3642_ == 0 {
                            v___x_3634_ = v___x_3610_;
                            v_isShared_3635_ = v_isSharedCheck_3642_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_3632_);
                            crate::leanh::lean_dec(v___x_3610_);
                            v___x_3634_ = crate::leanh::lean_box(0);
                            v_isShared_3635_ = v_isSharedCheck_3642_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_3608_);
                        v_startInclusive_3643_ = crate::leanh::lean_ctor_get(v_s_3603_, 1);
                        crate::leanh::lean_inc(v_startInclusive_3643_);
                        v_endExclusive_3644_ = crate::leanh::lean_ctor_get(v_s_3603_, 2);
                        crate::leanh::lean_inc(v_endExclusive_3644_);
                        crate::leanh::lean_dec_ref(v_s_3603_);
                        v___x_3645_ = lean_nat_sub(v_endExclusive_3644_, v_startInclusive_3643_);
                        crate::leanh::lean_dec(v_startInclusive_3643_);
                        crate::leanh::lean_dec(v_endExclusive_3644_);
                        v_slice_3646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_slice_3646_, 0, v_currPos_3605_);
                        crate::leanh::lean_ctor_set(v_slice_3646_, 1, v___x_3645_);
                        v___x_3647_ = crate::leanh::lean_box(1);
                        v___x_3648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3648_, 0, v___x_3647_);
                        crate::leanh::lean_ctor_set(v___x_3648_, 1, v_slice_3646_);
                        return v___x_3648_;
                    }
                }
            }
            2 => {
                v___x_3615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                return v___x_3615_;
            }
            3 => {
                v_startPos_3621_ = crate::leanh::lean_ctor_get(v_out_3611_, 0);
                crate::leanh::lean_inc(v_startPos_3621_);
                v_endPos_3622_ = crate::leanh::lean_ctor_get(v_out_3611_, 1);
                crate::leanh::lean_inc(v_endPos_3622_);
                crate::leanh::lean_dec_ref_known(v_out_3611_, 2);
                v_slice_3623_ =
                    l_String_Slice_subslice_x21(v_s_3603_, v_currPos_3605_, v_startPos_3621_);
                crate::leanh::lean_dec_ref(v_s_3603_);
                if v_isShared_3609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3608_, 1, v_it_3617_);
                    crate::leanh::lean_ctor_set(v___x_3608_, 0, v_endPos_3622_);
                    v_nextIt_3625_ = v___x_3608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_endPos_3622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_it_3617_);
                    v_nextIt_3625_ = v_reuseFailAlloc_3629_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3620_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3619_, 1, v_slice_3623_);
                    crate::leanh::lean_ctor_set(v___x_3619_, 0, v_nextIt_3625_);
                    v___x_3627_ = v___x_3619_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_nextIt_3625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_slice_3623_);
                    v___x_3627_ = v_reuseFailAlloc_3628_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3627_;
            }
            6 => {
                if v_isShared_3609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3608_, 1, v_it_3632_);
                    v___x_3637_ = v___x_3608_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_currPos_3605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_it_3632_);
                    v___x_3637_ = v_reuseFailAlloc_3641_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3634_, 0, v___x_3637_);
                    v___x_3639_ = v___x_3634_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(
    mut v_inst_3651_: *mut crate::leanh::LeanObject,
    mut v_s_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3653_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3653_, 0, v_inst_3651_);
    crate::leanh::lean_closure_set(v___f_3653_, 1, v_s_3652_);
    return v___f_3653_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorIdSubslice(
    mut v_00_u03c1_3654_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3655_: *mut crate::leanh::LeanObject,
    mut v_inst_3656_: *mut crate::leanh::LeanObject,
    mut v_pat_3657_: *mut crate::leanh::LeanObject,
    mut v_inst_3658_: *mut crate::leanh::LeanObject,
    mut v_s_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3660_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3660_, 0, v_inst_3656_);
    crate::leanh::lean_closure_set(v___f_3660_, 1, v_s_3659_);
    return v___f_3660_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(
    mut v_00_u03c1_3661_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3662_: *mut crate::leanh::LeanObject,
    mut v_inst_3663_: *mut crate::leanh::LeanObject,
    mut v_pat_3664_: *mut crate::leanh::LeanObject,
    mut v_inst_3665_: *mut crate::leanh::LeanObject,
    mut v_s_3666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(
        v_00_u03c1_3661_,
        v_00_u03c3_3662_,
        v_inst_3663_,
        v_pat_3664_,
        v_inst_3665_,
        v_s_3666_,
    );
    crate::leanh::lean_dec(v_inst_3665_);
    crate::leanh::lean_dec(v_pat_3664_);
    return v_res_3667_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(
    mut v_x_3668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3668_) == 0 {
        let mut v_searcher_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_searcher_3669_ = crate::leanh::lean_ctor_get(v_x_3668_, 1);
        crate::leanh::lean_inc(v_searcher_3669_);
        v___x_3670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3670_, 0, v_searcher_3669_);
        return v___x_3670_;
    } else {
        let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3671_ = crate::leanh::lean_box(0);
        return v___x_3671_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(
    mut v_x_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(
            v_x_3672_,
        );
    crate::leanh::lean_dec(v_x_3672_);
    return v_res_3673_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(
    mut v_00_u03c1_3674_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3675_: *mut crate::leanh::LeanObject,
    mut v_pat_3676_: *mut crate::leanh::LeanObject,
    mut v_inst_3677_: *mut crate::leanh::LeanObject,
    mut v_s_3678_: *mut crate::leanh::LeanObject,
    mut v_x_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(
            v_x_3679_,
        );
    return v___x_3680_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(
    mut v_00_u03c1_3681_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3682_: *mut crate::leanh::LeanObject,
    mut v_pat_3683_: *mut crate::leanh::LeanObject,
    mut v_inst_3684_: *mut crate::leanh::LeanObject,
    mut v_s_3685_: *mut crate::leanh::LeanObject,
    mut v_x_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3687_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(
        v_00_u03c1_3681_,
        v_00_u03c3_3682_,
        v_pat_3683_,
        v_inst_3684_,
        v_s_3685_,
        v_x_3686_,
    );
    crate::leanh::lean_dec(v_x_3686_);
    crate::leanh::lean_dec_ref(v_s_3685_);
    crate::leanh::lean_dec(v_inst_3684_);
    crate::leanh::lean_dec(v_pat_3683_);
    return v_res_3687_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(
    mut v_x_3688_: *mut crate::leanh::LeanObject,
    mut v_h__1_3689_: *mut crate::leanh::LeanObject,
    mut v_h__2_3690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3688_) == 0 {
        let mut v_currPos_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3690_);
        v_currPos_3691_ = crate::leanh::lean_ctor_get(v_x_3688_, 0);
        crate::leanh::lean_inc(v_currPos_3691_);
        v_searcher_3692_ = crate::leanh::lean_ctor_get(v_x_3688_, 1);
        crate::leanh::lean_inc(v_searcher_3692_);
        crate::leanh::lean_dec_ref_known(v_x_3688_, 2);
        v___x_3693_ = crate::leanh::lean_apply_2(v_h__1_3689_, v_currPos_3691_, v_searcher_3692_);
        return v___x_3693_;
    } else {
        let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3689_);
        v___x_3694_ = crate::leanh::lean_box(0);
        v___x_3695_ = crate::leanh::lean_apply_1(v_h__2_3690_, v___x_3694_);
        return v___x_3695_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(
    mut v_00_u03c1_3696_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3697_: *mut crate::leanh::LeanObject,
    mut v_pat_3698_: *mut crate::leanh::LeanObject,
    mut v_inst_3699_: *mut crate::leanh::LeanObject,
    mut v_s_3700_: *mut crate::leanh::LeanObject,
    mut v_motive_3701_: *mut crate::leanh::LeanObject,
    mut v_x_3702_: *mut crate::leanh::LeanObject,
    mut v_h__1_3703_: *mut crate::leanh::LeanObject,
    mut v_h__2_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3702_) == 0 {
        let mut v_currPos_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3704_);
        v_currPos_3705_ = crate::leanh::lean_ctor_get(v_x_3702_, 0);
        crate::leanh::lean_inc(v_currPos_3705_);
        v_searcher_3706_ = crate::leanh::lean_ctor_get(v_x_3702_, 1);
        crate::leanh::lean_inc(v_searcher_3706_);
        crate::leanh::lean_dec_ref_known(v_x_3702_, 2);
        v___x_3707_ = crate::leanh::lean_apply_2(v_h__1_3703_, v_currPos_3705_, v_searcher_3706_);
        return v___x_3707_;
    } else {
        let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3703_);
        v___x_3708_ = crate::leanh::lean_box(0);
        v___x_3709_ = crate::leanh::lean_apply_1(v_h__2_3704_, v___x_3708_);
        return v___x_3709_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(
    mut v_00_u03c1_3710_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3711_: *mut crate::leanh::LeanObject,
    mut v_pat_3712_: *mut crate::leanh::LeanObject,
    mut v_inst_3713_: *mut crate::leanh::LeanObject,
    mut v_s_3714_: *mut crate::leanh::LeanObject,
    mut v_motive_3715_: *mut crate::leanh::LeanObject,
    mut v_x_3716_: *mut crate::leanh::LeanObject,
    mut v_h__1_3717_: *mut crate::leanh::LeanObject,
    mut v_h__2_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3719_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_3710_, v_00_u03c3_3711_, v_pat_3712_, v_inst_3713_, v_s_3714_, v_motive_3715_, v_x_3716_, v_h__1_3717_, v_h__2_3718_);
    crate::leanh::lean_dec_ref(v_s_3714_);
    crate::leanh::lean_dec(v_inst_3713_);
    crate::leanh::lean_dec(v_pat_3712_);
    return v_res_3719_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(
    mut v_x_3720_: *mut crate::leanh::LeanObject,
    mut v_h__1_3721_: *mut crate::leanh::LeanObject,
    mut v_h__2_3722_: *mut crate::leanh::LeanObject,
    mut v_h__3_3723_: *mut crate::leanh::LeanObject,
    mut v_h__4_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3720_) {
        0 => {
            let mut v_out_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_3724_);
            crate::leanh::lean_dec(v_h__3_3723_);
            v_out_3725_ = crate::leanh::lean_ctor_get(v_x_3720_, 1);
            crate::leanh::lean_inc(v_out_3725_);
            if crate::leanh::lean_obj_tag(v_out_3725_) == 0 {
                let mut v_it_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__1_3721_);
                v_it_3726_ = crate::leanh::lean_ctor_get(v_x_3720_, 0);
                crate::leanh::lean_inc(v_it_3726_);
                crate::leanh::lean_dec_ref_known(v_x_3720_, 2);
                v_startPos_3727_ = crate::leanh::lean_ctor_get(v_out_3725_, 0);
                crate::leanh::lean_inc(v_startPos_3727_);
                v_endPos_3728_ = crate::leanh::lean_ctor_get(v_out_3725_, 1);
                crate::leanh::lean_inc(v_endPos_3728_);
                crate::leanh::lean_dec_ref_known(v_out_3725_, 2);
                v___x_3729_ = crate::leanh::lean_apply_5(
                    v_h__2_3722_,
                    v_it_3726_,
                    v_startPos_3727_,
                    v_endPos_3728_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3729_;
            } else {
                let mut v_it_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_3722_);
                v_it_3730_ = crate::leanh::lean_ctor_get(v_x_3720_, 0);
                crate::leanh::lean_inc(v_it_3730_);
                crate::leanh::lean_dec_ref_known(v_x_3720_, 2);
                v_startPos_3731_ = crate::leanh::lean_ctor_get(v_out_3725_, 0);
                crate::leanh::lean_inc(v_startPos_3731_);
                v_endPos_3732_ = crate::leanh::lean_ctor_get(v_out_3725_, 1);
                crate::leanh::lean_inc(v_endPos_3732_);
                crate::leanh::lean_dec_ref_known(v_out_3725_, 2);
                v___x_3733_ = crate::leanh::lean_apply_5(
                    v_h__1_3721_,
                    v_it_3730_,
                    v_startPos_3731_,
                    v_endPos_3732_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3733_;
            }
        }
        1 => {
            let mut v_it_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_3724_);
            crate::leanh::lean_dec(v_h__2_3722_);
            crate::leanh::lean_dec(v_h__1_3721_);
            v_it_3734_ = crate::leanh::lean_ctor_get(v_x_3720_, 0);
            crate::leanh::lean_inc(v_it_3734_);
            crate::leanh::lean_dec_ref_known(v_x_3720_, 1);
            v___x_3735_ = crate::leanh::lean_apply_3(
                v_h__3_3723_,
                v_it_3734_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3735_;
        }
        _ => {
            let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3723_);
            crate::leanh::lean_dec(v_h__2_3722_);
            crate::leanh::lean_dec(v_h__1_3721_);
            v___x_3736_ = crate::leanh::lean_apply_2(
                v_h__4_3724_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3736_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(
    mut v_00_u03c3_3737_: *mut crate::leanh::LeanObject,
    mut v_inst_3738_: *mut crate::leanh::LeanObject,
    mut v_s_3739_: *mut crate::leanh::LeanObject,
    mut v_searcher_3740_: *mut crate::leanh::LeanObject,
    mut v_motive_3741_: *mut crate::leanh::LeanObject,
    mut v_x_3742_: *mut crate::leanh::LeanObject,
    mut v_h__1_3743_: *mut crate::leanh::LeanObject,
    mut v_h__2_3744_: *mut crate::leanh::LeanObject,
    mut v_h__3_3745_: *mut crate::leanh::LeanObject,
    mut v_h__4_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3742_) {
        0 => {
            let mut v_out_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_3746_);
            crate::leanh::lean_dec(v_h__3_3745_);
            v_out_3747_ = crate::leanh::lean_ctor_get(v_x_3742_, 1);
            crate::leanh::lean_inc(v_out_3747_);
            if crate::leanh::lean_obj_tag(v_out_3747_) == 0 {
                let mut v_it_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__1_3743_);
                v_it_3748_ = crate::leanh::lean_ctor_get(v_x_3742_, 0);
                crate::leanh::lean_inc(v_it_3748_);
                crate::leanh::lean_dec_ref_known(v_x_3742_, 2);
                v_startPos_3749_ = crate::leanh::lean_ctor_get(v_out_3747_, 0);
                crate::leanh::lean_inc(v_startPos_3749_);
                v_endPos_3750_ = crate::leanh::lean_ctor_get(v_out_3747_, 1);
                crate::leanh::lean_inc(v_endPos_3750_);
                crate::leanh::lean_dec_ref_known(v_out_3747_, 2);
                v___x_3751_ = crate::leanh::lean_apply_5(
                    v_h__2_3744_,
                    v_it_3748_,
                    v_startPos_3749_,
                    v_endPos_3750_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3751_;
            } else {
                let mut v_it_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_3744_);
                v_it_3752_ = crate::leanh::lean_ctor_get(v_x_3742_, 0);
                crate::leanh::lean_inc(v_it_3752_);
                crate::leanh::lean_dec_ref_known(v_x_3742_, 2);
                v_startPos_3753_ = crate::leanh::lean_ctor_get(v_out_3747_, 0);
                crate::leanh::lean_inc(v_startPos_3753_);
                v_endPos_3754_ = crate::leanh::lean_ctor_get(v_out_3747_, 1);
                crate::leanh::lean_inc(v_endPos_3754_);
                crate::leanh::lean_dec_ref_known(v_out_3747_, 2);
                v___x_3755_ = crate::leanh::lean_apply_5(
                    v_h__1_3743_,
                    v_it_3752_,
                    v_startPos_3753_,
                    v_endPos_3754_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3755_;
            }
        }
        1 => {
            let mut v_it_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_3746_);
            crate::leanh::lean_dec(v_h__2_3744_);
            crate::leanh::lean_dec(v_h__1_3743_);
            v_it_3756_ = crate::leanh::lean_ctor_get(v_x_3742_, 0);
            crate::leanh::lean_inc(v_it_3756_);
            crate::leanh::lean_dec_ref_known(v_x_3742_, 1);
            v___x_3757_ = crate::leanh::lean_apply_3(
                v_h__3_3745_,
                v_it_3756_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3757_;
        }
        _ => {
            let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3745_);
            crate::leanh::lean_dec(v_h__2_3744_);
            crate::leanh::lean_dec(v_h__1_3743_);
            v___x_3758_ = crate::leanh::lean_apply_2(
                v_h__4_3746_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3758_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(
    mut v_00_u03c3_3759_: *mut crate::leanh::LeanObject,
    mut v_inst_3760_: *mut crate::leanh::LeanObject,
    mut v_s_3761_: *mut crate::leanh::LeanObject,
    mut v_searcher_3762_: *mut crate::leanh::LeanObject,
    mut v_motive_3763_: *mut crate::leanh::LeanObject,
    mut v_x_3764_: *mut crate::leanh::LeanObject,
    mut v_h__1_3765_: *mut crate::leanh::LeanObject,
    mut v_h__2_3766_: *mut crate::leanh::LeanObject,
    mut v_h__3_3767_: *mut crate::leanh::LeanObject,
    mut v_h__4_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3769_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_3759_, v_inst_3760_, v_s_3761_, v_searcher_3762_, v_motive_3763_, v_x_3764_, v_h__1_3765_, v_h__2_3766_, v_h__3_3767_, v_h__4_3768_);
    crate::leanh::lean_dec(v_searcher_3762_);
    crate::leanh::lean_dec_ref(v_s_3761_);
    crate::leanh::lean_dec(v_inst_3760_);
    return v_res_3769_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(
    mut v_x_3770_: *mut crate::leanh::LeanObject,
    mut v_x_3771_: *mut crate::leanh::LeanObject,
    mut v_h__1_3772_: *mut crate::leanh::LeanObject,
    mut v_h__2_3773_: *mut crate::leanh::LeanObject,
    mut v_h__3_3774_: *mut crate::leanh::LeanObject,
    mut v_h__4_3775_: *mut crate::leanh::LeanObject,
    mut v_h__5_3776_: *mut crate::leanh::LeanObject,
    mut v_h__6_3777_: *mut crate::leanh::LeanObject,
    mut v_h__7_3778_: *mut crate::leanh::LeanObject,
    mut v_h__8_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3770_) == 0 {
        crate::leanh::lean_dec(v_h__8_3779_);
        crate::leanh::lean_dec(v_h__7_3778_);
        crate::leanh::lean_dec(v_h__6_3777_);
        match crate::leanh::lean_obj_tag(v_x_3771_) {
            0 => {
                let mut v_it_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_3776_);
                crate::leanh::lean_dec(v_h__4_3775_);
                crate::leanh::lean_dec(v_h__3_3774_);
                v_it_3780_ = crate::leanh::lean_ctor_get(v_x_3771_, 0);
                if crate::leanh::lean_obj_tag(v_it_3780_) == 0 {
                    let mut v_currPos_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_3780_);
                    crate::leanh::lean_dec(v_h__2_3773_);
                    v_currPos_3781_ = crate::leanh::lean_ctor_get(v_x_3770_, 0);
                    crate::leanh::lean_inc(v_currPos_3781_);
                    v_searcher_3782_ = crate::leanh::lean_ctor_get(v_x_3770_, 1);
                    crate::leanh::lean_inc(v_searcher_3782_);
                    crate::leanh::lean_dec_ref_known(v_x_3770_, 2);
                    v_out_3783_ = crate::leanh::lean_ctor_get(v_x_3771_, 1);
                    crate::leanh::lean_inc(v_out_3783_);
                    crate::leanh::lean_dec_ref_known(v_x_3771_, 2);
                    v_currPos_3784_ = crate::leanh::lean_ctor_get(v_it_3780_, 0);
                    crate::leanh::lean_inc(v_currPos_3784_);
                    v_searcher_3785_ = crate::leanh::lean_ctor_get(v_it_3780_, 1);
                    crate::leanh::lean_inc(v_searcher_3785_);
                    crate::leanh::lean_dec_ref_known(v_it_3780_, 2);
                    v___x_3786_ = crate::leanh::lean_apply_5(
                        v_h__1_3772_,
                        v_currPos_3781_,
                        v_searcher_3782_,
                        v_currPos_3784_,
                        v_searcher_3785_,
                        v_out_3783_,
                    );
                    return v___x_3786_;
                } else {
                    let mut v_currPos_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_3772_);
                    v_currPos_3787_ = crate::leanh::lean_ctor_get(v_x_3770_, 0);
                    crate::leanh::lean_inc(v_currPos_3787_);
                    v_searcher_3788_ = crate::leanh::lean_ctor_get(v_x_3770_, 1);
                    crate::leanh::lean_inc(v_searcher_3788_);
                    crate::leanh::lean_dec_ref_known(v_x_3770_, 2);
                    v_out_3789_ = crate::leanh::lean_ctor_get(v_x_3771_, 1);
                    crate::leanh::lean_inc(v_out_3789_);
                    crate::leanh::lean_dec_ref_known(v_x_3771_, 2);
                    v___x_3790_ = crate::leanh::lean_apply_3(
                        v_h__2_3773_,
                        v_currPos_3787_,
                        v_searcher_3788_,
                        v_out_3789_,
                    );
                    return v___x_3790_;
                }
            }
            1 => {
                let mut v_it_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_3776_);
                crate::leanh::lean_dec(v_h__2_3773_);
                crate::leanh::lean_dec(v_h__1_3772_);
                v_it_3791_ = crate::leanh::lean_ctor_get(v_x_3771_, 0);
                crate::leanh::lean_inc(v_it_3791_);
                crate::leanh::lean_dec_ref_known(v_x_3771_, 1);
                if crate::leanh::lean_obj_tag(v_it_3791_) == 0 {
                    let mut v_currPos_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_3775_);
                    v_currPos_3792_ = crate::leanh::lean_ctor_get(v_x_3770_, 0);
                    crate::leanh::lean_inc(v_currPos_3792_);
                    v_searcher_3793_ = crate::leanh::lean_ctor_get(v_x_3770_, 1);
                    crate::leanh::lean_inc(v_searcher_3793_);
                    crate::leanh::lean_dec_ref_known(v_x_3770_, 2);
                    v_currPos_3794_ = crate::leanh::lean_ctor_get(v_it_3791_, 0);
                    crate::leanh::lean_inc(v_currPos_3794_);
                    v_searcher_3795_ = crate::leanh::lean_ctor_get(v_it_3791_, 1);
                    crate::leanh::lean_inc(v_searcher_3795_);
                    crate::leanh::lean_dec_ref_known(v_it_3791_, 2);
                    v___x_3796_ = crate::leanh::lean_apply_4(
                        v_h__3_3774_,
                        v_currPos_3792_,
                        v_searcher_3793_,
                        v_currPos_3794_,
                        v_searcher_3795_,
                    );
                    return v___x_3796_;
                } else {
                    let mut v_currPos_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_3774_);
                    v_currPos_3797_ = crate::leanh::lean_ctor_get(v_x_3770_, 0);
                    crate::leanh::lean_inc(v_currPos_3797_);
                    v_searcher_3798_ = crate::leanh::lean_ctor_get(v_x_3770_, 1);
                    crate::leanh::lean_inc(v_searcher_3798_);
                    crate::leanh::lean_dec_ref_known(v_x_3770_, 2);
                    v___x_3799_ =
                        crate::leanh::lean_apply_2(v_h__4_3775_, v_currPos_3797_, v_searcher_3798_);
                    return v___x_3799_;
                }
            }
            _ => {
                let mut v_currPos_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_3775_);
                crate::leanh::lean_dec(v_h__3_3774_);
                crate::leanh::lean_dec(v_h__2_3773_);
                crate::leanh::lean_dec(v_h__1_3772_);
                v_currPos_3800_ = crate::leanh::lean_ctor_get(v_x_3770_, 0);
                crate::leanh::lean_inc(v_currPos_3800_);
                v_searcher_3801_ = crate::leanh::lean_ctor_get(v_x_3770_, 1);
                crate::leanh::lean_inc(v_searcher_3801_);
                crate::leanh::lean_dec_ref_known(v_x_3770_, 2);
                v___x_3802_ =
                    crate::leanh::lean_apply_2(v_h__5_3776_, v_currPos_3800_, v_searcher_3801_);
                return v___x_3802_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_3776_);
        crate::leanh::lean_dec(v_h__4_3775_);
        crate::leanh::lean_dec(v_h__3_3774_);
        crate::leanh::lean_dec(v_h__2_3773_);
        crate::leanh::lean_dec(v_h__1_3772_);
        match crate::leanh::lean_obj_tag(v_x_3771_) {
            0 => {
                let mut v_it_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_3779_);
                crate::leanh::lean_dec(v_h__7_3778_);
                v_it_3803_ = crate::leanh::lean_ctor_get(v_x_3771_, 0);
                crate::leanh::lean_inc(v_it_3803_);
                v_out_3804_ = crate::leanh::lean_ctor_get(v_x_3771_, 1);
                crate::leanh::lean_inc(v_out_3804_);
                crate::leanh::lean_dec_ref_known(v_x_3771_, 2);
                v___x_3805_ = crate::leanh::lean_apply_2(v_h__6_3777_, v_it_3803_, v_out_3804_);
                return v___x_3805_;
            }
            1 => {
                let mut v_it_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_3779_);
                crate::leanh::lean_dec(v_h__6_3777_);
                v_it_3806_ = crate::leanh::lean_ctor_get(v_x_3771_, 0);
                crate::leanh::lean_inc(v_it_3806_);
                crate::leanh::lean_dec_ref_known(v_x_3771_, 1);
                v___x_3807_ = crate::leanh::lean_apply_1(v_h__7_3778_, v_it_3806_);
                return v___x_3807_;
            }
            _ => {
                let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_3778_);
                crate::leanh::lean_dec(v_h__6_3777_);
                v___x_3808_ = crate::leanh::lean_box(0);
                v___x_3809_ = crate::leanh::lean_apply_1(v_h__8_3779_, v___x_3808_);
                return v___x_3809_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(
    mut v_00_u03c1_3810_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3811_: *mut crate::leanh::LeanObject,
    mut v_pat_3812_: *mut crate::leanh::LeanObject,
    mut v_inst_3813_: *mut crate::leanh::LeanObject,
    mut v_s_3814_: *mut crate::leanh::LeanObject,
    mut v_motive_3815_: *mut crate::leanh::LeanObject,
    mut v_x_3816_: *mut crate::leanh::LeanObject,
    mut v_x_3817_: *mut crate::leanh::LeanObject,
    mut v_h__1_3818_: *mut crate::leanh::LeanObject,
    mut v_h__2_3819_: *mut crate::leanh::LeanObject,
    mut v_h__3_3820_: *mut crate::leanh::LeanObject,
    mut v_h__4_3821_: *mut crate::leanh::LeanObject,
    mut v_h__5_3822_: *mut crate::leanh::LeanObject,
    mut v_h__6_3823_: *mut crate::leanh::LeanObject,
    mut v_h__7_3824_: *mut crate::leanh::LeanObject,
    mut v_h__8_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3816_) == 0 {
        crate::leanh::lean_dec(v_h__8_3825_);
        crate::leanh::lean_dec(v_h__7_3824_);
        crate::leanh::lean_dec(v_h__6_3823_);
        match crate::leanh::lean_obj_tag(v_x_3817_) {
            0 => {
                let mut v_it_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_3822_);
                crate::leanh::lean_dec(v_h__4_3821_);
                crate::leanh::lean_dec(v_h__3_3820_);
                v_it_3826_ = crate::leanh::lean_ctor_get(v_x_3817_, 0);
                if crate::leanh::lean_obj_tag(v_it_3826_) == 0 {
                    let mut v_currPos_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_3826_);
                    crate::leanh::lean_dec(v_h__2_3819_);
                    v_currPos_3827_ = crate::leanh::lean_ctor_get(v_x_3816_, 0);
                    crate::leanh::lean_inc(v_currPos_3827_);
                    v_searcher_3828_ = crate::leanh::lean_ctor_get(v_x_3816_, 1);
                    crate::leanh::lean_inc(v_searcher_3828_);
                    crate::leanh::lean_dec_ref_known(v_x_3816_, 2);
                    v_out_3829_ = crate::leanh::lean_ctor_get(v_x_3817_, 1);
                    crate::leanh::lean_inc(v_out_3829_);
                    crate::leanh::lean_dec_ref_known(v_x_3817_, 2);
                    v_currPos_3830_ = crate::leanh::lean_ctor_get(v_it_3826_, 0);
                    crate::leanh::lean_inc(v_currPos_3830_);
                    v_searcher_3831_ = crate::leanh::lean_ctor_get(v_it_3826_, 1);
                    crate::leanh::lean_inc(v_searcher_3831_);
                    crate::leanh::lean_dec_ref_known(v_it_3826_, 2);
                    v___x_3832_ = crate::leanh::lean_apply_5(
                        v_h__1_3818_,
                        v_currPos_3827_,
                        v_searcher_3828_,
                        v_currPos_3830_,
                        v_searcher_3831_,
                        v_out_3829_,
                    );
                    return v___x_3832_;
                } else {
                    let mut v_currPos_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_3818_);
                    v_currPos_3833_ = crate::leanh::lean_ctor_get(v_x_3816_, 0);
                    crate::leanh::lean_inc(v_currPos_3833_);
                    v_searcher_3834_ = crate::leanh::lean_ctor_get(v_x_3816_, 1);
                    crate::leanh::lean_inc(v_searcher_3834_);
                    crate::leanh::lean_dec_ref_known(v_x_3816_, 2);
                    v_out_3835_ = crate::leanh::lean_ctor_get(v_x_3817_, 1);
                    crate::leanh::lean_inc(v_out_3835_);
                    crate::leanh::lean_dec_ref_known(v_x_3817_, 2);
                    v___x_3836_ = crate::leanh::lean_apply_3(
                        v_h__2_3819_,
                        v_currPos_3833_,
                        v_searcher_3834_,
                        v_out_3835_,
                    );
                    return v___x_3836_;
                }
            }
            1 => {
                let mut v_it_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_3822_);
                crate::leanh::lean_dec(v_h__2_3819_);
                crate::leanh::lean_dec(v_h__1_3818_);
                v_it_3837_ = crate::leanh::lean_ctor_get(v_x_3817_, 0);
                crate::leanh::lean_inc(v_it_3837_);
                crate::leanh::lean_dec_ref_known(v_x_3817_, 1);
                if crate::leanh::lean_obj_tag(v_it_3837_) == 0 {
                    let mut v_currPos_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_3821_);
                    v_currPos_3838_ = crate::leanh::lean_ctor_get(v_x_3816_, 0);
                    crate::leanh::lean_inc(v_currPos_3838_);
                    v_searcher_3839_ = crate::leanh::lean_ctor_get(v_x_3816_, 1);
                    crate::leanh::lean_inc(v_searcher_3839_);
                    crate::leanh::lean_dec_ref_known(v_x_3816_, 2);
                    v_currPos_3840_ = crate::leanh::lean_ctor_get(v_it_3837_, 0);
                    crate::leanh::lean_inc(v_currPos_3840_);
                    v_searcher_3841_ = crate::leanh::lean_ctor_get(v_it_3837_, 1);
                    crate::leanh::lean_inc(v_searcher_3841_);
                    crate::leanh::lean_dec_ref_known(v_it_3837_, 2);
                    v___x_3842_ = crate::leanh::lean_apply_4(
                        v_h__3_3820_,
                        v_currPos_3838_,
                        v_searcher_3839_,
                        v_currPos_3840_,
                        v_searcher_3841_,
                    );
                    return v___x_3842_;
                } else {
                    let mut v_currPos_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_3820_);
                    v_currPos_3843_ = crate::leanh::lean_ctor_get(v_x_3816_, 0);
                    crate::leanh::lean_inc(v_currPos_3843_);
                    v_searcher_3844_ = crate::leanh::lean_ctor_get(v_x_3816_, 1);
                    crate::leanh::lean_inc(v_searcher_3844_);
                    crate::leanh::lean_dec_ref_known(v_x_3816_, 2);
                    v___x_3845_ =
                        crate::leanh::lean_apply_2(v_h__4_3821_, v_currPos_3843_, v_searcher_3844_);
                    return v___x_3845_;
                }
            }
            _ => {
                let mut v_currPos_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_3821_);
                crate::leanh::lean_dec(v_h__3_3820_);
                crate::leanh::lean_dec(v_h__2_3819_);
                crate::leanh::lean_dec(v_h__1_3818_);
                v_currPos_3846_ = crate::leanh::lean_ctor_get(v_x_3816_, 0);
                crate::leanh::lean_inc(v_currPos_3846_);
                v_searcher_3847_ = crate::leanh::lean_ctor_get(v_x_3816_, 1);
                crate::leanh::lean_inc(v_searcher_3847_);
                crate::leanh::lean_dec_ref_known(v_x_3816_, 2);
                v___x_3848_ =
                    crate::leanh::lean_apply_2(v_h__5_3822_, v_currPos_3846_, v_searcher_3847_);
                return v___x_3848_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_3822_);
        crate::leanh::lean_dec(v_h__4_3821_);
        crate::leanh::lean_dec(v_h__3_3820_);
        crate::leanh::lean_dec(v_h__2_3819_);
        crate::leanh::lean_dec(v_h__1_3818_);
        match crate::leanh::lean_obj_tag(v_x_3817_) {
            0 => {
                let mut v_it_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_3825_);
                crate::leanh::lean_dec(v_h__7_3824_);
                v_it_3849_ = crate::leanh::lean_ctor_get(v_x_3817_, 0);
                crate::leanh::lean_inc(v_it_3849_);
                v_out_3850_ = crate::leanh::lean_ctor_get(v_x_3817_, 1);
                crate::leanh::lean_inc(v_out_3850_);
                crate::leanh::lean_dec_ref_known(v_x_3817_, 2);
                v___x_3851_ = crate::leanh::lean_apply_2(v_h__6_3823_, v_it_3849_, v_out_3850_);
                return v___x_3851_;
            }
            1 => {
                let mut v_it_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_3825_);
                crate::leanh::lean_dec(v_h__6_3823_);
                v_it_3852_ = crate::leanh::lean_ctor_get(v_x_3817_, 0);
                crate::leanh::lean_inc(v_it_3852_);
                crate::leanh::lean_dec_ref_known(v_x_3817_, 1);
                v___x_3853_ = crate::leanh::lean_apply_1(v_h__7_3824_, v_it_3852_);
                return v___x_3853_;
            }
            _ => {
                let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_3824_);
                crate::leanh::lean_dec(v_h__6_3823_);
                v___x_3854_ = crate::leanh::lean_box(0);
                v___x_3855_ = crate::leanh::lean_apply_1(v_h__8_3825_, v___x_3854_);
                return v___x_3855_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(
    mut v_00_u03c1_3856_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3857_: *mut crate::leanh::LeanObject,
    mut v_pat_3858_: *mut crate::leanh::LeanObject,
    mut v_inst_3859_: *mut crate::leanh::LeanObject,
    mut v_s_3860_: *mut crate::leanh::LeanObject,
    mut v_motive_3861_: *mut crate::leanh::LeanObject,
    mut v_x_3862_: *mut crate::leanh::LeanObject,
    mut v_x_3863_: *mut crate::leanh::LeanObject,
    mut v_h__1_3864_: *mut crate::leanh::LeanObject,
    mut v_h__2_3865_: *mut crate::leanh::LeanObject,
    mut v_h__3_3866_: *mut crate::leanh::LeanObject,
    mut v_h__4_3867_: *mut crate::leanh::LeanObject,
    mut v_h__5_3868_: *mut crate::leanh::LeanObject,
    mut v_h__6_3869_: *mut crate::leanh::LeanObject,
    mut v_h__7_3870_: *mut crate::leanh::LeanObject,
    mut v_h__8_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_3856_, v_00_u03c3_3857_, v_pat_3858_, v_inst_3859_, v_s_3860_, v_motive_3861_, v_x_3862_, v_x_3863_, v_h__1_3864_, v_h__2_3865_, v_h__3_3866_, v_h__4_3867_, v_h__5_3868_, v_h__6_3869_, v_h__7_3870_, v_h__8_3871_);
    crate::leanh::lean_dec_ref(v_s_3860_);
    crate::leanh::lean_dec(v_inst_3859_);
    crate::leanh::lean_dec(v_pat_3858_);
    return v_res_3872_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(
    mut v_x_3873_: *mut crate::leanh::LeanObject,
    mut v_h__1_3874_: *mut crate::leanh::LeanObject,
    mut v_h__2_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3873_) == 0 {
        let mut v_currPos_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3875_);
        v_currPos_3876_ = crate::leanh::lean_ctor_get(v_x_3873_, 0);
        crate::leanh::lean_inc(v_currPos_3876_);
        v_searcher_3877_ = crate::leanh::lean_ctor_get(v_x_3873_, 1);
        crate::leanh::lean_inc(v_searcher_3877_);
        crate::leanh::lean_dec_ref_known(v_x_3873_, 2);
        v___x_3878_ = crate::leanh::lean_apply_2(v_h__1_3874_, v_currPos_3876_, v_searcher_3877_);
        return v___x_3878_;
    } else {
        let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3874_);
        v___x_3879_ = crate::leanh::lean_box(0);
        v___x_3880_ = crate::leanh::lean_apply_1(v_h__2_3875_, v___x_3879_);
        return v___x_3880_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(
    mut v_00_u03c1_3881_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3882_: *mut crate::leanh::LeanObject,
    mut v_pat_3883_: *mut crate::leanh::LeanObject,
    mut v_inst_3884_: *mut crate::leanh::LeanObject,
    mut v_s_3885_: *mut crate::leanh::LeanObject,
    mut v_motive_3886_: *mut crate::leanh::LeanObject,
    mut v_x_3887_: *mut crate::leanh::LeanObject,
    mut v_h__1_3888_: *mut crate::leanh::LeanObject,
    mut v_h__2_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3887_) == 0 {
        let mut v_currPos_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3889_);
        v_currPos_3890_ = crate::leanh::lean_ctor_get(v_x_3887_, 0);
        crate::leanh::lean_inc(v_currPos_3890_);
        v_searcher_3891_ = crate::leanh::lean_ctor_get(v_x_3887_, 1);
        crate::leanh::lean_inc(v_searcher_3891_);
        crate::leanh::lean_dec_ref_known(v_x_3887_, 2);
        v___x_3892_ = crate::leanh::lean_apply_2(v_h__1_3888_, v_currPos_3890_, v_searcher_3891_);
        return v___x_3892_;
    } else {
        let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3888_);
        v___x_3893_ = crate::leanh::lean_box(0);
        v___x_3894_ = crate::leanh::lean_apply_1(v_h__2_3889_, v___x_3893_);
        return v___x_3894_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(
    mut v_00_u03c1_3895_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3896_: *mut crate::leanh::LeanObject,
    mut v_pat_3897_: *mut crate::leanh::LeanObject,
    mut v_inst_3898_: *mut crate::leanh::LeanObject,
    mut v_s_3899_: *mut crate::leanh::LeanObject,
    mut v_motive_3900_: *mut crate::leanh::LeanObject,
    mut v_x_3901_: *mut crate::leanh::LeanObject,
    mut v_h__1_3902_: *mut crate::leanh::LeanObject,
    mut v_h__2_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(
            v_00_u03c1_3895_,
            v_00_u03c3_3896_,
            v_pat_3897_,
            v_inst_3898_,
            v_s_3899_,
            v_motive_3900_,
            v_x_3901_,
            v_h__1_3902_,
            v_h__2_3903_,
        );
    crate::leanh::lean_dec_ref(v_s_3899_);
    crate::leanh::lean_dec(v_inst_3898_);
    crate::leanh::lean_dec(v_pat_3897_);
    return v_res_3904_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(
    mut v_00_u03c1_3905_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3906_: *mut crate::leanh::LeanObject,
    mut v_inst_3907_: *mut crate::leanh::LeanObject,
    mut v_pat_3908_: *mut crate::leanh::LeanObject,
    mut v_inst_3909_: *mut crate::leanh::LeanObject,
    mut v_s_3910_: *mut crate::leanh::LeanObject,
    mut v_inst_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = crate::leanh::lean_box(0);
    return v___x_3912_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(
    mut v_00_u03c1_3913_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3914_: *mut crate::leanh::LeanObject,
    mut v_inst_3915_: *mut crate::leanh::LeanObject,
    mut v_pat_3916_: *mut crate::leanh::LeanObject,
    mut v_inst_3917_: *mut crate::leanh::LeanObject,
    mut v_s_3918_: *mut crate::leanh::LeanObject,
    mut v_inst_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3920_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(
            v_00_u03c1_3913_,
            v_00_u03c3_3914_,
            v_inst_3915_,
            v_pat_3916_,
            v_inst_3917_,
            v_s_3918_,
            v_inst_3919_,
        );
    crate::leanh::lean_dec_ref(v_s_3918_);
    crate::leanh::lean_dec(v_inst_3917_);
    crate::leanh::lean_dec(v_pat_3916_);
    crate::leanh::lean_dec(v_inst_3915_);
    return v_res_3920_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(
    mut v_toPure_3921_: *mut crate::leanh::LeanObject,
    mut v_recur_3922_: *mut crate::leanh::LeanObject,
    mut v_it_3923_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_3924_) == 0 {
        let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_3923_);
        crate::leanh::lean_dec(v_recur_3922_);
        v_a_3925_ = crate::leanh::lean_ctor_get(v_____do__lift_3924_, 0);
        crate::leanh::lean_inc(v_a_3925_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_3924_, 1);
        v___x_3926_ =
            crate::leanh::lean_apply_2(v_toPure_3921_, crate::leanh::lean_box(0), v_a_3925_);
        return v___x_3926_;
    } else {
        let mut v_a_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_3921_);
        v_a_3927_ = crate::leanh::lean_ctor_get(v_____do__lift_3924_, 0);
        crate::leanh::lean_inc(v_a_3927_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_3924_, 1);
        v___x_3928_ = crate::leanh::lean_apply_4(
            v_recur_3922_,
            v_it_3923_,
            v_a_3927_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_3928_;
    }
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(
    mut v_toPure_3929_: *mut crate::leanh::LeanObject,
    mut v_recur_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v_acc_3932_: *mut crate::leanh::LeanObject,
    mut v_toBind_3933_: *mut crate::leanh::LeanObject,
    mut v_s_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_3934_) {
        0 => {
            let mut v_it_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_3935_ = crate::leanh::lean_ctor_get(v_s_3934_, 0);
            crate::leanh::lean_inc(v_it_3935_);
            v_out_3936_ = crate::leanh::lean_ctor_get(v_s_3934_, 1);
            crate::leanh::lean_inc(v_out_3936_);
            crate::leanh::lean_dec_ref_known(v_s_3934_, 2);
            v___f_3937_ = crate::leanh::lean_alloc_closure(
                l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_3937_, 0, v_toPure_3929_);
            crate::leanh::lean_closure_set(v___f_3937_, 1, v_recur_3930_);
            crate::leanh::lean_closure_set(v___f_3937_, 2, v_it_3935_);
            v___x_3938_ = crate::leanh::lean_apply_3(
                v___y_3931_,
                v_out_3936_,
                crate::leanh::lean_box(0),
                v_acc_3932_,
            );
            v___x_3939_ = crate::leanh::lean_apply_4(
                v_toBind_3933_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_3938_,
                v___f_3937_,
            );
            return v___x_3939_;
        }
        1 => {
            let mut v_it_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_3933_);
            crate::leanh::lean_dec(v___y_3931_);
            crate::leanh::lean_dec(v_toPure_3929_);
            v_it_3940_ = crate::leanh::lean_ctor_get(v_s_3934_, 0);
            crate::leanh::lean_inc(v_it_3940_);
            crate::leanh::lean_dec_ref_known(v_s_3934_, 1);
            v___x_3941_ = crate::leanh::lean_apply_4(
                v_recur_3930_,
                v_it_3940_,
                v_acc_3932_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3941_;
        }
        _ => {
            let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_3933_);
            crate::leanh::lean_dec(v___y_3931_);
            crate::leanh::lean_dec(v_recur_3930_);
            v___x_3942_ =
                crate::leanh::lean_apply_2(v_toPure_3929_, crate::leanh::lean_box(0), v_acc_3932_);
            return v___x_3942_;
        }
    }
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(
    mut v_toPure_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
    mut v_toBind_3945_: *mut crate::leanh::LeanObject,
    mut v_inst_3946_: *mut crate::leanh::LeanObject,
    mut v_s_3947_: *mut crate::leanh::LeanObject,
    mut v_lift_3948_: *mut crate::leanh::LeanObject,
    mut v_it_3949_: *mut crate::leanh::LeanObject,
    mut v_acc_3950_: *mut crate::leanh::LeanObject,
    mut v_hP_3951_: *mut crate::leanh::LeanObject,
    mut v_recur_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v_startPos_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3981_: u8 = 0;
    let mut v_unused_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3986_: u8 = 0;
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_startInclusive_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4002_: u8 = 0;
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3953_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_3953_, 0, v_toPure_3943_);
                crate::leanh::lean_closure_set(v___f_3953_, 1, v_recur_3952_);
                crate::leanh::lean_closure_set(v___f_3953_, 2, v___y_3944_);
                crate::leanh::lean_closure_set(v___f_3953_, 3, v_acc_3950_);
                crate::leanh::lean_closure_set(v___f_3953_, 4, v_toBind_3945_);
                if crate::leanh::lean_obj_tag(v_it_3949_) == 0 {
                    v_currPos_3954_ = crate::leanh::lean_ctor_get(v_it_3949_, 0);
                    v_searcher_3955_ = crate::leanh::lean_ctor_get(v_it_3949_, 1);
                    v_isSharedCheck_4002_ = (!crate::leanh::lean_is_exclusive(v_it_3949_)) as u8;
                    if v_isSharedCheck_4002_ == 0 {
                        v___x_3957_ = v_it_3949_;
                        v_isShared_3958_ = v_isSharedCheck_4002_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_3955_);
                        crate::leanh::lean_inc(v_currPos_3954_);
                        crate::leanh::lean_dec(v_it_3949_);
                        v___x_3957_ = crate::leanh::lean_box(0);
                        v_isShared_3958_ = v_isSharedCheck_4002_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_3947_);
                    crate::leanh::lean_dec(v_inst_3946_);
                    v___x_4003_ = crate::leanh::lean_box(2);
                    v___x_4004_ = crate::leanh::lean_apply_4(
                        v_lift_3948_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_3953_,
                        v___x_4003_,
                    );
                    return v___x_4004_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_3947_);
                v___x_3959_ = crate::leanh::lean_apply_2(v_inst_3946_, v_s_3947_, v_searcher_3955_);
                match crate::leanh::lean_obj_tag(v___x_3959_) {
                    0 => {
                        v_out_3960_ = crate::leanh::lean_ctor_get(v___x_3959_, 1);
                        crate::leanh::lean_inc(v_out_3960_);
                        if crate::leanh::lean_obj_tag(v_out_3960_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_3960_, 2);
                            crate::leanh::lean_dec_ref(v_s_3947_);
                            v_it_3961_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                            crate::leanh::lean_inc(v_it_3961_);
                            crate::leanh::lean_dec_ref_known(v___x_3959_, 2);
                            if v_isShared_3958_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3957_, 1, v_it_3961_);
                                v___x_3963_ = v___x_3957_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3966_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3966_,
                                    0,
                                    v_currPos_3954_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_it_3961_);
                                v___x_3963_ = v_reuseFailAlloc_3966_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_3967_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                            v_isSharedCheck_3981_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3959_)) as u8;
                            if v_isSharedCheck_3981_ == 0 {
                                v_unused_3982_ = crate::leanh::lean_ctor_get(v___x_3959_, 1);
                                crate::leanh::lean_dec(v_unused_3982_);
                                v___x_3969_ = v___x_3959_;
                                v_isShared_3970_ = v_isSharedCheck_3981_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_3967_);
                                crate::leanh::lean_dec(v___x_3959_);
                                v___x_3969_ = crate::leanh::lean_box(0);
                                v_isShared_3970_ = v_isSharedCheck_3981_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_3947_);
                        v_it_3983_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                        v_isSharedCheck_3994_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3959_)) as u8;
                        if v_isSharedCheck_3994_ == 0 {
                            v___x_3985_ = v___x_3959_;
                            v_isShared_3986_ = v_isSharedCheck_3994_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_3983_);
                            crate::leanh::lean_dec(v___x_3959_);
                            v___x_3985_ = crate::leanh::lean_box(0);
                            v_isShared_3986_ = v_isSharedCheck_3994_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_3957_);
                        v_startInclusive_3995_ = crate::leanh::lean_ctor_get(v_s_3947_, 1);
                        crate::leanh::lean_inc(v_startInclusive_3995_);
                        v_endExclusive_3996_ = crate::leanh::lean_ctor_get(v_s_3947_, 2);
                        crate::leanh::lean_inc(v_endExclusive_3996_);
                        crate::leanh::lean_dec_ref(v_s_3947_);
                        v___x_3997_ = lean_nat_sub(v_endExclusive_3996_, v_startInclusive_3995_);
                        crate::leanh::lean_dec(v_startInclusive_3995_);
                        crate::leanh::lean_dec(v_endExclusive_3996_);
                        v_slice_3998_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_slice_3998_, 0, v_currPos_3954_);
                        crate::leanh::lean_ctor_set(v_slice_3998_, 1, v___x_3997_);
                        v___x_3999_ = crate::leanh::lean_box(1);
                        v___x_4000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3999_);
                        crate::leanh::lean_ctor_set(v___x_4000_, 1, v_slice_3998_);
                        v___x_4001_ = crate::leanh::lean_apply_4(
                            v_lift_3948_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_3953_,
                            v___x_4000_,
                        );
                        return v___x_4001_;
                    }
                }
            }
            2 => {
                v___x_3964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3964_, 0, v___x_3963_);
                v___x_3965_ = crate::leanh::lean_apply_4(
                    v_lift_3948_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_3953_,
                    v___x_3964_,
                );
                return v___x_3965_;
            }
            3 => {
                v_startPos_3971_ = crate::leanh::lean_ctor_get(v_out_3960_, 0);
                crate::leanh::lean_inc(v_startPos_3971_);
                v_endPos_3972_ = crate::leanh::lean_ctor_get(v_out_3960_, 1);
                crate::leanh::lean_inc(v_endPos_3972_);
                crate::leanh::lean_dec_ref_known(v_out_3960_, 2);
                v_slice_3973_ =
                    l_String_Slice_subslice_x21(v_s_3947_, v_currPos_3954_, v_startPos_3971_);
                crate::leanh::lean_dec_ref(v_s_3947_);
                if v_isShared_3958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3957_, 1, v_it_3967_);
                    crate::leanh::lean_ctor_set(v___x_3957_, 0, v_endPos_3972_);
                    v_nextIt_3975_ = v___x_3957_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_endPos_3972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_it_3967_);
                    v_nextIt_3975_ = v_reuseFailAlloc_3980_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3970_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3969_, 1, v_slice_3973_);
                    crate::leanh::lean_ctor_set(v___x_3969_, 0, v_nextIt_3975_);
                    v___x_3977_ = v___x_3969_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_nextIt_3975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_slice_3973_);
                    v___x_3977_ = v_reuseFailAlloc_3979_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3978_ = crate::leanh::lean_apply_4(
                    v_lift_3948_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_3953_,
                    v___x_3977_,
                );
                return v___x_3978_;
            }
            6 => {
                if v_isShared_3958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3957_, 1, v_it_3983_);
                    v___x_3988_ = v___x_3957_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_currPos_3954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_it_3983_);
                    v___x_3988_ = v_reuseFailAlloc_3993_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3985_, 0, v___x_3988_);
                    v___x_3990_ = v___x_3985_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3988_);
                    v___x_3990_ = v_reuseFailAlloc_3992_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3991_ = crate::leanh::lean_apply_4(
                    v_lift_3948_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_3953_,
                    v___x_3990_,
                );
                return v___x_3991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(
    mut v_inst_4005_: *mut crate::leanh::LeanObject,
    mut v_inst_4006_: *mut crate::leanh::LeanObject,
    mut v_s_4007_: *mut crate::leanh::LeanObject,
    mut v_lift_4008_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4009_: *mut crate::leanh::LeanObject,
    mut v_Pl_4010_: *mut crate::leanh::LeanObject,
    mut v_it_4011_: *mut crate::leanh::LeanObject,
    mut v_init_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4014_ = crate::leanh::lean_ctor_get(v_inst_4005_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4014_);
    v_toBind_4015_ = crate::leanh::lean_ctor_get(v_inst_4005_, 1);
    crate::leanh::lean_inc(v_toBind_4015_);
    crate::leanh::lean_dec_ref(v_inst_4005_);
    v_toPure_4016_ = crate::leanh::lean_ctor_get(v_toApplicative_4014_, 1);
    crate::leanh::lean_inc(v_toPure_4016_);
    crate::leanh::lean_dec_ref(v_toApplicative_4014_);
    v___f_4017_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4017_, 0, v_toPure_4016_);
    crate::leanh::lean_closure_set(v___f_4017_, 1, v___y_4013_);
    crate::leanh::lean_closure_set(v___f_4017_, 2, v_toBind_4015_);
    crate::leanh::lean_closure_set(v___f_4017_, 3, v_inst_4006_);
    crate::leanh::lean_closure_set(v___f_4017_, 4, v_s_4007_);
    crate::leanh::lean_closure_set(v___f_4017_, 5, v_lift_4008_);
    v___x_4018_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_4017_,
        v_it_4011_,
        v_init_4012_,
        crate::leanh::lean_box(0),
    );
    return v___x_4018_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(
    mut v_inst_4019_: *mut crate::leanh::LeanObject,
    mut v_s_4020_: *mut crate::leanh::LeanObject,
    mut v_inst_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4022_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4022_, 0, v_inst_4021_);
    crate::leanh::lean_closure_set(v___f_4022_, 1, v_inst_4019_);
    crate::leanh::lean_closure_set(v___f_4022_, 2, v_s_4020_);
    return v___f_4022_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(
    mut v_00_u03c1_4023_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4024_: *mut crate::leanh::LeanObject,
    mut v_inst_4025_: *mut crate::leanh::LeanObject,
    mut v_pat_4026_: *mut crate::leanh::LeanObject,
    mut v_inst_4027_: *mut crate::leanh::LeanObject,
    mut v_n_4028_: *mut crate::leanh::LeanObject,
    mut v_s_4029_: *mut crate::leanh::LeanObject,
    mut v_inst_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4031_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4031_, 0, v_inst_4030_);
    crate::leanh::lean_closure_set(v___f_4031_, 1, v_inst_4025_);
    crate::leanh::lean_closure_set(v___f_4031_, 2, v_s_4029_);
    return v___f_4031_;
}
pub unsafe fn l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(
    mut v_00_u03c1_4032_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4033_: *mut crate::leanh::LeanObject,
    mut v_inst_4034_: *mut crate::leanh::LeanObject,
    mut v_pat_4035_: *mut crate::leanh::LeanObject,
    mut v_inst_4036_: *mut crate::leanh::LeanObject,
    mut v_n_4037_: *mut crate::leanh::LeanObject,
    mut v_s_4038_: *mut crate::leanh::LeanObject,
    mut v_inst_4039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4040_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(
        v_00_u03c1_4032_,
        v_00_u03c3_4033_,
        v_inst_4034_,
        v_pat_4035_,
        v_inst_4036_,
        v_n_4037_,
        v_s_4038_,
        v_inst_4039_,
    );
    crate::leanh::lean_dec(v_inst_4036_);
    crate::leanh::lean_dec(v_pat_4035_);
    return v_res_4040_;
}
pub unsafe fn l_String_Slice_splitToSubslice___redArg(
    mut v_s_4041_: *mut crate::leanh::LeanObject,
    mut v_inst_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4044_ = crate::leanh::lean_apply_1(v_inst_4042_, v_s_4041_);
    v___x_4045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4043_);
    crate::leanh::lean_ctor_set(v___x_4045_, 1, v___x_4044_);
    return v___x_4045_;
}
pub unsafe fn l_String_Slice_splitToSubslice(
    mut v_00_u03c1_4046_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4047_: *mut crate::leanh::LeanObject,
    mut v_s_4048_: *mut crate::leanh::LeanObject,
    mut v_pat_4049_: *mut crate::leanh::LeanObject,
    mut v_inst_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4051_ = l_String_Slice_splitToSubslice___redArg(v_s_4048_, v_inst_4050_);
    return v___x_4051_;
}
pub unsafe fn l_String_Slice_splitToSubslice___boxed(
    mut v_00_u03c1_4052_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4053_: *mut crate::leanh::LeanObject,
    mut v_s_4054_: *mut crate::leanh::LeanObject,
    mut v_pat_4055_: *mut crate::leanh::LeanObject,
    mut v_inst_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4057_ = l_String_Slice_splitToSubslice(
        v_00_u03c1_4052_,
        v_00_u03c3_4053_,
        v_s_4054_,
        v_pat_4055_,
        v_inst_4056_,
    );
    crate::leanh::lean_dec(v_pat_4055_);
    return v_res_4057_;
}
pub unsafe fn l_String_Slice_split___redArg(
    mut v_s_4058_: *mut crate::leanh::LeanObject,
    mut v_inst_4059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_String_Slice_splitToSubslice___redArg(v_s_4058_, v_inst_4059_);
    return v___x_4060_;
}
pub unsafe fn l_String_Slice_split(
    mut v_00_u03c1_4061_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4062_: *mut crate::leanh::LeanObject,
    mut v_inst_4063_: *mut crate::leanh::LeanObject,
    mut v_s_4064_: *mut crate::leanh::LeanObject,
    mut v_pat_4065_: *mut crate::leanh::LeanObject,
    mut v_inst_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_String_Slice_splitToSubslice___redArg(v_s_4064_, v_inst_4066_);
    return v___x_4067_;
}
pub unsafe fn l_String_Slice_split___boxed(
    mut v_00_u03c1_4068_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4069_: *mut crate::leanh::LeanObject,
    mut v_inst_4070_: *mut crate::leanh::LeanObject,
    mut v_s_4071_: *mut crate::leanh::LeanObject,
    mut v_pat_4072_: *mut crate::leanh::LeanObject,
    mut v_inst_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4074_ = l_String_Slice_split(
        v_00_u03c1_4068_,
        v_00_u03c3_4069_,
        v_inst_4070_,
        v_s_4071_,
        v_pat_4072_,
        v_inst_4073_,
    );
    crate::leanh::lean_dec(v_pat_4072_);
    crate::leanh::lean_dec(v_inst_4070_);
    return v_res_4074_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(
    mut v_x_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4075_) == 0 {
        let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4076_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4076_;
    } else {
        let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4077_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4077_;
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg___boxed(
    mut v_x_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4079_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_4078_);
    crate::leanh::lean_dec(v_x_4078_);
    return v_res_4079_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorIdx(
    mut v_00_u03c3_4080_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4081_: *mut crate::leanh::LeanObject,
    mut v_pat_4082_: *mut crate::leanh::LeanObject,
    mut v_s_4083_: *mut crate::leanh::LeanObject,
    mut v_inst_4084_: *mut crate::leanh::LeanObject,
    mut v_x_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_4085_);
    return v___x_4086_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorIdx___boxed(
    mut v_00_u03c3_4087_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4088_: *mut crate::leanh::LeanObject,
    mut v_pat_4089_: *mut crate::leanh::LeanObject,
    mut v_s_4090_: *mut crate::leanh::LeanObject,
    mut v_inst_4091_: *mut crate::leanh::LeanObject,
    mut v_x_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4093_ = l_String_Slice_SplitInclusiveIterator_ctorIdx(
        v_00_u03c3_4087_,
        v_00_u03c1_4088_,
        v_pat_4089_,
        v_s_4090_,
        v_inst_4091_,
        v_x_4092_,
    );
    crate::leanh::lean_dec(v_x_4092_);
    crate::leanh::lean_dec(v_inst_4091_);
    crate::leanh::lean_dec_ref(v_s_4090_);
    crate::leanh::lean_dec(v_pat_4089_);
    return v_res_4093_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(
    mut v_t_4094_: *mut crate::leanh::LeanObject,
    mut v_k_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4094_) == 0 {
        let mut v_currPos_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_currPos_4096_ = crate::leanh::lean_ctor_get(v_t_4094_, 0);
        crate::leanh::lean_inc(v_currPos_4096_);
        v_searcher_4097_ = crate::leanh::lean_ctor_get(v_t_4094_, 1);
        crate::leanh::lean_inc(v_searcher_4097_);
        crate::leanh::lean_dec_ref_known(v_t_4094_, 2);
        v___x_4098_ = crate::leanh::lean_apply_2(v_k_4095_, v_currPos_4096_, v_searcher_4097_);
        return v___x_4098_;
    } else {
        return v_k_4095_;
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorElim(
    mut v_00_u03c3_4099_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4100_: *mut crate::leanh::LeanObject,
    mut v_pat_4101_: *mut crate::leanh::LeanObject,
    mut v_s_4102_: *mut crate::leanh::LeanObject,
    mut v_inst_4103_: *mut crate::leanh::LeanObject,
    mut v_motive_4104_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4105_: *mut crate::leanh::LeanObject,
    mut v_t_4106_: *mut crate::leanh::LeanObject,
    mut v_h_4107_: *mut crate::leanh::LeanObject,
    mut v_k_4108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_4106_, v_k_4108_);
    return v___x_4109_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(
    mut v_00_u03c3_4110_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4111_: *mut crate::leanh::LeanObject,
    mut v_pat_4112_: *mut crate::leanh::LeanObject,
    mut v_s_4113_: *mut crate::leanh::LeanObject,
    mut v_inst_4114_: *mut crate::leanh::LeanObject,
    mut v_motive_4115_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4116_: *mut crate::leanh::LeanObject,
    mut v_t_4117_: *mut crate::leanh::LeanObject,
    mut v_h_4118_: *mut crate::leanh::LeanObject,
    mut v_k_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4120_ = l_String_Slice_SplitInclusiveIterator_ctorElim(
        v_00_u03c3_4110_,
        v_00_u03c1_4111_,
        v_pat_4112_,
        v_s_4113_,
        v_inst_4114_,
        v_motive_4115_,
        v_ctorIdx_4116_,
        v_t_4117_,
        v_h_4118_,
        v_k_4119_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4116_);
    crate::leanh::lean_dec(v_inst_4114_);
    crate::leanh::lean_dec_ref(v_s_4113_);
    crate::leanh::lean_dec(v_pat_4112_);
    return v_res_4120_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(
    mut v_t_4121_: *mut crate::leanh::LeanObject,
    mut v_operating_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4123_ =
        l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_4121_, v_operating_4122_);
    return v___x_4123_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_operating_elim(
    mut v_00_u03c3_4124_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4125_: *mut crate::leanh::LeanObject,
    mut v_pat_4126_: *mut crate::leanh::LeanObject,
    mut v_s_4127_: *mut crate::leanh::LeanObject,
    mut v_inst_4128_: *mut crate::leanh::LeanObject,
    mut v_motive_4129_: *mut crate::leanh::LeanObject,
    mut v_t_4130_: *mut crate::leanh::LeanObject,
    mut v_h_4131_: *mut crate::leanh::LeanObject,
    mut v_operating_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ =
        l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_4130_, v_operating_4132_);
    return v___x_4133_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(
    mut v_00_u03c3_4134_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4135_: *mut crate::leanh::LeanObject,
    mut v_pat_4136_: *mut crate::leanh::LeanObject,
    mut v_s_4137_: *mut crate::leanh::LeanObject,
    mut v_inst_4138_: *mut crate::leanh::LeanObject,
    mut v_motive_4139_: *mut crate::leanh::LeanObject,
    mut v_t_4140_: *mut crate::leanh::LeanObject,
    mut v_h_4141_: *mut crate::leanh::LeanObject,
    mut v_operating_4142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4143_ = l_String_Slice_SplitInclusiveIterator_operating_elim(
        v_00_u03c3_4134_,
        v_00_u03c1_4135_,
        v_pat_4136_,
        v_s_4137_,
        v_inst_4138_,
        v_motive_4139_,
        v_t_4140_,
        v_h_4141_,
        v_operating_4142_,
    );
    crate::leanh::lean_dec(v_inst_4138_);
    crate::leanh::lean_dec_ref(v_s_4137_);
    crate::leanh::lean_dec(v_pat_4136_);
    return v_res_4143_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(
    mut v_t_4144_: *mut crate::leanh::LeanObject,
    mut v_atEnd_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_4144_, v_atEnd_4145_);
    return v___x_4146_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_atEnd_elim(
    mut v_00_u03c3_4147_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4148_: *mut crate::leanh::LeanObject,
    mut v_pat_4149_: *mut crate::leanh::LeanObject,
    mut v_s_4150_: *mut crate::leanh::LeanObject,
    mut v_inst_4151_: *mut crate::leanh::LeanObject,
    mut v_motive_4152_: *mut crate::leanh::LeanObject,
    mut v_t_4153_: *mut crate::leanh::LeanObject,
    mut v_h_4154_: *mut crate::leanh::LeanObject,
    mut v_atEnd_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_4153_, v_atEnd_4155_);
    return v___x_4156_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(
    mut v_00_u03c3_4157_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4158_: *mut crate::leanh::LeanObject,
    mut v_pat_4159_: *mut crate::leanh::LeanObject,
    mut v_s_4160_: *mut crate::leanh::LeanObject,
    mut v_inst_4161_: *mut crate::leanh::LeanObject,
    mut v_motive_4162_: *mut crate::leanh::LeanObject,
    mut v_t_4163_: *mut crate::leanh::LeanObject,
    mut v_h_4164_: *mut crate::leanh::LeanObject,
    mut v_atEnd_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4166_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(
        v_00_u03c3_4157_,
        v_00_u03c1_4158_,
        v_pat_4159_,
        v_s_4160_,
        v_inst_4161_,
        v_motive_4162_,
        v_t_4163_,
        v_h_4164_,
        v_atEnd_4165_,
    );
    crate::leanh::lean_dec(v_inst_4161_);
    crate::leanh::lean_dec_ref(v_s_4160_);
    crate::leanh::lean_dec(v_pat_4159_);
    return v_res_4166_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitInclusiveIterator_default(
    mut v_00_u03c3_4167_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4168_: *mut crate::leanh::LeanObject,
    mut v_pat_4169_: *mut crate::leanh::LeanObject,
    mut v_s_4170_: *mut crate::leanh::LeanObject,
    mut v_inst_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4172_ = crate::leanh::lean_box(1);
    return v___x_4172_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(
    mut v_00_u03c3_4173_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_4174_: *mut crate::leanh::LeanObject,
    mut v_pat_4175_: *mut crate::leanh::LeanObject,
    mut v_s_4176_: *mut crate::leanh::LeanObject,
    mut v_inst_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(
        v_00_u03c3_4173_,
        v_00_u03c1_4174_,
        v_pat_4175_,
        v_s_4176_,
        v_inst_4177_,
    );
    crate::leanh::lean_dec(v_inst_4177_);
    crate::leanh::lean_dec_ref(v_s_4176_);
    crate::leanh::lean_dec(v_pat_4175_);
    return v_res_4178_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitInclusiveIterator(
    mut v_a_4179_: *mut crate::leanh::LeanObject,
    mut v_a_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4184_ = crate::leanh::lean_box(1);
    return v___x_4184_;
}
pub unsafe fn l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(
    mut v_a_4185_: *mut crate::leanh::LeanObject,
    mut v_a_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_String_Slice_instInhabitedSplitInclusiveIterator(
        v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_,
    );
    crate::leanh::lean_dec(v_a_4189_);
    crate::leanh::lean_dec_ref(v_a_4188_);
    crate::leanh::lean_dec(v_a_4187_);
    return v_res_4190_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(
    mut v_inst_4191_: *mut crate::leanh::LeanObject,
    mut v_s_4192_: *mut crate::leanh::LeanObject,
    mut v_x_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currPos_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4198_: u8 = 0;
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v_endPos_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v_unused_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_str_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4193_) == 0 {
                    v_currPos_4194_ = crate::leanh::lean_ctor_get(v_x_4193_, 0);
                    v_searcher_4195_ = crate::leanh::lean_ctor_get(v_x_4193_, 1);
                    v_isSharedCheck_4247_ = (!crate::leanh::lean_is_exclusive(v_x_4193_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4197_ = v_x_4193_;
                        v_isShared_4198_ = v_isSharedCheck_4247_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_4195_);
                        crate::leanh::lean_inc(v_currPos_4194_);
                        crate::leanh::lean_dec(v_x_4193_);
                        v___x_4197_ = crate::leanh::lean_box(0);
                        v_isShared_4198_ = v_isSharedCheck_4247_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_4192_);
                    crate::leanh::lean_dec(v_inst_4191_);
                    v___x_4248_ = crate::leanh::lean_box(2);
                    return v___x_4248_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_4192_);
                v___x_4199_ = crate::leanh::lean_apply_2(v_inst_4191_, v_s_4192_, v_searcher_4195_);
                match crate::leanh::lean_obj_tag(v___x_4199_) {
                    0 => {
                        v_out_4200_ = crate::leanh::lean_ctor_get(v___x_4199_, 1);
                        crate::leanh::lean_inc(v_out_4200_);
                        if crate::leanh::lean_obj_tag(v_out_4200_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_4200_, 2);
                            crate::leanh::lean_dec_ref(v_s_4192_);
                            v_it_4201_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                            crate::leanh::lean_inc(v_it_4201_);
                            crate::leanh::lean_dec_ref_known(v___x_4199_, 2);
                            if v_isShared_4198_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4197_, 1, v_it_4201_);
                                v___x_4203_ = v___x_4197_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4205_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4205_,
                                    0,
                                    v_currPos_4194_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_it_4201_);
                                v___x_4203_ = v_reuseFailAlloc_4205_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_4206_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                            v_isSharedCheck_4218_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4199_)) as u8;
                            if v_isSharedCheck_4218_ == 0 {
                                v_unused_4219_ = crate::leanh::lean_ctor_get(v___x_4199_, 1);
                                crate::leanh::lean_dec(v_unused_4219_);
                                v___x_4208_ = v___x_4199_;
                                v_isShared_4209_ = v_isSharedCheck_4218_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_4206_);
                                crate::leanh::lean_dec(v___x_4199_);
                                v___x_4208_ = crate::leanh::lean_box(0);
                                v_isShared_4209_ = v_isSharedCheck_4218_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_4192_);
                        v_it_4220_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                        v_isSharedCheck_4230_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4199_)) as u8;
                        if v_isSharedCheck_4230_ == 0 {
                            v___x_4222_ = v___x_4199_;
                            v_isShared_4223_ = v_isSharedCheck_4230_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_4220_);
                            crate::leanh::lean_dec(v___x_4199_);
                            v___x_4222_ = crate::leanh::lean_box(0);
                            v_isShared_4223_ = v_isSharedCheck_4230_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_4197_);
                        v_str_4231_ = crate::leanh::lean_ctor_get(v_s_4192_, 0);
                        v_startInclusive_4232_ = crate::leanh::lean_ctor_get(v_s_4192_, 1);
                        v_endExclusive_4233_ = crate::leanh::lean_ctor_get(v_s_4192_, 2);
                        v_isSharedCheck_4246_ = (!crate::leanh::lean_is_exclusive(v_s_4192_)) as u8;
                        if v_isSharedCheck_4246_ == 0 {
                            v___x_4235_ = v_s_4192_;
                            v_isShared_4236_ = v_isSharedCheck_4246_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_endExclusive_4233_);
                            crate::leanh::lean_inc(v_startInclusive_4232_);
                            crate::leanh::lean_inc(v_str_4231_);
                            crate::leanh::lean_dec(v_s_4192_);
                            v___x_4235_ = crate::leanh::lean_box(0);
                            v_isShared_4236_ = v_isSharedCheck_4246_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
                return v___x_4204_;
            }
            3 => {
                v_endPos_4210_ = crate::leanh::lean_ctor_get(v_out_4200_, 1);
                crate::leanh::lean_inc(v_endPos_4210_);
                crate::leanh::lean_dec_ref_known(v_out_4200_, 2);
                v_slice_4211_ =
                    l_String_Slice_slice_x21(v_s_4192_, v_currPos_4194_, v_endPos_4210_);
                crate::leanh::lean_dec(v_currPos_4194_);
                if v_isShared_4198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4197_, 1, v_it_4206_);
                    crate::leanh::lean_ctor_set(v___x_4197_, 0, v_endPos_4210_);
                    v_nextIt_4213_ = v___x_4197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_endPos_4210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_it_4206_);
                    v_nextIt_4213_ = v_reuseFailAlloc_4217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4208_, 1, v_slice_4211_);
                    crate::leanh::lean_ctor_set(v___x_4208_, 0, v_nextIt_4213_);
                    v___x_4215_ = v___x_4208_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_nextIt_4213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_slice_4211_);
                    v___x_4215_ = v_reuseFailAlloc_4216_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4215_;
            }
            6 => {
                if v_isShared_4198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4197_, 1, v_it_4220_);
                    v___x_4225_ = v___x_4197_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_currPos_4194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_it_4220_);
                    v___x_4225_ = v_reuseFailAlloc_4229_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4222_, 0, v___x_4225_);
                    v___x_4227_ = v___x_4222_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4227_;
            }
            9 => {
                v___x_4237_ = lean_nat_sub(v_endExclusive_4233_, v_startInclusive_4232_);
                v___x_4238_ = lean_nat_dec_eq(v_currPos_4194_, v___x_4237_);
                crate::leanh::lean_dec(v___x_4237_);
                if v___x_4238_ == 0 {
                    v___x_4239_ = lean_nat_add(v_startInclusive_4232_, v_currPos_4194_);
                    crate::leanh::lean_dec(v_currPos_4194_);
                    crate::leanh::lean_dec(v_startInclusive_4232_);
                    if v_isShared_4236_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4235_, 1, v___x_4239_);
                        v_slice_4241_ = v___x_4235_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_str_4231_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4239_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_4244_,
                            2,
                            v_endExclusive_4233_,
                        );
                        v_slice_4241_ = v_reuseFailAlloc_4244_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4235_);
                    crate::leanh::lean_dec(v_endExclusive_4233_);
                    crate::leanh::lean_dec(v_startInclusive_4232_);
                    crate::leanh::lean_dec_ref(v_str_4231_);
                    crate::leanh::lean_dec(v_currPos_4194_);
                    v___x_4245_ = crate::leanh::lean_box(2);
                    return v___x_4245_;
                }
            }
            10 => {
                v___x_4242_ = crate::leanh::lean_box(1);
                v___x_4243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4242_);
                crate::leanh::lean_ctor_set(v___x_4243_, 1, v_slice_4241_);
                return v___x_4243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(
    mut v_inst_4249_: *mut crate::leanh::LeanObject,
    mut v_s_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4251_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4251_, 0, v_inst_4249_);
    crate::leanh::lean_closure_set(v___f_4251_, 1, v_s_4250_);
    return v___f_4251_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorId(
    mut v_00_u03c1_4252_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4253_: *mut crate::leanh::LeanObject,
    mut v_inst_4254_: *mut crate::leanh::LeanObject,
    mut v_pat_4255_: *mut crate::leanh::LeanObject,
    mut v_inst_4256_: *mut crate::leanh::LeanObject,
    mut v_s_4257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4258_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4258_, 0, v_inst_4254_);
    crate::leanh::lean_closure_set(v___f_4258_, 1, v_s_4257_);
    return v___f_4258_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(
    mut v_00_u03c1_4259_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4260_: *mut crate::leanh::LeanObject,
    mut v_inst_4261_: *mut crate::leanh::LeanObject,
    mut v_pat_4262_: *mut crate::leanh::LeanObject,
    mut v_inst_4263_: *mut crate::leanh::LeanObject,
    mut v_s_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4265_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(
        v_00_u03c1_4259_,
        v_00_u03c3_4260_,
        v_inst_4261_,
        v_pat_4262_,
        v_inst_4263_,
        v_s_4264_,
    );
    crate::leanh::lean_dec(v_inst_4263_);
    crate::leanh::lean_dec(v_pat_4262_);
    return v_res_4265_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(
    mut v_x_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4266_) == 0 {
        let mut v_searcher_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_searcher_4267_ = crate::leanh::lean_ctor_get(v_x_4266_, 1);
        crate::leanh::lean_inc(v_searcher_4267_);
        v___x_4268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4268_, 0, v_searcher_4267_);
        return v___x_4268_;
    } else {
        let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4269_ = crate::leanh::lean_box(0);
        return v___x_4269_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(
    mut v_x_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4271_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(
            v_x_4270_,
        );
    crate::leanh::lean_dec(v_x_4270_);
    return v_res_4271_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(
    mut v_00_u03c1_4272_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4273_: *mut crate::leanh::LeanObject,
    mut v_pat_4274_: *mut crate::leanh::LeanObject,
    mut v_inst_4275_: *mut crate::leanh::LeanObject,
    mut v_s_4276_: *mut crate::leanh::LeanObject,
    mut v_x_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(
            v_x_4277_,
        );
    return v___x_4278_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(
    mut v_00_u03c1_4279_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4280_: *mut crate::leanh::LeanObject,
    mut v_pat_4281_: *mut crate::leanh::LeanObject,
    mut v_inst_4282_: *mut crate::leanh::LeanObject,
    mut v_s_4283_: *mut crate::leanh::LeanObject,
    mut v_x_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4285_ =
        l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(
            v_00_u03c1_4279_,
            v_00_u03c3_4280_,
            v_pat_4281_,
            v_inst_4282_,
            v_s_4283_,
            v_x_4284_,
        );
    crate::leanh::lean_dec(v_x_4284_);
    crate::leanh::lean_dec_ref(v_s_4283_);
    crate::leanh::lean_dec(v_inst_4282_);
    crate::leanh::lean_dec(v_pat_4281_);
    return v_res_4285_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(
    mut v_x_4286_: *mut crate::leanh::LeanObject,
    mut v_h__1_4287_: *mut crate::leanh::LeanObject,
    mut v_h__2_4288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4286_) == 0 {
        let mut v_currPos_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4288_);
        v_currPos_4289_ = crate::leanh::lean_ctor_get(v_x_4286_, 0);
        crate::leanh::lean_inc(v_currPos_4289_);
        v_searcher_4290_ = crate::leanh::lean_ctor_get(v_x_4286_, 1);
        crate::leanh::lean_inc(v_searcher_4290_);
        crate::leanh::lean_dec_ref_known(v_x_4286_, 2);
        v___x_4291_ = crate::leanh::lean_apply_2(v_h__1_4287_, v_currPos_4289_, v_searcher_4290_);
        return v___x_4291_;
    } else {
        let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4287_);
        v___x_4292_ = crate::leanh::lean_box(0);
        v___x_4293_ = crate::leanh::lean_apply_1(v_h__2_4288_, v___x_4292_);
        return v___x_4293_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(
    mut v_00_u03c1_4294_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4295_: *mut crate::leanh::LeanObject,
    mut v_pat_4296_: *mut crate::leanh::LeanObject,
    mut v_inst_4297_: *mut crate::leanh::LeanObject,
    mut v_s_4298_: *mut crate::leanh::LeanObject,
    mut v_motive_4299_: *mut crate::leanh::LeanObject,
    mut v_x_4300_: *mut crate::leanh::LeanObject,
    mut v_h__1_4301_: *mut crate::leanh::LeanObject,
    mut v_h__2_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4300_) == 0 {
        let mut v_currPos_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4302_);
        v_currPos_4303_ = crate::leanh::lean_ctor_get(v_x_4300_, 0);
        crate::leanh::lean_inc(v_currPos_4303_);
        v_searcher_4304_ = crate::leanh::lean_ctor_get(v_x_4300_, 1);
        crate::leanh::lean_inc(v_searcher_4304_);
        crate::leanh::lean_dec_ref_known(v_x_4300_, 2);
        v___x_4305_ = crate::leanh::lean_apply_2(v_h__1_4301_, v_currPos_4303_, v_searcher_4304_);
        return v___x_4305_;
    } else {
        let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4301_);
        v___x_4306_ = crate::leanh::lean_box(0);
        v___x_4307_ = crate::leanh::lean_apply_1(v_h__2_4302_, v___x_4306_);
        return v___x_4307_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(
    mut v_00_u03c1_4308_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4309_: *mut crate::leanh::LeanObject,
    mut v_pat_4310_: *mut crate::leanh::LeanObject,
    mut v_inst_4311_: *mut crate::leanh::LeanObject,
    mut v_s_4312_: *mut crate::leanh::LeanObject,
    mut v_motive_4313_: *mut crate::leanh::LeanObject,
    mut v_x_4314_: *mut crate::leanh::LeanObject,
    mut v_h__1_4315_: *mut crate::leanh::LeanObject,
    mut v_h__2_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4317_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_4308_, v_00_u03c3_4309_, v_pat_4310_, v_inst_4311_, v_s_4312_, v_motive_4313_, v_x_4314_, v_h__1_4315_, v_h__2_4316_);
    crate::leanh::lean_dec_ref(v_s_4312_);
    crate::leanh::lean_dec(v_inst_4311_);
    crate::leanh::lean_dec(v_pat_4310_);
    return v_res_4317_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(
    mut v_x_4318_: *mut crate::leanh::LeanObject,
    mut v_x_4319_: *mut crate::leanh::LeanObject,
    mut v_h__1_4320_: *mut crate::leanh::LeanObject,
    mut v_h__2_4321_: *mut crate::leanh::LeanObject,
    mut v_h__3_4322_: *mut crate::leanh::LeanObject,
    mut v_h__4_4323_: *mut crate::leanh::LeanObject,
    mut v_h__5_4324_: *mut crate::leanh::LeanObject,
    mut v_h__6_4325_: *mut crate::leanh::LeanObject,
    mut v_h__7_4326_: *mut crate::leanh::LeanObject,
    mut v_h__8_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4318_) == 0 {
        crate::leanh::lean_dec(v_h__8_4327_);
        crate::leanh::lean_dec(v_h__7_4326_);
        crate::leanh::lean_dec(v_h__6_4325_);
        match crate::leanh::lean_obj_tag(v_x_4319_) {
            0 => {
                let mut v_it_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_4324_);
                crate::leanh::lean_dec(v_h__4_4323_);
                crate::leanh::lean_dec(v_h__3_4322_);
                v_it_4328_ = crate::leanh::lean_ctor_get(v_x_4319_, 0);
                if crate::leanh::lean_obj_tag(v_it_4328_) == 0 {
                    let mut v_currPos_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_4328_);
                    crate::leanh::lean_dec(v_h__2_4321_);
                    v_currPos_4329_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                    crate::leanh::lean_inc(v_currPos_4329_);
                    v_searcher_4330_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                    crate::leanh::lean_inc(v_searcher_4330_);
                    crate::leanh::lean_dec_ref_known(v_x_4318_, 2);
                    v_out_4331_ = crate::leanh::lean_ctor_get(v_x_4319_, 1);
                    crate::leanh::lean_inc(v_out_4331_);
                    crate::leanh::lean_dec_ref_known(v_x_4319_, 2);
                    v_currPos_4332_ = crate::leanh::lean_ctor_get(v_it_4328_, 0);
                    crate::leanh::lean_inc(v_currPos_4332_);
                    v_searcher_4333_ = crate::leanh::lean_ctor_get(v_it_4328_, 1);
                    crate::leanh::lean_inc(v_searcher_4333_);
                    crate::leanh::lean_dec_ref_known(v_it_4328_, 2);
                    v___x_4334_ = crate::leanh::lean_apply_5(
                        v_h__1_4320_,
                        v_currPos_4329_,
                        v_searcher_4330_,
                        v_currPos_4332_,
                        v_searcher_4333_,
                        v_out_4331_,
                    );
                    return v___x_4334_;
                } else {
                    let mut v_currPos_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_4320_);
                    v_currPos_4335_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                    crate::leanh::lean_inc(v_currPos_4335_);
                    v_searcher_4336_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                    crate::leanh::lean_inc(v_searcher_4336_);
                    crate::leanh::lean_dec_ref_known(v_x_4318_, 2);
                    v_out_4337_ = crate::leanh::lean_ctor_get(v_x_4319_, 1);
                    crate::leanh::lean_inc(v_out_4337_);
                    crate::leanh::lean_dec_ref_known(v_x_4319_, 2);
                    v___x_4338_ = crate::leanh::lean_apply_3(
                        v_h__2_4321_,
                        v_currPos_4335_,
                        v_searcher_4336_,
                        v_out_4337_,
                    );
                    return v___x_4338_;
                }
            }
            1 => {
                let mut v_it_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_4324_);
                crate::leanh::lean_dec(v_h__2_4321_);
                crate::leanh::lean_dec(v_h__1_4320_);
                v_it_4339_ = crate::leanh::lean_ctor_get(v_x_4319_, 0);
                crate::leanh::lean_inc(v_it_4339_);
                crate::leanh::lean_dec_ref_known(v_x_4319_, 1);
                if crate::leanh::lean_obj_tag(v_it_4339_) == 0 {
                    let mut v_currPos_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4323_);
                    v_currPos_4340_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                    crate::leanh::lean_inc(v_currPos_4340_);
                    v_searcher_4341_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                    crate::leanh::lean_inc(v_searcher_4341_);
                    crate::leanh::lean_dec_ref_known(v_x_4318_, 2);
                    v_currPos_4342_ = crate::leanh::lean_ctor_get(v_it_4339_, 0);
                    crate::leanh::lean_inc(v_currPos_4342_);
                    v_searcher_4343_ = crate::leanh::lean_ctor_get(v_it_4339_, 1);
                    crate::leanh::lean_inc(v_searcher_4343_);
                    crate::leanh::lean_dec_ref_known(v_it_4339_, 2);
                    v___x_4344_ = crate::leanh::lean_apply_4(
                        v_h__3_4322_,
                        v_currPos_4340_,
                        v_searcher_4341_,
                        v_currPos_4342_,
                        v_searcher_4343_,
                    );
                    return v___x_4344_;
                } else {
                    let mut v_currPos_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_4322_);
                    v_currPos_4345_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                    crate::leanh::lean_inc(v_currPos_4345_);
                    v_searcher_4346_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                    crate::leanh::lean_inc(v_searcher_4346_);
                    crate::leanh::lean_dec_ref_known(v_x_4318_, 2);
                    v___x_4347_ =
                        crate::leanh::lean_apply_2(v_h__4_4323_, v_currPos_4345_, v_searcher_4346_);
                    return v___x_4347_;
                }
            }
            _ => {
                let mut v_currPos_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_4323_);
                crate::leanh::lean_dec(v_h__3_4322_);
                crate::leanh::lean_dec(v_h__2_4321_);
                crate::leanh::lean_dec(v_h__1_4320_);
                v_currPos_4348_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                crate::leanh::lean_inc(v_currPos_4348_);
                v_searcher_4349_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                crate::leanh::lean_inc(v_searcher_4349_);
                crate::leanh::lean_dec_ref_known(v_x_4318_, 2);
                v___x_4350_ =
                    crate::leanh::lean_apply_2(v_h__5_4324_, v_currPos_4348_, v_searcher_4349_);
                return v___x_4350_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_4324_);
        crate::leanh::lean_dec(v_h__4_4323_);
        crate::leanh::lean_dec(v_h__3_4322_);
        crate::leanh::lean_dec(v_h__2_4321_);
        crate::leanh::lean_dec(v_h__1_4320_);
        match crate::leanh::lean_obj_tag(v_x_4319_) {
            0 => {
                let mut v_it_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_4327_);
                crate::leanh::lean_dec(v_h__7_4326_);
                v_it_4351_ = crate::leanh::lean_ctor_get(v_x_4319_, 0);
                crate::leanh::lean_inc(v_it_4351_);
                v_out_4352_ = crate::leanh::lean_ctor_get(v_x_4319_, 1);
                crate::leanh::lean_inc(v_out_4352_);
                crate::leanh::lean_dec_ref_known(v_x_4319_, 2);
                v___x_4353_ = crate::leanh::lean_apply_2(v_h__6_4325_, v_it_4351_, v_out_4352_);
                return v___x_4353_;
            }
            1 => {
                let mut v_it_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_4327_);
                crate::leanh::lean_dec(v_h__6_4325_);
                v_it_4354_ = crate::leanh::lean_ctor_get(v_x_4319_, 0);
                crate::leanh::lean_inc(v_it_4354_);
                crate::leanh::lean_dec_ref_known(v_x_4319_, 1);
                v___x_4355_ = crate::leanh::lean_apply_1(v_h__7_4326_, v_it_4354_);
                return v___x_4355_;
            }
            _ => {
                let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_4326_);
                crate::leanh::lean_dec(v_h__6_4325_);
                v___x_4356_ = crate::leanh::lean_box(0);
                v___x_4357_ = crate::leanh::lean_apply_1(v_h__8_4327_, v___x_4356_);
                return v___x_4357_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(
    mut v_00_u03c1_4358_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4359_: *mut crate::leanh::LeanObject,
    mut v_pat_4360_: *mut crate::leanh::LeanObject,
    mut v_inst_4361_: *mut crate::leanh::LeanObject,
    mut v_s_4362_: *mut crate::leanh::LeanObject,
    mut v_motive_4363_: *mut crate::leanh::LeanObject,
    mut v_x_4364_: *mut crate::leanh::LeanObject,
    mut v_x_4365_: *mut crate::leanh::LeanObject,
    mut v_h__1_4366_: *mut crate::leanh::LeanObject,
    mut v_h__2_4367_: *mut crate::leanh::LeanObject,
    mut v_h__3_4368_: *mut crate::leanh::LeanObject,
    mut v_h__4_4369_: *mut crate::leanh::LeanObject,
    mut v_h__5_4370_: *mut crate::leanh::LeanObject,
    mut v_h__6_4371_: *mut crate::leanh::LeanObject,
    mut v_h__7_4372_: *mut crate::leanh::LeanObject,
    mut v_h__8_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4364_) == 0 {
        crate::leanh::lean_dec(v_h__8_4373_);
        crate::leanh::lean_dec(v_h__7_4372_);
        crate::leanh::lean_dec(v_h__6_4371_);
        match crate::leanh::lean_obj_tag(v_x_4365_) {
            0 => {
                let mut v_it_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_4370_);
                crate::leanh::lean_dec(v_h__4_4369_);
                crate::leanh::lean_dec(v_h__3_4368_);
                v_it_4374_ = crate::leanh::lean_ctor_get(v_x_4365_, 0);
                if crate::leanh::lean_obj_tag(v_it_4374_) == 0 {
                    let mut v_currPos_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_4374_);
                    crate::leanh::lean_dec(v_h__2_4367_);
                    v_currPos_4375_ = crate::leanh::lean_ctor_get(v_x_4364_, 0);
                    crate::leanh::lean_inc(v_currPos_4375_);
                    v_searcher_4376_ = crate::leanh::lean_ctor_get(v_x_4364_, 1);
                    crate::leanh::lean_inc(v_searcher_4376_);
                    crate::leanh::lean_dec_ref_known(v_x_4364_, 2);
                    v_out_4377_ = crate::leanh::lean_ctor_get(v_x_4365_, 1);
                    crate::leanh::lean_inc(v_out_4377_);
                    crate::leanh::lean_dec_ref_known(v_x_4365_, 2);
                    v_currPos_4378_ = crate::leanh::lean_ctor_get(v_it_4374_, 0);
                    crate::leanh::lean_inc(v_currPos_4378_);
                    v_searcher_4379_ = crate::leanh::lean_ctor_get(v_it_4374_, 1);
                    crate::leanh::lean_inc(v_searcher_4379_);
                    crate::leanh::lean_dec_ref_known(v_it_4374_, 2);
                    v___x_4380_ = crate::leanh::lean_apply_5(
                        v_h__1_4366_,
                        v_currPos_4375_,
                        v_searcher_4376_,
                        v_currPos_4378_,
                        v_searcher_4379_,
                        v_out_4377_,
                    );
                    return v___x_4380_;
                } else {
                    let mut v_currPos_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_4366_);
                    v_currPos_4381_ = crate::leanh::lean_ctor_get(v_x_4364_, 0);
                    crate::leanh::lean_inc(v_currPos_4381_);
                    v_searcher_4382_ = crate::leanh::lean_ctor_get(v_x_4364_, 1);
                    crate::leanh::lean_inc(v_searcher_4382_);
                    crate::leanh::lean_dec_ref_known(v_x_4364_, 2);
                    v_out_4383_ = crate::leanh::lean_ctor_get(v_x_4365_, 1);
                    crate::leanh::lean_inc(v_out_4383_);
                    crate::leanh::lean_dec_ref_known(v_x_4365_, 2);
                    v___x_4384_ = crate::leanh::lean_apply_3(
                        v_h__2_4367_,
                        v_currPos_4381_,
                        v_searcher_4382_,
                        v_out_4383_,
                    );
                    return v___x_4384_;
                }
            }
            1 => {
                let mut v_it_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_4370_);
                crate::leanh::lean_dec(v_h__2_4367_);
                crate::leanh::lean_dec(v_h__1_4366_);
                v_it_4385_ = crate::leanh::lean_ctor_get(v_x_4365_, 0);
                crate::leanh::lean_inc(v_it_4385_);
                crate::leanh::lean_dec_ref_known(v_x_4365_, 1);
                if crate::leanh::lean_obj_tag(v_it_4385_) == 0 {
                    let mut v_currPos_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4369_);
                    v_currPos_4386_ = crate::leanh::lean_ctor_get(v_x_4364_, 0);
                    crate::leanh::lean_inc(v_currPos_4386_);
                    v_searcher_4387_ = crate::leanh::lean_ctor_get(v_x_4364_, 1);
                    crate::leanh::lean_inc(v_searcher_4387_);
                    crate::leanh::lean_dec_ref_known(v_x_4364_, 2);
                    v_currPos_4388_ = crate::leanh::lean_ctor_get(v_it_4385_, 0);
                    crate::leanh::lean_inc(v_currPos_4388_);
                    v_searcher_4389_ = crate::leanh::lean_ctor_get(v_it_4385_, 1);
                    crate::leanh::lean_inc(v_searcher_4389_);
                    crate::leanh::lean_dec_ref_known(v_it_4385_, 2);
                    v___x_4390_ = crate::leanh::lean_apply_4(
                        v_h__3_4368_,
                        v_currPos_4386_,
                        v_searcher_4387_,
                        v_currPos_4388_,
                        v_searcher_4389_,
                    );
                    return v___x_4390_;
                } else {
                    let mut v_currPos_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_4368_);
                    v_currPos_4391_ = crate::leanh::lean_ctor_get(v_x_4364_, 0);
                    crate::leanh::lean_inc(v_currPos_4391_);
                    v_searcher_4392_ = crate::leanh::lean_ctor_get(v_x_4364_, 1);
                    crate::leanh::lean_inc(v_searcher_4392_);
                    crate::leanh::lean_dec_ref_known(v_x_4364_, 2);
                    v___x_4393_ =
                        crate::leanh::lean_apply_2(v_h__4_4369_, v_currPos_4391_, v_searcher_4392_);
                    return v___x_4393_;
                }
            }
            _ => {
                let mut v_currPos_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_4369_);
                crate::leanh::lean_dec(v_h__3_4368_);
                crate::leanh::lean_dec(v_h__2_4367_);
                crate::leanh::lean_dec(v_h__1_4366_);
                v_currPos_4394_ = crate::leanh::lean_ctor_get(v_x_4364_, 0);
                crate::leanh::lean_inc(v_currPos_4394_);
                v_searcher_4395_ = crate::leanh::lean_ctor_get(v_x_4364_, 1);
                crate::leanh::lean_inc(v_searcher_4395_);
                crate::leanh::lean_dec_ref_known(v_x_4364_, 2);
                v___x_4396_ =
                    crate::leanh::lean_apply_2(v_h__5_4370_, v_currPos_4394_, v_searcher_4395_);
                return v___x_4396_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_4370_);
        crate::leanh::lean_dec(v_h__4_4369_);
        crate::leanh::lean_dec(v_h__3_4368_);
        crate::leanh::lean_dec(v_h__2_4367_);
        crate::leanh::lean_dec(v_h__1_4366_);
        match crate::leanh::lean_obj_tag(v_x_4365_) {
            0 => {
                let mut v_it_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_4373_);
                crate::leanh::lean_dec(v_h__7_4372_);
                v_it_4397_ = crate::leanh::lean_ctor_get(v_x_4365_, 0);
                crate::leanh::lean_inc(v_it_4397_);
                v_out_4398_ = crate::leanh::lean_ctor_get(v_x_4365_, 1);
                crate::leanh::lean_inc(v_out_4398_);
                crate::leanh::lean_dec_ref_known(v_x_4365_, 2);
                v___x_4399_ = crate::leanh::lean_apply_2(v_h__6_4371_, v_it_4397_, v_out_4398_);
                return v___x_4399_;
            }
            1 => {
                let mut v_it_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_4373_);
                crate::leanh::lean_dec(v_h__6_4371_);
                v_it_4400_ = crate::leanh::lean_ctor_get(v_x_4365_, 0);
                crate::leanh::lean_inc(v_it_4400_);
                crate::leanh::lean_dec_ref_known(v_x_4365_, 1);
                v___x_4401_ = crate::leanh::lean_apply_1(v_h__7_4372_, v_it_4400_);
                return v___x_4401_;
            }
            _ => {
                let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_4372_);
                crate::leanh::lean_dec(v_h__6_4371_);
                v___x_4402_ = crate::leanh::lean_box(0);
                v___x_4403_ = crate::leanh::lean_apply_1(v_h__8_4373_, v___x_4402_);
                return v___x_4403_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(
    mut v_00_u03c1_4404_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4405_: *mut crate::leanh::LeanObject,
    mut v_pat_4406_: *mut crate::leanh::LeanObject,
    mut v_inst_4407_: *mut crate::leanh::LeanObject,
    mut v_s_4408_: *mut crate::leanh::LeanObject,
    mut v_motive_4409_: *mut crate::leanh::LeanObject,
    mut v_x_4410_: *mut crate::leanh::LeanObject,
    mut v_x_4411_: *mut crate::leanh::LeanObject,
    mut v_h__1_4412_: *mut crate::leanh::LeanObject,
    mut v_h__2_4413_: *mut crate::leanh::LeanObject,
    mut v_h__3_4414_: *mut crate::leanh::LeanObject,
    mut v_h__4_4415_: *mut crate::leanh::LeanObject,
    mut v_h__5_4416_: *mut crate::leanh::LeanObject,
    mut v_h__6_4417_: *mut crate::leanh::LeanObject,
    mut v_h__7_4418_: *mut crate::leanh::LeanObject,
    mut v_h__8_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4420_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_4404_, v_00_u03c3_4405_, v_pat_4406_, v_inst_4407_, v_s_4408_, v_motive_4409_, v_x_4410_, v_x_4411_, v_h__1_4412_, v_h__2_4413_, v_h__3_4414_, v_h__4_4415_, v_h__5_4416_, v_h__6_4417_, v_h__7_4418_, v_h__8_4419_);
    crate::leanh::lean_dec_ref(v_s_4408_);
    crate::leanh::lean_dec(v_inst_4407_);
    crate::leanh::lean_dec(v_pat_4406_);
    return v_res_4420_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(
    mut v_x_4421_: *mut crate::leanh::LeanObject,
    mut v_h__1_4422_: *mut crate::leanh::LeanObject,
    mut v_h__2_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4421_) == 0 {
        let mut v_currPos_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4423_);
        v_currPos_4424_ = crate::leanh::lean_ctor_get(v_x_4421_, 0);
        crate::leanh::lean_inc(v_currPos_4424_);
        v_searcher_4425_ = crate::leanh::lean_ctor_get(v_x_4421_, 1);
        crate::leanh::lean_inc(v_searcher_4425_);
        crate::leanh::lean_dec_ref_known(v_x_4421_, 2);
        v___x_4426_ = crate::leanh::lean_apply_2(v_h__1_4422_, v_currPos_4424_, v_searcher_4425_);
        return v___x_4426_;
    } else {
        let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4422_);
        v___x_4427_ = crate::leanh::lean_box(0);
        v___x_4428_ = crate::leanh::lean_apply_1(v_h__2_4423_, v___x_4427_);
        return v___x_4428_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(
    mut v_00_u03c1_4429_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4430_: *mut crate::leanh::LeanObject,
    mut v_pat_4431_: *mut crate::leanh::LeanObject,
    mut v_inst_4432_: *mut crate::leanh::LeanObject,
    mut v_s_4433_: *mut crate::leanh::LeanObject,
    mut v_motive_4434_: *mut crate::leanh::LeanObject,
    mut v_x_4435_: *mut crate::leanh::LeanObject,
    mut v_h__1_4436_: *mut crate::leanh::LeanObject,
    mut v_h__2_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4435_) == 0 {
        let mut v_currPos_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4437_);
        v_currPos_4438_ = crate::leanh::lean_ctor_get(v_x_4435_, 0);
        crate::leanh::lean_inc(v_currPos_4438_);
        v_searcher_4439_ = crate::leanh::lean_ctor_get(v_x_4435_, 1);
        crate::leanh::lean_inc(v_searcher_4439_);
        crate::leanh::lean_dec_ref_known(v_x_4435_, 2);
        v___x_4440_ = crate::leanh::lean_apply_2(v_h__1_4436_, v_currPos_4438_, v_searcher_4439_);
        return v___x_4440_;
    } else {
        let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4436_);
        v___x_4441_ = crate::leanh::lean_box(0);
        v___x_4442_ = crate::leanh::lean_apply_1(v_h__2_4437_, v___x_4441_);
        return v___x_4442_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(
    mut v_00_u03c1_4443_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4444_: *mut crate::leanh::LeanObject,
    mut v_pat_4445_: *mut crate::leanh::LeanObject,
    mut v_inst_4446_: *mut crate::leanh::LeanObject,
    mut v_s_4447_: *mut crate::leanh::LeanObject,
    mut v_motive_4448_: *mut crate::leanh::LeanObject,
    mut v_x_4449_: *mut crate::leanh::LeanObject,
    mut v_h__1_4450_: *mut crate::leanh::LeanObject,
    mut v_h__2_4451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4452_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_4443_, v_00_u03c3_4444_, v_pat_4445_, v_inst_4446_, v_s_4447_, v_motive_4448_, v_x_4449_, v_h__1_4450_, v_h__2_4451_);
    crate::leanh::lean_dec_ref(v_s_4447_);
    crate::leanh::lean_dec(v_inst_4446_);
    crate::leanh::lean_dec(v_pat_4445_);
    return v_res_4452_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(
    mut v_00_u03c1_4453_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4454_: *mut crate::leanh::LeanObject,
    mut v_inst_4455_: *mut crate::leanh::LeanObject,
    mut v_pat_4456_: *mut crate::leanh::LeanObject,
    mut v_inst_4457_: *mut crate::leanh::LeanObject,
    mut v_s_4458_: *mut crate::leanh::LeanObject,
    mut v_inst_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = crate::leanh::lean_box(0);
    return v___x_4460_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(
    mut v_00_u03c1_4461_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4462_: *mut crate::leanh::LeanObject,
    mut v_inst_4463_: *mut crate::leanh::LeanObject,
    mut v_pat_4464_: *mut crate::leanh::LeanObject,
    mut v_inst_4465_: *mut crate::leanh::LeanObject,
    mut v_s_4466_: *mut crate::leanh::LeanObject,
    mut v_inst_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4468_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_4461_, v_00_u03c3_4462_, v_inst_4463_, v_pat_4464_, v_inst_4465_, v_s_4466_, v_inst_4467_);
    crate::leanh::lean_dec_ref(v_s_4466_);
    crate::leanh::lean_dec(v_inst_4465_);
    crate::leanh::lean_dec(v_pat_4464_);
    crate::leanh::lean_dec(v_inst_4463_);
    return v_res_4468_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(
    mut v_toPure_4469_: *mut crate::leanh::LeanObject,
    mut v_recur_4470_: *mut crate::leanh::LeanObject,
    mut v_it_4471_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_4472_) == 0 {
        let mut v_a_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_4471_);
        crate::leanh::lean_dec(v_recur_4470_);
        v_a_4473_ = crate::leanh::lean_ctor_get(v_____do__lift_4472_, 0);
        crate::leanh::lean_inc(v_a_4473_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_4472_, 1);
        v___x_4474_ =
            crate::leanh::lean_apply_2(v_toPure_4469_, crate::leanh::lean_box(0), v_a_4473_);
        return v___x_4474_;
    } else {
        let mut v_a_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4469_);
        v_a_4475_ = crate::leanh::lean_ctor_get(v_____do__lift_4472_, 0);
        crate::leanh::lean_inc(v_a_4475_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_4472_, 1);
        v___x_4476_ = crate::leanh::lean_apply_4(
            v_recur_4470_,
            v_it_4471_,
            v_a_4475_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_4476_;
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(
    mut v_toPure_4477_: *mut crate::leanh::LeanObject,
    mut v_recur_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v_acc_4480_: *mut crate::leanh::LeanObject,
    mut v_toBind_4481_: *mut crate::leanh::LeanObject,
    mut v_s_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_4482_) {
        0 => {
            let mut v_it_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_4483_ = crate::leanh::lean_ctor_get(v_s_4482_, 0);
            crate::leanh::lean_inc(v_it_4483_);
            v_out_4484_ = crate::leanh::lean_ctor_get(v_s_4482_, 1);
            crate::leanh::lean_inc(v_out_4484_);
            crate::leanh::lean_dec_ref_known(v_s_4482_, 2);
            v___f_4485_ = crate::leanh::lean_alloc_closure(
                l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_4485_, 0, v_toPure_4477_);
            crate::leanh::lean_closure_set(v___f_4485_, 1, v_recur_4478_);
            crate::leanh::lean_closure_set(v___f_4485_, 2, v_it_4483_);
            v___x_4486_ = crate::leanh::lean_apply_3(
                v___y_4479_,
                v_out_4484_,
                crate::leanh::lean_box(0),
                v_acc_4480_,
            );
            v___x_4487_ = crate::leanh::lean_apply_4(
                v_toBind_4481_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_4486_,
                v___f_4485_,
            );
            return v___x_4487_;
        }
        1 => {
            let mut v_it_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_4481_);
            crate::leanh::lean_dec(v___y_4479_);
            crate::leanh::lean_dec(v_toPure_4477_);
            v_it_4488_ = crate::leanh::lean_ctor_get(v_s_4482_, 0);
            crate::leanh::lean_inc(v_it_4488_);
            crate::leanh::lean_dec_ref_known(v_s_4482_, 1);
            v___x_4489_ = crate::leanh::lean_apply_4(
                v_recur_4478_,
                v_it_4488_,
                v_acc_4480_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_4489_;
        }
        _ => {
            let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_4481_);
            crate::leanh::lean_dec(v___y_4479_);
            crate::leanh::lean_dec(v_recur_4478_);
            v___x_4490_ =
                crate::leanh::lean_apply_2(v_toPure_4477_, crate::leanh::lean_box(0), v_acc_4480_);
            return v___x_4490_;
        }
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(
    mut v_toPure_4491_: *mut crate::leanh::LeanObject,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
    mut v_toBind_4493_: *mut crate::leanh::LeanObject,
    mut v_inst_4494_: *mut crate::leanh::LeanObject,
    mut v_s_4495_: *mut crate::leanh::LeanObject,
    mut v_lift_4496_: *mut crate::leanh::LeanObject,
    mut v_it_4497_: *mut crate::leanh::LeanObject,
    mut v_acc_4498_: *mut crate::leanh::LeanObject,
    mut v_hP_4499_: *mut crate::leanh::LeanObject,
    mut v_recur_4500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v_endPos_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_unused_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4541_: u8 = 0;
    let mut v_str_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4501_ = crate::leanh::lean_alloc_closure(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                crate::leanh::lean_closure_set(v___f_4501_, 0, v_toPure_4491_);
                crate::leanh::lean_closure_set(v___f_4501_, 1, v_recur_4500_);
                crate::leanh::lean_closure_set(v___f_4501_, 2, v___y_4492_);
                crate::leanh::lean_closure_set(v___f_4501_, 3, v_acc_4498_);
                crate::leanh::lean_closure_set(v___f_4501_, 4, v_toBind_4493_);
                if crate::leanh::lean_obj_tag(v_it_4497_) == 0 {
                    v_currPos_4502_ = crate::leanh::lean_ctor_get(v_it_4497_, 0);
                    v_searcher_4503_ = crate::leanh::lean_ctor_get(v_it_4497_, 1);
                    v_isSharedCheck_4560_ = (!crate::leanh::lean_is_exclusive(v_it_4497_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4505_ = v_it_4497_;
                        v_isShared_4506_ = v_isSharedCheck_4560_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_4503_);
                        crate::leanh::lean_inc(v_currPos_4502_);
                        crate::leanh::lean_dec(v_it_4497_);
                        v___x_4505_ = crate::leanh::lean_box(0);
                        v_isShared_4506_ = v_isSharedCheck_4560_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_4495_);
                    crate::leanh::lean_dec(v_inst_4494_);
                    v___x_4561_ = crate::leanh::lean_box(2);
                    v___x_4562_ = crate::leanh::lean_apply_4(
                        v_lift_4496_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_4501_,
                        v___x_4561_,
                    );
                    return v___x_4562_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_4495_);
                v___x_4507_ = crate::leanh::lean_apply_2(v_inst_4494_, v_s_4495_, v_searcher_4503_);
                match crate::leanh::lean_obj_tag(v___x_4507_) {
                    0 => {
                        v_out_4508_ = crate::leanh::lean_ctor_get(v___x_4507_, 1);
                        crate::leanh::lean_inc(v_out_4508_);
                        if crate::leanh::lean_obj_tag(v_out_4508_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_4508_, 2);
                            crate::leanh::lean_dec_ref(v_s_4495_);
                            v_it_4509_ = crate::leanh::lean_ctor_get(v___x_4507_, 0);
                            crate::leanh::lean_inc(v_it_4509_);
                            crate::leanh::lean_dec_ref_known(v___x_4507_, 2);
                            if v_isShared_4506_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4505_, 1, v_it_4509_);
                                v___x_4511_ = v___x_4505_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4514_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4514_,
                                    0,
                                    v_currPos_4502_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_it_4509_);
                                v___x_4511_ = v_reuseFailAlloc_4514_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_4515_ = crate::leanh::lean_ctor_get(v___x_4507_, 0);
                            v_isSharedCheck_4528_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4507_)) as u8;
                            if v_isSharedCheck_4528_ == 0 {
                                v_unused_4529_ = crate::leanh::lean_ctor_get(v___x_4507_, 1);
                                crate::leanh::lean_dec(v_unused_4529_);
                                v___x_4517_ = v___x_4507_;
                                v_isShared_4518_ = v_isSharedCheck_4528_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_4515_);
                                crate::leanh::lean_dec(v___x_4507_);
                                v___x_4517_ = crate::leanh::lean_box(0);
                                v_isShared_4518_ = v_isSharedCheck_4528_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_4495_);
                        v_it_4530_ = crate::leanh::lean_ctor_get(v___x_4507_, 0);
                        v_isSharedCheck_4541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4507_)) as u8;
                        if v_isSharedCheck_4541_ == 0 {
                            v___x_4532_ = v___x_4507_;
                            v_isShared_4533_ = v_isSharedCheck_4541_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_4530_);
                            crate::leanh::lean_dec(v___x_4507_);
                            v___x_4532_ = crate::leanh::lean_box(0);
                            v_isShared_4533_ = v_isSharedCheck_4541_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_4505_);
                        v_str_4542_ = crate::leanh::lean_ctor_get(v_s_4495_, 0);
                        v_startInclusive_4543_ = crate::leanh::lean_ctor_get(v_s_4495_, 1);
                        v_endExclusive_4544_ = crate::leanh::lean_ctor_get(v_s_4495_, 2);
                        v_isSharedCheck_4559_ = (!crate::leanh::lean_is_exclusive(v_s_4495_)) as u8;
                        if v_isSharedCheck_4559_ == 0 {
                            v___x_4546_ = v_s_4495_;
                            v_isShared_4547_ = v_isSharedCheck_4559_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_endExclusive_4544_);
                            crate::leanh::lean_inc(v_startInclusive_4543_);
                            crate::leanh::lean_inc(v_str_4542_);
                            crate::leanh::lean_dec(v_s_4495_);
                            v___x_4546_ = crate::leanh::lean_box(0);
                            v_isShared_4547_ = v_isSharedCheck_4559_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                v___x_4513_ = crate::leanh::lean_apply_4(
                    v_lift_4496_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_4501_,
                    v___x_4512_,
                );
                return v___x_4513_;
            }
            3 => {
                v_endPos_4519_ = crate::leanh::lean_ctor_get(v_out_4508_, 1);
                crate::leanh::lean_inc(v_endPos_4519_);
                crate::leanh::lean_dec_ref_known(v_out_4508_, 2);
                v_slice_4520_ =
                    l_String_Slice_slice_x21(v_s_4495_, v_currPos_4502_, v_endPos_4519_);
                crate::leanh::lean_dec(v_currPos_4502_);
                if v_isShared_4506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4505_, 1, v_it_4515_);
                    crate::leanh::lean_ctor_set(v___x_4505_, 0, v_endPos_4519_);
                    v_nextIt_4522_ = v___x_4505_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_endPos_4519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_it_4515_);
                    v_nextIt_4522_ = v_reuseFailAlloc_4527_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4517_, 1, v_slice_4520_);
                    crate::leanh::lean_ctor_set(v___x_4517_, 0, v_nextIt_4522_);
                    v___x_4524_ = v___x_4517_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_nextIt_4522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_slice_4520_);
                    v___x_4524_ = v_reuseFailAlloc_4526_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4525_ = crate::leanh::lean_apply_4(
                    v_lift_4496_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_4501_,
                    v___x_4524_,
                );
                return v___x_4525_;
            }
            6 => {
                if v_isShared_4506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4505_, 1, v_it_4530_);
                    v___x_4535_ = v___x_4505_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_currPos_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4540_, 1, v_it_4530_);
                    v___x_4535_ = v_reuseFailAlloc_4540_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4532_, 0, v___x_4535_);
                    v___x_4537_ = v___x_4532_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4535_);
                    v___x_4537_ = v_reuseFailAlloc_4539_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4538_ = crate::leanh::lean_apply_4(
                    v_lift_4496_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_4501_,
                    v___x_4537_,
                );
                return v___x_4538_;
            }
            9 => {
                v___x_4548_ = lean_nat_sub(v_endExclusive_4544_, v_startInclusive_4543_);
                v___x_4549_ = lean_nat_dec_eq(v_currPos_4502_, v___x_4548_);
                crate::leanh::lean_dec(v___x_4548_);
                if v___x_4549_ == 0 {
                    v___x_4550_ = lean_nat_add(v_startInclusive_4543_, v_currPos_4502_);
                    crate::leanh::lean_dec(v_currPos_4502_);
                    crate::leanh::lean_dec(v_startInclusive_4543_);
                    if v_isShared_4547_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4546_, 1, v___x_4550_);
                        v_slice_4552_ = v___x_4546_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_str_4542_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 1, v___x_4550_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_4556_,
                            2,
                            v_endExclusive_4544_,
                        );
                        v_slice_4552_ = v_reuseFailAlloc_4556_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4546_);
                    crate::leanh::lean_dec(v_endExclusive_4544_);
                    crate::leanh::lean_dec(v_startInclusive_4543_);
                    crate::leanh::lean_dec_ref(v_str_4542_);
                    crate::leanh::lean_dec(v_currPos_4502_);
                    v___x_4557_ = crate::leanh::lean_box(2);
                    v___x_4558_ = crate::leanh::lean_apply_4(
                        v_lift_4496_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_4501_,
                        v___x_4557_,
                    );
                    return v___x_4558_;
                }
            }
            10 => {
                v___x_4553_ = crate::leanh::lean_box(1);
                v___x_4554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4554_, 0, v___x_4553_);
                crate::leanh::lean_ctor_set(v___x_4554_, 1, v_slice_4552_);
                v___x_4555_ = crate::leanh::lean_apply_4(
                    v_lift_4496_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_4501_,
                    v___x_4554_,
                );
                return v___x_4555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(
    mut v_inst_4563_: *mut crate::leanh::LeanObject,
    mut v_inst_4564_: *mut crate::leanh::LeanObject,
    mut v_s_4565_: *mut crate::leanh::LeanObject,
    mut v_lift_4566_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_4567_: *mut crate::leanh::LeanObject,
    mut v_Pl_4568_: *mut crate::leanh::LeanObject,
    mut v_it_4569_: *mut crate::leanh::LeanObject,
    mut v_init_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4572_ = crate::leanh::lean_ctor_get(v_inst_4563_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4572_);
    v_toBind_4573_ = crate::leanh::lean_ctor_get(v_inst_4563_, 1);
    crate::leanh::lean_inc(v_toBind_4573_);
    crate::leanh::lean_dec_ref(v_inst_4563_);
    v_toPure_4574_ = crate::leanh::lean_ctor_get(v_toApplicative_4572_, 1);
    crate::leanh::lean_inc(v_toPure_4574_);
    crate::leanh::lean_dec_ref(v_toApplicative_4572_);
    v___f_4575_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4575_, 0, v_toPure_4574_);
    crate::leanh::lean_closure_set(v___f_4575_, 1, v___y_4571_);
    crate::leanh::lean_closure_set(v___f_4575_, 2, v_toBind_4573_);
    crate::leanh::lean_closure_set(v___f_4575_, 3, v_inst_4564_);
    crate::leanh::lean_closure_set(v___f_4575_, 4, v_s_4565_);
    crate::leanh::lean_closure_set(v___f_4575_, 5, v_lift_4566_);
    v___x_4576_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_4575_,
        v_it_4569_,
        v_init_4570_,
        crate::leanh::lean_box(0),
    );
    return v___x_4576_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(
    mut v_inst_4577_: *mut crate::leanh::LeanObject,
    mut v_inst_4578_: *mut crate::leanh::LeanObject,
    mut v_s_4579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4580_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4580_, 0, v_inst_4578_);
    crate::leanh::lean_closure_set(v___f_4580_, 1, v_inst_4577_);
    crate::leanh::lean_closure_set(v___f_4580_, 2, v_s_4579_);
    return v___f_4580_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(
    mut v_00_u03c1_4581_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4582_: *mut crate::leanh::LeanObject,
    mut v_inst_4583_: *mut crate::leanh::LeanObject,
    mut v_pat_4584_: *mut crate::leanh::LeanObject,
    mut v_inst_4585_: *mut crate::leanh::LeanObject,
    mut v_n_4586_: *mut crate::leanh::LeanObject,
    mut v_inst_4587_: *mut crate::leanh::LeanObject,
    mut v_s_4588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4589_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4589_, 0, v_inst_4587_);
    crate::leanh::lean_closure_set(v___f_4589_, 1, v_inst_4583_);
    crate::leanh::lean_closure_set(v___f_4589_, 2, v_s_4588_);
    return v___f_4589_;
}
pub unsafe fn l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(
    mut v_00_u03c1_4590_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4591_: *mut crate::leanh::LeanObject,
    mut v_inst_4592_: *mut crate::leanh::LeanObject,
    mut v_pat_4593_: *mut crate::leanh::LeanObject,
    mut v_inst_4594_: *mut crate::leanh::LeanObject,
    mut v_n_4595_: *mut crate::leanh::LeanObject,
    mut v_inst_4596_: *mut crate::leanh::LeanObject,
    mut v_s_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4598_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(
        v_00_u03c1_4590_,
        v_00_u03c3_4591_,
        v_inst_4592_,
        v_pat_4593_,
        v_inst_4594_,
        v_n_4595_,
        v_inst_4596_,
        v_s_4597_,
    );
    crate::leanh::lean_dec(v_inst_4594_);
    crate::leanh::lean_dec(v_pat_4593_);
    return v_res_4598_;
}
pub unsafe fn l_String_Slice_splitInclusive___redArg(
    mut v_s_4599_: *mut crate::leanh::LeanObject,
    mut v_inst_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4602_ = crate::leanh::lean_apply_1(v_inst_4600_, v_s_4599_);
    v___x_4603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4603_, 0, v___x_4601_);
    crate::leanh::lean_ctor_set(v___x_4603_, 1, v___x_4602_);
    return v___x_4603_;
}
pub unsafe fn l_String_Slice_splitInclusive(
    mut v_00_u03c1_4604_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4605_: *mut crate::leanh::LeanObject,
    mut v_s_4606_: *mut crate::leanh::LeanObject,
    mut v_pat_4607_: *mut crate::leanh::LeanObject,
    mut v_inst_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_String_Slice_splitInclusive___redArg(v_s_4606_, v_inst_4608_);
    return v___x_4609_;
}
pub unsafe fn l_String_Slice_splitInclusive___boxed(
    mut v_00_u03c1_4610_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4611_: *mut crate::leanh::LeanObject,
    mut v_s_4612_: *mut crate::leanh::LeanObject,
    mut v_pat_4613_: *mut crate::leanh::LeanObject,
    mut v_inst_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4615_ = l_String_Slice_splitInclusive(
        v_00_u03c1_4610_,
        v_00_u03c3_4611_,
        v_s_4612_,
        v_pat_4613_,
        v_inst_4614_,
    );
    crate::leanh::lean_dec(v_pat_4613_);
    return v_res_4615_;
}
pub unsafe fn l_String_Slice_skipPrefix_x3f___redArg(
    mut v_s_4616_: *mut crate::leanh::LeanObject,
    mut v_inst_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipPrefix_x3f_4618_ = crate::leanh::lean_ctor_get(v_inst_4617_, 0);
    crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4618_);
    crate::leanh::lean_dec_ref(v_inst_4617_);
    v___x_4619_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4618_, v_s_4616_);
    return v___x_4619_;
}
pub unsafe fn l_String_Slice_skipPrefix_x3f(
    mut v_00_u03c1_4620_: *mut crate::leanh::LeanObject,
    mut v_s_4621_: *mut crate::leanh::LeanObject,
    mut v_pat_4622_: *mut crate::leanh::LeanObject,
    mut v_inst_4623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipPrefix_x3f_4624_ = crate::leanh::lean_ctor_get(v_inst_4623_, 0);
    crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4624_);
    crate::leanh::lean_dec_ref(v_inst_4623_);
    v___x_4625_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4624_, v_s_4621_);
    return v___x_4625_;
}
pub unsafe fn l_String_Slice_skipPrefix_x3f___boxed(
    mut v_00_u03c1_4626_: *mut crate::leanh::LeanObject,
    mut v_s_4627_: *mut crate::leanh::LeanObject,
    mut v_pat_4628_: *mut crate::leanh::LeanObject,
    mut v_inst_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ =
        l_String_Slice_skipPrefix_x3f(v_00_u03c1_4626_, v_s_4627_, v_pat_4628_, v_inst_4629_);
    crate::leanh::lean_dec(v_pat_4628_);
    return v_res_4630_;
}
pub unsafe fn l_String_Slice_Pos_skip_x3f___redArg(
    mut v_s_4631_: *mut crate::leanh::LeanObject,
    mut v_pos_4632_: *mut crate::leanh::LeanObject,
    mut v_inst_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4639_: u8 = 0;
    let mut v_skipPrefix_x3f_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4653_: u8 = 0;
    let mut v_reuseFailAlloc_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4634_ = crate::leanh::lean_ctor_get(v_s_4631_, 0);
                v_startInclusive_4635_ = crate::leanh::lean_ctor_get(v_s_4631_, 1);
                v_endExclusive_4636_ = crate::leanh::lean_ctor_get(v_s_4631_, 2);
                v_isSharedCheck_4655_ = (!crate::leanh::lean_is_exclusive(v_s_4631_)) as u8;
                if v_isSharedCheck_4655_ == 0 {
                    v___x_4638_ = v_s_4631_;
                    v_isShared_4639_ = v_isSharedCheck_4655_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_4636_);
                    crate::leanh::lean_inc(v_startInclusive_4635_);
                    crate::leanh::lean_inc(v_str_4634_);
                    crate::leanh::lean_dec(v_s_4631_);
                    v___x_4638_ = crate::leanh::lean_box(0);
                    v_isShared_4639_ = v_isSharedCheck_4655_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_skipPrefix_x3f_4640_ = crate::leanh::lean_ctor_get(v_inst_4633_, 0);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4640_);
                crate::leanh::lean_dec_ref(v_inst_4633_);
                v___x_4641_ = lean_nat_add(v_startInclusive_4635_, v_pos_4632_);
                crate::leanh::lean_dec(v_startInclusive_4635_);
                if v_isShared_4639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4638_, 1, v___x_4641_);
                    v___x_4643_ = v___x_4638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4654_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_str_4634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4654_, 1, v___x_4641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4654_, 2, v_endExclusive_4636_);
                    v___x_4643_ = v_reuseFailAlloc_4654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4644_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4640_, v___x_4643_);
                if crate::leanh::lean_obj_tag(v___x_4644_) == 0 {
                    return v___x_4644_;
                } else {
                    v_val_4645_ = crate::leanh::lean_ctor_get(v___x_4644_, 0);
                    v_isSharedCheck_4653_ = (!crate::leanh::lean_is_exclusive(v___x_4644_)) as u8;
                    if v_isSharedCheck_4653_ == 0 {
                        v___x_4647_ = v___x_4644_;
                        v_isShared_4648_ = v_isSharedCheck_4653_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4645_);
                        crate::leanh::lean_dec(v___x_4644_);
                        v___x_4647_ = crate::leanh::lean_box(0);
                        v_isShared_4648_ = v_isSharedCheck_4653_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4649_ = lean_nat_add(v_pos_4632_, v_val_4645_);
                crate::leanh::lean_dec(v_val_4645_);
                if v_isShared_4648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4647_, 0, v___x_4649_);
                    v___x_4651_ = v___x_4647_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
                    v___x_4651_ = v_reuseFailAlloc_4652_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skip_x3f___redArg___boxed(
    mut v_s_4656_: *mut crate::leanh::LeanObject,
    mut v_pos_4657_: *mut crate::leanh::LeanObject,
    mut v_inst_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_4656_, v_pos_4657_, v_inst_4658_);
    crate::leanh::lean_dec(v_pos_4657_);
    return v_res_4659_;
}
pub unsafe fn l_String_Slice_Pos_skip_x3f(
    mut v_00_u03c1_4660_: *mut crate::leanh::LeanObject,
    mut v_s_4661_: *mut crate::leanh::LeanObject,
    mut v_pos_4662_: *mut crate::leanh::LeanObject,
    mut v_pat_4663_: *mut crate::leanh::LeanObject,
    mut v_inst_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v_skipPrefix_x3f_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4679_: u8 = 0;
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4684_: u8 = 0;
    let mut v_reuseFailAlloc_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4665_ = crate::leanh::lean_ctor_get(v_s_4661_, 0);
                v_startInclusive_4666_ = crate::leanh::lean_ctor_get(v_s_4661_, 1);
                v_endExclusive_4667_ = crate::leanh::lean_ctor_get(v_s_4661_, 2);
                v_isSharedCheck_4686_ = (!crate::leanh::lean_is_exclusive(v_s_4661_)) as u8;
                if v_isSharedCheck_4686_ == 0 {
                    v___x_4669_ = v_s_4661_;
                    v_isShared_4670_ = v_isSharedCheck_4686_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_4667_);
                    crate::leanh::lean_inc(v_startInclusive_4666_);
                    crate::leanh::lean_inc(v_str_4665_);
                    crate::leanh::lean_dec(v_s_4661_);
                    v___x_4669_ = crate::leanh::lean_box(0);
                    v_isShared_4670_ = v_isSharedCheck_4686_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_skipPrefix_x3f_4671_ = crate::leanh::lean_ctor_get(v_inst_4664_, 0);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4671_);
                crate::leanh::lean_dec_ref(v_inst_4664_);
                v___x_4672_ = lean_nat_add(v_startInclusive_4666_, v_pos_4662_);
                crate::leanh::lean_dec(v_startInclusive_4666_);
                if v_isShared_4670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4669_, 1, v___x_4672_);
                    v___x_4674_ = v___x_4669_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_str_4665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_endExclusive_4667_);
                    v___x_4674_ = v_reuseFailAlloc_4685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4675_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4671_, v___x_4674_);
                if crate::leanh::lean_obj_tag(v___x_4675_) == 0 {
                    return v___x_4675_;
                } else {
                    v_val_4676_ = crate::leanh::lean_ctor_get(v___x_4675_, 0);
                    v_isSharedCheck_4684_ = (!crate::leanh::lean_is_exclusive(v___x_4675_)) as u8;
                    if v_isSharedCheck_4684_ == 0 {
                        v___x_4678_ = v___x_4675_;
                        v_isShared_4679_ = v_isSharedCheck_4684_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4676_);
                        crate::leanh::lean_dec(v___x_4675_);
                        v___x_4678_ = crate::leanh::lean_box(0);
                        v_isShared_4679_ = v_isSharedCheck_4684_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4680_ = lean_nat_add(v_pos_4662_, v_val_4676_);
                crate::leanh::lean_dec(v_val_4676_);
                if v_isShared_4679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4678_, 0, v___x_4680_);
                    v___x_4682_ = v___x_4678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
                    v___x_4682_ = v_reuseFailAlloc_4683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skip_x3f___boxed(
    mut v_00_u03c1_4687_: *mut crate::leanh::LeanObject,
    mut v_s_4688_: *mut crate::leanh::LeanObject,
    mut v_pos_4689_: *mut crate::leanh::LeanObject,
    mut v_pat_4690_: *mut crate::leanh::LeanObject,
    mut v_inst_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4692_ = l_String_Slice_Pos_skip_x3f(
        v_00_u03c1_4687_,
        v_s_4688_,
        v_pos_4689_,
        v_pat_4690_,
        v_inst_4691_,
    );
    crate::leanh::lean_dec(v_pat_4690_);
    crate::leanh::lean_dec(v_pos_4689_);
    return v_res_4692_;
}
pub unsafe fn l_String_Slice_dropPrefix_x3f___redArg(
    mut v_s_4693_: *mut crate::leanh::LeanObject,
    mut v_inst_4694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v_str_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4707_: u8 = 0;
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_isSharedCheck_4716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_4695_ = crate::leanh::lean_ctor_get(v_inst_4694_, 0);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4695_);
                crate::leanh::lean_dec_ref(v_inst_4694_);
                crate::leanh::lean_inc_ref(v_s_4693_);
                v___x_4696_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4695_, v_s_4693_);
                if crate::leanh::lean_obj_tag(v___x_4696_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_4693_);
                    v___x_4697_ = crate::leanh::lean_box(0);
                    return v___x_4697_;
                } else {
                    v_val_4698_ = crate::leanh::lean_ctor_get(v___x_4696_, 0);
                    v_isSharedCheck_4716_ = (!crate::leanh::lean_is_exclusive(v___x_4696_)) as u8;
                    if v_isSharedCheck_4716_ == 0 {
                        v___x_4700_ = v___x_4696_;
                        v_isShared_4701_ = v_isSharedCheck_4716_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4698_);
                        crate::leanh::lean_dec(v___x_4696_);
                        v___x_4700_ = crate::leanh::lean_box(0);
                        v_isShared_4701_ = v_isSharedCheck_4716_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_4702_ = crate::leanh::lean_ctor_get(v_s_4693_, 0);
                v_startInclusive_4703_ = crate::leanh::lean_ctor_get(v_s_4693_, 1);
                v_endExclusive_4704_ = crate::leanh::lean_ctor_get(v_s_4693_, 2);
                v_isSharedCheck_4715_ = (!crate::leanh::lean_is_exclusive(v_s_4693_)) as u8;
                if v_isSharedCheck_4715_ == 0 {
                    v___x_4706_ = v_s_4693_;
                    v_isShared_4707_ = v_isSharedCheck_4715_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_4704_);
                    crate::leanh::lean_inc(v_startInclusive_4703_);
                    crate::leanh::lean_inc(v_str_4702_);
                    crate::leanh::lean_dec(v_s_4693_);
                    v___x_4706_ = crate::leanh::lean_box(0);
                    v_isShared_4707_ = v_isSharedCheck_4715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4708_ = lean_nat_add(v_startInclusive_4703_, v_val_4698_);
                crate::leanh::lean_dec(v_val_4698_);
                crate::leanh::lean_dec(v_startInclusive_4703_);
                if v_isShared_4707_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4706_, 1, v___x_4708_);
                    v___x_4710_ = v___x_4706_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_str_4702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 2, v_endExclusive_4704_);
                    v___x_4710_ = v_reuseFailAlloc_4714_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4700_, 0, v___x_4710_);
                    v___x_4712_ = v___x_4700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropPrefix_x3f(
    mut v_00_u03c1_4717_: *mut crate::leanh::LeanObject,
    mut v_s_4718_: *mut crate::leanh::LeanObject,
    mut v_pat_4719_: *mut crate::leanh::LeanObject,
    mut v_inst_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v_str_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_4721_ = crate::leanh::lean_ctor_get(v_inst_4720_, 0);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4721_);
                crate::leanh::lean_dec_ref(v_inst_4720_);
                crate::leanh::lean_inc_ref(v_s_4718_);
                v___x_4722_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4721_, v_s_4718_);
                if crate::leanh::lean_obj_tag(v___x_4722_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_4718_);
                    v___x_4723_ = crate::leanh::lean_box(0);
                    return v___x_4723_;
                } else {
                    v_val_4724_ = crate::leanh::lean_ctor_get(v___x_4722_, 0);
                    v_isSharedCheck_4742_ = (!crate::leanh::lean_is_exclusive(v___x_4722_)) as u8;
                    if v_isSharedCheck_4742_ == 0 {
                        v___x_4726_ = v___x_4722_;
                        v_isShared_4727_ = v_isSharedCheck_4742_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4724_);
                        crate::leanh::lean_dec(v___x_4722_);
                        v___x_4726_ = crate::leanh::lean_box(0);
                        v_isShared_4727_ = v_isSharedCheck_4742_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_4728_ = crate::leanh::lean_ctor_get(v_s_4718_, 0);
                v_startInclusive_4729_ = crate::leanh::lean_ctor_get(v_s_4718_, 1);
                v_endExclusive_4730_ = crate::leanh::lean_ctor_get(v_s_4718_, 2);
                v_isSharedCheck_4741_ = (!crate::leanh::lean_is_exclusive(v_s_4718_)) as u8;
                if v_isSharedCheck_4741_ == 0 {
                    v___x_4732_ = v_s_4718_;
                    v_isShared_4733_ = v_isSharedCheck_4741_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_4730_);
                    crate::leanh::lean_inc(v_startInclusive_4729_);
                    crate::leanh::lean_inc(v_str_4728_);
                    crate::leanh::lean_dec(v_s_4718_);
                    v___x_4732_ = crate::leanh::lean_box(0);
                    v_isShared_4733_ = v_isSharedCheck_4741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4734_ = lean_nat_add(v_startInclusive_4729_, v_val_4724_);
                crate::leanh::lean_dec(v_val_4724_);
                crate::leanh::lean_dec(v_startInclusive_4729_);
                if v_isShared_4733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4732_, 1, v___x_4734_);
                    v___x_4736_ = v___x_4732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_str_4728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 1, v___x_4734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 2, v_endExclusive_4730_);
                    v___x_4736_ = v_reuseFailAlloc_4740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4726_, 0, v___x_4736_);
                    v___x_4738_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropPrefix_x3f___boxed(
    mut v_00_u03c1_4743_: *mut crate::leanh::LeanObject,
    mut v_s_4744_: *mut crate::leanh::LeanObject,
    mut v_pat_4745_: *mut crate::leanh::LeanObject,
    mut v_inst_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4747_ =
        l_String_Slice_dropPrefix_x3f(v_00_u03c1_4743_, v_s_4744_, v_pat_4745_, v_inst_4746_);
    crate::leanh::lean_dec(v_pat_4745_);
    return v_res_4747_;
}
pub unsafe fn l_String_Slice_dropPrefix___redArg(
    mut v_s_4748_: *mut crate::leanh::LeanObject,
    mut v_inst_4749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4758_: u8 = 0;
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_4750_ = crate::leanh::lean_ctor_get(v_inst_4749_, 0);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4750_);
                crate::leanh::lean_dec_ref(v_inst_4749_);
                crate::leanh::lean_inc_ref(v_s_4748_);
                v___x_4751_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4750_, v_s_4748_);
                if crate::leanh::lean_obj_tag(v___x_4751_) == 0 {
                    return v_s_4748_;
                } else {
                    v_val_4752_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                    crate::leanh::lean_inc(v_val_4752_);
                    crate::leanh::lean_dec_ref_known(v___x_4751_, 1);
                    v_str_4753_ = crate::leanh::lean_ctor_get(v_s_4748_, 0);
                    v_startInclusive_4754_ = crate::leanh::lean_ctor_get(v_s_4748_, 1);
                    v_endExclusive_4755_ = crate::leanh::lean_ctor_get(v_s_4748_, 2);
                    v_isSharedCheck_4763_ = (!crate::leanh::lean_is_exclusive(v_s_4748_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4757_ = v_s_4748_;
                        v_isShared_4758_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endExclusive_4755_);
                        crate::leanh::lean_inc(v_startInclusive_4754_);
                        crate::leanh::lean_inc(v_str_4753_);
                        crate::leanh::lean_dec(v_s_4748_);
                        v___x_4757_ = crate::leanh::lean_box(0);
                        v_isShared_4758_ = v_isSharedCheck_4763_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4759_ = lean_nat_add(v_startInclusive_4754_, v_val_4752_);
                crate::leanh::lean_dec(v_val_4752_);
                crate::leanh::lean_dec(v_startInclusive_4754_);
                if v_isShared_4758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4757_, 1, v___x_4759_);
                    v___x_4761_ = v___x_4757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_str_4753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_endExclusive_4755_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropPrefix(
    mut v_00_u03c1_4764_: *mut crate::leanh::LeanObject,
    mut v_s_4765_: *mut crate::leanh::LeanObject,
    mut v_pat_4766_: *mut crate::leanh::LeanObject,
    mut v_inst_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4768_ = l_String_Slice_dropPrefix___redArg(v_s_4765_, v_inst_4767_);
    return v___x_4768_;
}
pub unsafe fn l_String_Slice_dropPrefix___boxed(
    mut v_00_u03c1_4769_: *mut crate::leanh::LeanObject,
    mut v_s_4770_: *mut crate::leanh::LeanObject,
    mut v_pat_4771_: *mut crate::leanh::LeanObject,
    mut v_inst_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_String_Slice_dropPrefix(v_00_u03c1_4769_, v_s_4770_, v_pat_4771_, v_inst_4772_);
    crate::leanh::lean_dec(v_pat_4771_);
    return v_res_4773_;
}
pub unsafe fn l_String_Slice_replace___redArg___lam__0(
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_f_4776_: *mut crate::leanh::LeanObject,
    mut v_c_4777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = crate::leanh::lean_apply_1(v_f_4776_, v_c_4777_);
    return v___x_4778_;
}
pub unsafe fn l_String_Slice_replace___redArg___lam__1(
    mut v_s_4779_: *mut crate::leanh::LeanObject,
    mut v_inst_4780_: *mut crate::leanh::LeanObject,
    mut v_replacement_4781_: *mut crate::leanh::LeanObject,
    mut v_x1_4782_: *mut crate::leanh::LeanObject,
    mut v_x2_4783_: *mut crate::leanh::LeanObject,
    mut v_x3_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x1_4782_) == 0 {
        let mut v_startPos_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_replacement_4781_);
        crate::leanh::lean_dec_ref(v_inst_4780_);
        v_startPos_4785_ = crate::leanh::lean_ctor_get(v_x1_4782_, 0);
        v_endPos_4786_ = crate::leanh::lean_ctor_get(v_x1_4782_, 1);
        v___x_4787_ = l_String_Slice_slice_x21(v_s_4779_, v_startPos_4785_, v_endPos_4786_);
        v_str_4788_ = crate::leanh::lean_ctor_get(v___x_4787_, 0);
        crate::leanh::lean_inc_ref(v_str_4788_);
        v_startInclusive_4789_ = crate::leanh::lean_ctor_get(v___x_4787_, 1);
        crate::leanh::lean_inc(v_startInclusive_4789_);
        v_endExclusive_4790_ = crate::leanh::lean_ctor_get(v___x_4787_, 2);
        crate::leanh::lean_inc(v_endExclusive_4790_);
        crate::leanh::lean_dec_ref(v___x_4787_);
        v___x_4791_ =
            lean_string_utf8_extract(v_str_4788_, v_startInclusive_4789_, v_endExclusive_4790_);
        crate::leanh::lean_dec(v_endExclusive_4790_);
        crate::leanh::lean_dec(v_startInclusive_4789_);
        crate::leanh::lean_dec_ref(v_str_4788_);
        v___x_4792_ = lean_string_append(v_x3_4784_, v___x_4791_);
        crate::leanh::lean_dec_ref(v___x_4791_);
        v___x_4793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4793_, 0, v___x_4792_);
        return v___x_4793_;
    } else {
        let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_4779_);
        v___x_4794_ = crate::leanh::lean_apply_1(v_inst_4780_, v_replacement_4781_);
        v_str_4795_ = crate::leanh::lean_ctor_get(v___x_4794_, 0);
        crate::leanh::lean_inc_ref(v_str_4795_);
        v_startInclusive_4796_ = crate::leanh::lean_ctor_get(v___x_4794_, 1);
        crate::leanh::lean_inc(v_startInclusive_4796_);
        v_endExclusive_4797_ = crate::leanh::lean_ctor_get(v___x_4794_, 2);
        crate::leanh::lean_inc(v_endExclusive_4797_);
        crate::leanh::lean_dec_ref(v___x_4794_);
        v___x_4798_ =
            lean_string_utf8_extract(v_str_4795_, v_startInclusive_4796_, v_endExclusive_4797_);
        crate::leanh::lean_dec(v_endExclusive_4797_);
        crate::leanh::lean_dec(v_startInclusive_4796_);
        crate::leanh::lean_dec_ref(v_str_4795_);
        v___x_4799_ = lean_string_append(v_x3_4784_, v___x_4798_);
        crate::leanh::lean_dec_ref(v___x_4798_);
        v___x_4800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4800_, 0, v___x_4799_);
        return v___x_4800_;
    }
}
pub unsafe fn l_String_Slice_replace___redArg___lam__1___boxed(
    mut v_s_4801_: *mut crate::leanh::LeanObject,
    mut v_inst_4802_: *mut crate::leanh::LeanObject,
    mut v_replacement_4803_: *mut crate::leanh::LeanObject,
    mut v_x1_4804_: *mut crate::leanh::LeanObject,
    mut v_x2_4805_: *mut crate::leanh::LeanObject,
    mut v_x3_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ = l_String_Slice_replace___redArg___lam__1(
        v_s_4801_,
        v_inst_4802_,
        v_replacement_4803_,
        v_x1_4804_,
        v_x2_4805_,
        v_x3_4806_,
    );
    crate::leanh::lean_dec_ref(v_x1_4804_);
    return v_res_4807_;
}
pub unsafe fn l_String_Slice_replace___redArg(
    mut v_inst_4810_: *mut crate::leanh::LeanObject,
    mut v_inst_4811_: *mut crate::leanh::LeanObject,
    mut v_s_4812_: *mut crate::leanh::LeanObject,
    mut v_inst_4813_: *mut crate::leanh::LeanObject,
    mut v_replacement_4814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4815_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_s_4812_, 2);
    v___f_4816_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_replace___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4816_, 0, v_s_4812_);
    crate::leanh::lean_closure_set(v___f_4816_, 1, v_inst_4811_);
    crate::leanh::lean_closure_set(v___f_4816_, 2, v_replacement_4814_);
    v___x_4817_ = l_String_Slice_replace___redArg___closed__1;
    v___x_4818_ = crate::leanh::lean_apply_1(v_inst_4813_, v_s_4812_);
    v___x_4819_ = crate::leanh::lean_apply_7(
        v_inst_4810_,
        v_s_4812_,
        v___f_4815_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4818_,
        v___x_4817_,
        v___f_4816_,
    );
    return v___x_4819_;
}
pub unsafe fn l_String_Slice_replace(
    mut v_00_u03c1_4820_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4821_: *mut crate::leanh::LeanObject,
    mut v_inst_4822_: *mut crate::leanh::LeanObject,
    mut v_inst_4823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4824_: *mut crate::leanh::LeanObject,
    mut v_inst_4825_: *mut crate::leanh::LeanObject,
    mut v_s_4826_: *mut crate::leanh::LeanObject,
    mut v_pattern_4827_: *mut crate::leanh::LeanObject,
    mut v_inst_4828_: *mut crate::leanh::LeanObject,
    mut v_replacement_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4830_ = l_String_Slice_replace___redArg(
        v_inst_4823_,
        v_inst_4825_,
        v_s_4826_,
        v_inst_4828_,
        v_replacement_4829_,
    );
    return v___x_4830_;
}
pub unsafe fn l_String_Slice_replace___boxed(
    mut v_00_u03c1_4831_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4832_: *mut crate::leanh::LeanObject,
    mut v_inst_4833_: *mut crate::leanh::LeanObject,
    mut v_inst_4834_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4835_: *mut crate::leanh::LeanObject,
    mut v_inst_4836_: *mut crate::leanh::LeanObject,
    mut v_s_4837_: *mut crate::leanh::LeanObject,
    mut v_pattern_4838_: *mut crate::leanh::LeanObject,
    mut v_inst_4839_: *mut crate::leanh::LeanObject,
    mut v_replacement_4840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4841_ = l_String_Slice_replace(
        v_00_u03c1_4831_,
        v_00_u03c3_4832_,
        v_inst_4833_,
        v_inst_4834_,
        v_00_u03b1_4835_,
        v_inst_4836_,
        v_s_4837_,
        v_pattern_4838_,
        v_inst_4839_,
        v_replacement_4840_,
    );
    crate::leanh::lean_dec(v_pattern_4838_);
    crate::leanh::lean_dec(v_inst_4833_);
    return v_res_4841_;
}
pub unsafe fn l_String_Slice_drop(
    mut v_s_4842_: *mut crate::leanh::LeanObject,
    mut v_n_4843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_unused_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4844_ = crate::leanh::lean_ctor_get(v_s_4842_, 0);
                crate::leanh::lean_inc_ref(v_str_4844_);
                v_startInclusive_4845_ = crate::leanh::lean_ctor_get(v_s_4842_, 1);
                crate::leanh::lean_inc(v_startInclusive_4845_);
                v_endExclusive_4846_ = crate::leanh::lean_ctor_get(v_s_4842_, 2);
                crate::leanh::lean_inc(v_endExclusive_4846_);
                v___x_4847_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4848_ = l_String_Slice_Pos_nextn(v_s_4842_, v___x_4847_, v_n_4843_);
                v_isSharedCheck_4856_ = (!crate::leanh::lean_is_exclusive(v_s_4842_)) as u8;
                if v_isSharedCheck_4856_ == 0 {
                    v_unused_4857_ = crate::leanh::lean_ctor_get(v_s_4842_, 2);
                    crate::leanh::lean_dec(v_unused_4857_);
                    v_unused_4858_ = crate::leanh::lean_ctor_get(v_s_4842_, 1);
                    crate::leanh::lean_dec(v_unused_4858_);
                    v_unused_4859_ = crate::leanh::lean_ctor_get(v_s_4842_, 0);
                    crate::leanh::lean_dec(v_unused_4859_);
                    v___x_4850_ = v_s_4842_;
                    v_isShared_4851_ = v_isSharedCheck_4856_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4842_);
                    v___x_4850_ = crate::leanh::lean_box(0);
                    v_isShared_4851_ = v_isSharedCheck_4856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4852_ = lean_nat_add(v_startInclusive_4845_, v___x_4848_);
                crate::leanh::lean_dec(v___x_4848_);
                crate::leanh::lean_dec(v_startInclusive_4845_);
                if v_isShared_4851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4852_);
                    v___x_4854_ = v___x_4850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_str_4844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 1, v___x_4852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 2, v_endExclusive_4846_);
                    v___x_4854_ = v_reuseFailAlloc_4855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___redArg(
    mut v_s_4860_: *mut crate::leanh::LeanObject,
    mut v_pos_4861_: *mut crate::leanh::LeanObject,
    mut v_inst_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_skipPrefix_x3f_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4863_ = crate::leanh::lean_ctor_get(v_s_4860_, 0);
                v_startInclusive_4864_ = crate::leanh::lean_ctor_get(v_s_4860_, 1);
                v_endExclusive_4865_ = crate::leanh::lean_ctor_get(v_s_4860_, 2);
                v_skipPrefix_x3f_4866_ = crate::leanh::lean_ctor_get(v_inst_4862_, 0);
                v___x_4867_ = lean_nat_add(v_startInclusive_4864_, v_pos_4861_);
                crate::leanh::lean_inc(v_endExclusive_4865_);
                crate::leanh::lean_inc_ref(v_str_4863_);
                v___x_4868_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4868_, 0, v_str_4863_);
                crate::leanh::lean_ctor_set(v___x_4868_, 1, v___x_4867_);
                crate::leanh::lean_ctor_set(v___x_4868_, 2, v_endExclusive_4865_);
                crate::leanh::lean_inc_ref(v_skipPrefix_x3f_4866_);
                v___x_4869_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_4866_, v___x_4868_);
                if crate::leanh::lean_obj_tag(v___x_4869_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4862_);
                    return v_pos_4861_;
                } else {
                    v_val_4870_ = crate::leanh::lean_ctor_get(v___x_4869_, 0);
                    crate::leanh::lean_inc(v_val_4870_);
                    crate::leanh::lean_dec_ref_known(v___x_4869_, 1);
                    v___x_4871_ = lean_nat_add(v_pos_4861_, v_val_4870_);
                    crate::leanh::lean_dec(v_val_4870_);
                    v___x_4872_ = lean_nat_dec_lt(v_pos_4861_, v___x_4871_);
                    if v___x_4872_ == 0 {
                        crate::leanh::lean_dec(v___x_4871_);
                        crate::leanh::lean_dec_ref(v_inst_4862_);
                        return v_pos_4861_;
                    } else {
                        crate::leanh::lean_dec(v_pos_4861_);
                        v_pos_4861_ = v___x_4871_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___redArg___boxed(
    mut v_s_4874_: *mut crate::leanh::LeanObject,
    mut v_pos_4875_: *mut crate::leanh::LeanObject,
    mut v_inst_4876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4877_ = l_String_Slice_Pos_skipWhile___redArg(v_s_4874_, v_pos_4875_, v_inst_4876_);
    crate::leanh::lean_dec_ref(v_s_4874_);
    return v_res_4877_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile(
    mut v_00_u03c1_4878_: *mut crate::leanh::LeanObject,
    mut v_s_4879_: *mut crate::leanh::LeanObject,
    mut v_pos_4880_: *mut crate::leanh::LeanObject,
    mut v_pat_4881_: *mut crate::leanh::LeanObject,
    mut v_inst_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4883_ = l_String_Slice_Pos_skipWhile___redArg(v_s_4879_, v_pos_4880_, v_inst_4882_);
    return v___x_4883_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___boxed(
    mut v_00_u03c1_4884_: *mut crate::leanh::LeanObject,
    mut v_s_4885_: *mut crate::leanh::LeanObject,
    mut v_pos_4886_: *mut crate::leanh::LeanObject,
    mut v_pat_4887_: *mut crate::leanh::LeanObject,
    mut v_inst_4888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4889_ = l_String_Slice_Pos_skipWhile(
        v_00_u03c1_4884_,
        v_s_4885_,
        v_pos_4886_,
        v_pat_4887_,
        v_inst_4888_,
    );
    crate::leanh::lean_dec(v_pat_4887_);
    crate::leanh::lean_dec_ref(v_s_4885_);
    return v_res_4889_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(
    mut v_x_4890_: *mut crate::leanh::LeanObject,
    mut v_h__1_4891_: *mut crate::leanh::LeanObject,
    mut v_h__2_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4890_) == 0 {
        let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4891_);
        v___x_4893_ = crate::leanh::lean_box(0);
        v___x_4894_ = crate::leanh::lean_apply_1(v_h__2_4892_, v___x_4893_);
        return v___x_4894_;
    } else {
        let mut v_val_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4892_);
        v_val_4895_ = crate::leanh::lean_ctor_get(v_x_4890_, 0);
        crate::leanh::lean_inc(v_val_4895_);
        crate::leanh::lean_dec_ref_known(v_x_4890_, 1);
        v___x_4896_ = crate::leanh::lean_apply_1(v_h__1_4891_, v_val_4895_);
        return v___x_4896_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(
    mut v_s_4897_: *mut crate::leanh::LeanObject,
    mut v_motive_4898_: *mut crate::leanh::LeanObject,
    mut v_x_4899_: *mut crate::leanh::LeanObject,
    mut v_h__1_4900_: *mut crate::leanh::LeanObject,
    mut v_h__2_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4899_) == 0 {
        let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4900_);
        v___x_4902_ = crate::leanh::lean_box(0);
        v___x_4903_ = crate::leanh::lean_apply_1(v_h__2_4901_, v___x_4902_);
        return v___x_4903_;
    } else {
        let mut v_val_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4901_);
        v_val_4904_ = crate::leanh::lean_ctor_get(v_x_4899_, 0);
        crate::leanh::lean_inc(v_val_4904_);
        crate::leanh::lean_dec_ref_known(v_x_4899_, 1);
        v___x_4905_ = crate::leanh::lean_apply_1(v_h__1_4900_, v_val_4904_);
        return v___x_4905_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(
    mut v_s_4906_: *mut crate::leanh::LeanObject,
    mut v_motive_4907_: *mut crate::leanh::LeanObject,
    mut v_x_4908_: *mut crate::leanh::LeanObject,
    mut v_h__1_4909_: *mut crate::leanh::LeanObject,
    mut v_h__2_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ =
        l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(
            v_s_4906_,
            v_motive_4907_,
            v_x_4908_,
            v_h__1_4909_,
            v_h__2_4910_,
        );
    crate::leanh::lean_dec_ref(v_s_4906_);
    return v_res_4911_;
}
pub unsafe fn l_String_Slice_skipPrefixWhile___redArg(
    mut v_s_4912_: *mut crate::leanh::LeanObject,
    mut v_inst_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4915_ = l_String_Slice_Pos_skipWhile___redArg(v_s_4912_, v___x_4914_, v_inst_4913_);
    return v___x_4915_;
}
pub unsafe fn l_String_Slice_skipPrefixWhile___redArg___boxed(
    mut v_s_4916_: *mut crate::leanh::LeanObject,
    mut v_inst_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_String_Slice_skipPrefixWhile___redArg(v_s_4916_, v_inst_4917_);
    crate::leanh::lean_dec_ref(v_s_4916_);
    return v_res_4918_;
}
pub unsafe fn l_String_Slice_skipPrefixWhile(
    mut v_00_u03c1_4919_: *mut crate::leanh::LeanObject,
    mut v_s_4920_: *mut crate::leanh::LeanObject,
    mut v_pat_4921_: *mut crate::leanh::LeanObject,
    mut v_inst_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4924_ = l_String_Slice_Pos_skipWhile___redArg(v_s_4920_, v___x_4923_, v_inst_4922_);
    return v___x_4924_;
}
pub unsafe fn l_String_Slice_skipPrefixWhile___boxed(
    mut v_00_u03c1_4925_: *mut crate::leanh::LeanObject,
    mut v_s_4926_: *mut crate::leanh::LeanObject,
    mut v_pat_4927_: *mut crate::leanh::LeanObject,
    mut v_inst_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4929_ =
        l_String_Slice_skipPrefixWhile(v_00_u03c1_4925_, v_s_4926_, v_pat_4927_, v_inst_4928_);
    crate::leanh::lean_dec(v_pat_4927_);
    crate::leanh::lean_dec_ref(v_s_4926_);
    return v_res_4929_;
}
pub unsafe fn l_String_Slice_dropWhile___redArg(
    mut v_s_4930_: *mut crate::leanh::LeanObject,
    mut v_inst_4931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4944_: u8 = 0;
    let mut v_unused_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4932_ = crate::leanh::lean_ctor_get(v_s_4930_, 0);
                crate::leanh::lean_inc_ref(v_str_4932_);
                v_startInclusive_4933_ = crate::leanh::lean_ctor_get(v_s_4930_, 1);
                crate::leanh::lean_inc(v_startInclusive_4933_);
                v_endExclusive_4934_ = crate::leanh::lean_ctor_get(v_s_4930_, 2);
                crate::leanh::lean_inc(v_endExclusive_4934_);
                v___x_4935_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4936_ =
                    l_String_Slice_Pos_skipWhile___redArg(v_s_4930_, v___x_4935_, v_inst_4931_);
                v_isSharedCheck_4944_ = (!crate::leanh::lean_is_exclusive(v_s_4930_)) as u8;
                if v_isSharedCheck_4944_ == 0 {
                    v_unused_4945_ = crate::leanh::lean_ctor_get(v_s_4930_, 2);
                    crate::leanh::lean_dec(v_unused_4945_);
                    v_unused_4946_ = crate::leanh::lean_ctor_get(v_s_4930_, 1);
                    crate::leanh::lean_dec(v_unused_4946_);
                    v_unused_4947_ = crate::leanh::lean_ctor_get(v_s_4930_, 0);
                    crate::leanh::lean_dec(v_unused_4947_);
                    v___x_4938_ = v_s_4930_;
                    v_isShared_4939_ = v_isSharedCheck_4944_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4930_);
                    v___x_4938_ = crate::leanh::lean_box(0);
                    v_isShared_4939_ = v_isSharedCheck_4944_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4940_ = lean_nat_add(v_startInclusive_4933_, v___x_4936_);
                crate::leanh::lean_dec(v___x_4936_);
                crate::leanh::lean_dec(v_startInclusive_4933_);
                if v_isShared_4939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4938_, 1, v___x_4940_);
                    v___x_4942_ = v___x_4938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4943_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_str_4932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 1, v___x_4940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_endExclusive_4934_);
                    v___x_4942_ = v_reuseFailAlloc_4943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4942_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropWhile(
    mut v_00_u03c1_4948_: *mut crate::leanh::LeanObject,
    mut v_s_4949_: *mut crate::leanh::LeanObject,
    mut v_pat_4950_: *mut crate::leanh::LeanObject,
    mut v_inst_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4952_ = crate::leanh::lean_ctor_get(v_s_4949_, 0);
                crate::leanh::lean_inc_ref(v_str_4952_);
                v_startInclusive_4953_ = crate::leanh::lean_ctor_get(v_s_4949_, 1);
                crate::leanh::lean_inc(v_startInclusive_4953_);
                v_endExclusive_4954_ = crate::leanh::lean_ctor_get(v_s_4949_, 2);
                crate::leanh::lean_inc(v_endExclusive_4954_);
                v___x_4955_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4956_ =
                    l_String_Slice_Pos_skipWhile___redArg(v_s_4949_, v___x_4955_, v_inst_4951_);
                v_isSharedCheck_4964_ = (!crate::leanh::lean_is_exclusive(v_s_4949_)) as u8;
                if v_isSharedCheck_4964_ == 0 {
                    v_unused_4965_ = crate::leanh::lean_ctor_get(v_s_4949_, 2);
                    crate::leanh::lean_dec(v_unused_4965_);
                    v_unused_4966_ = crate::leanh::lean_ctor_get(v_s_4949_, 1);
                    crate::leanh::lean_dec(v_unused_4966_);
                    v_unused_4967_ = crate::leanh::lean_ctor_get(v_s_4949_, 0);
                    crate::leanh::lean_dec(v_unused_4967_);
                    v___x_4958_ = v_s_4949_;
                    v_isShared_4959_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4949_);
                    v___x_4958_ = crate::leanh::lean_box(0);
                    v_isShared_4959_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4960_ = lean_nat_add(v_startInclusive_4953_, v___x_4956_);
                crate::leanh::lean_dec(v___x_4956_);
                crate::leanh::lean_dec(v_startInclusive_4953_);
                if v_isShared_4959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4958_, 1, v___x_4960_);
                    v___x_4962_ = v___x_4958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_str_4952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___x_4960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 2, v_endExclusive_4954_);
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropWhile___boxed(
    mut v_00_u03c1_4968_: *mut crate::leanh::LeanObject,
    mut v_s_4969_: *mut crate::leanh::LeanObject,
    mut v_pat_4970_: *mut crate::leanh::LeanObject,
    mut v_inst_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4972_ = l_String_Slice_dropWhile(v_00_u03c1_4968_, v_s_4969_, v_pat_4970_, v_inst_4971_);
    crate::leanh::lean_dec(v_pat_4970_);
    return v_res_4972_;
}
pub unsafe fn _init_l_String_Slice_trimAsciiStart___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4974_ = l_String_Slice_trimAsciiStart___closed__0;
    v___x_4975_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_4974_);
    return v___x_4975_;
}
pub unsafe fn l_String_Slice_trimAsciiStart(
    mut v_s_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4985_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_unused_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4977_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_trimAsciiStart___closed__1),
                    core::ptr::addr_of_mut!(l_String_Slice_trimAsciiStart___closed__1_once),
                    _init_l_String_Slice_trimAsciiStart___closed__1,
                );
                v_str_4978_ = crate::leanh::lean_ctor_get(v_s_4976_, 0);
                crate::leanh::lean_inc_ref(v_str_4978_);
                v_startInclusive_4979_ = crate::leanh::lean_ctor_get(v_s_4976_, 1);
                crate::leanh::lean_inc(v_startInclusive_4979_);
                v_endExclusive_4980_ = crate::leanh::lean_ctor_get(v_s_4976_, 2);
                crate::leanh::lean_inc(v_endExclusive_4980_);
                v___x_4981_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4982_ =
                    l_String_Slice_Pos_skipWhile___redArg(v_s_4976_, v___x_4981_, v___x_4977_);
                v_isSharedCheck_4990_ = (!crate::leanh::lean_is_exclusive(v_s_4976_)) as u8;
                if v_isSharedCheck_4990_ == 0 {
                    v_unused_4991_ = crate::leanh::lean_ctor_get(v_s_4976_, 2);
                    crate::leanh::lean_dec(v_unused_4991_);
                    v_unused_4992_ = crate::leanh::lean_ctor_get(v_s_4976_, 1);
                    crate::leanh::lean_dec(v_unused_4992_);
                    v_unused_4993_ = crate::leanh::lean_ctor_get(v_s_4976_, 0);
                    crate::leanh::lean_dec(v_unused_4993_);
                    v___x_4984_ = v_s_4976_;
                    v_isShared_4985_ = v_isSharedCheck_4990_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4976_);
                    v___x_4984_ = crate::leanh::lean_box(0);
                    v_isShared_4985_ = v_isSharedCheck_4990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4986_ = lean_nat_add(v_startInclusive_4979_, v___x_4982_);
                crate::leanh::lean_dec(v___x_4982_);
                crate::leanh::lean_dec(v_startInclusive_4979_);
                if v_isShared_4985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4984_, 1, v___x_4986_);
                    v___x_4988_ = v___x_4984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_str_4978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v___x_4986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_endExclusive_4980_);
                    v___x_4988_ = v_reuseFailAlloc_4989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_take(
    mut v_s_4994_: *mut crate::leanh::LeanObject,
    mut v_n_4995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_unused_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_4996_ = crate::leanh::lean_ctor_get(v_s_4994_, 0);
                crate::leanh::lean_inc_ref(v_str_4996_);
                v_startInclusive_4997_ = crate::leanh::lean_ctor_get(v_s_4994_, 1);
                crate::leanh::lean_inc(v_startInclusive_4997_);
                v___x_4998_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4999_ = l_String_Slice_Pos_nextn(v_s_4994_, v___x_4998_, v_n_4995_);
                v_isSharedCheck_5007_ = (!crate::leanh::lean_is_exclusive(v_s_4994_)) as u8;
                if v_isSharedCheck_5007_ == 0 {
                    v_unused_5008_ = crate::leanh::lean_ctor_get(v_s_4994_, 2);
                    crate::leanh::lean_dec(v_unused_5008_);
                    v_unused_5009_ = crate::leanh::lean_ctor_get(v_s_4994_, 1);
                    crate::leanh::lean_dec(v_unused_5009_);
                    v_unused_5010_ = crate::leanh::lean_ctor_get(v_s_4994_, 0);
                    crate::leanh::lean_dec(v_unused_5010_);
                    v___x_5001_ = v_s_4994_;
                    v_isShared_5002_ = v_isSharedCheck_5007_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_4994_);
                    v___x_5001_ = crate::leanh::lean_box(0);
                    v_isShared_5002_ = v_isSharedCheck_5007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5003_ = lean_nat_add(v_startInclusive_4997_, v___x_4999_);
                crate::leanh::lean_dec(v___x_4999_);
                if v_isShared_5002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5001_, 2, v___x_5003_);
                    v___x_5005_ = v___x_5001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_str_4996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 1, v_startInclusive_4997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 2, v___x_5003_);
                    v___x_5005_ = v_reuseFailAlloc_5006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeWhile___redArg(
    mut v_s_5011_: *mut crate::leanh::LeanObject,
    mut v_inst_5012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5024_: u8 = 0;
    let mut v_unused_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5013_ = crate::leanh::lean_ctor_get(v_s_5011_, 0);
                crate::leanh::lean_inc_ref(v_str_5013_);
                v_startInclusive_5014_ = crate::leanh::lean_ctor_get(v_s_5011_, 1);
                crate::leanh::lean_inc(v_startInclusive_5014_);
                v___x_5015_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5016_ =
                    l_String_Slice_Pos_skipWhile___redArg(v_s_5011_, v___x_5015_, v_inst_5012_);
                v_isSharedCheck_5024_ = (!crate::leanh::lean_is_exclusive(v_s_5011_)) as u8;
                if v_isSharedCheck_5024_ == 0 {
                    v_unused_5025_ = crate::leanh::lean_ctor_get(v_s_5011_, 2);
                    crate::leanh::lean_dec(v_unused_5025_);
                    v_unused_5026_ = crate::leanh::lean_ctor_get(v_s_5011_, 1);
                    crate::leanh::lean_dec(v_unused_5026_);
                    v_unused_5027_ = crate::leanh::lean_ctor_get(v_s_5011_, 0);
                    crate::leanh::lean_dec(v_unused_5027_);
                    v___x_5018_ = v_s_5011_;
                    v_isShared_5019_ = v_isSharedCheck_5024_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_5011_);
                    v___x_5018_ = crate::leanh::lean_box(0);
                    v_isShared_5019_ = v_isSharedCheck_5024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5020_ = lean_nat_add(v_startInclusive_5014_, v___x_5016_);
                crate::leanh::lean_dec(v___x_5016_);
                if v_isShared_5019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5018_, 2, v___x_5020_);
                    v___x_5022_ = v___x_5018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_str_5013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_startInclusive_5014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 2, v___x_5020_);
                    v___x_5022_ = v_reuseFailAlloc_5023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeWhile(
    mut v_00_u03c1_5028_: *mut crate::leanh::LeanObject,
    mut v_s_5029_: *mut crate::leanh::LeanObject,
    mut v_pat_5030_: *mut crate::leanh::LeanObject,
    mut v_inst_5031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_unused_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5032_ = crate::leanh::lean_ctor_get(v_s_5029_, 0);
                crate::leanh::lean_inc_ref(v_str_5032_);
                v_startInclusive_5033_ = crate::leanh::lean_ctor_get(v_s_5029_, 1);
                crate::leanh::lean_inc(v_startInclusive_5033_);
                v___x_5034_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5035_ =
                    l_String_Slice_Pos_skipWhile___redArg(v_s_5029_, v___x_5034_, v_inst_5031_);
                v_isSharedCheck_5043_ = (!crate::leanh::lean_is_exclusive(v_s_5029_)) as u8;
                if v_isSharedCheck_5043_ == 0 {
                    v_unused_5044_ = crate::leanh::lean_ctor_get(v_s_5029_, 2);
                    crate::leanh::lean_dec(v_unused_5044_);
                    v_unused_5045_ = crate::leanh::lean_ctor_get(v_s_5029_, 1);
                    crate::leanh::lean_dec(v_unused_5045_);
                    v_unused_5046_ = crate::leanh::lean_ctor_get(v_s_5029_, 0);
                    crate::leanh::lean_dec(v_unused_5046_);
                    v___x_5037_ = v_s_5029_;
                    v_isShared_5038_ = v_isSharedCheck_5043_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_5029_);
                    v___x_5037_ = crate::leanh::lean_box(0);
                    v_isShared_5038_ = v_isSharedCheck_5043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5039_ = lean_nat_add(v_startInclusive_5033_, v___x_5035_);
                crate::leanh::lean_dec(v___x_5035_);
                if v_isShared_5038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5037_, 2, v___x_5039_);
                    v___x_5041_ = v___x_5037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5042_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_str_5032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 1, v_startInclusive_5033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 2, v___x_5039_);
                    v___x_5041_ = v_reuseFailAlloc_5042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeWhile___boxed(
    mut v_00_u03c1_5047_: *mut crate::leanh::LeanObject,
    mut v_s_5048_: *mut crate::leanh::LeanObject,
    mut v_pat_5049_: *mut crate::leanh::LeanObject,
    mut v_inst_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5051_ = l_String_Slice_takeWhile(v_00_u03c1_5047_, v_s_5048_, v_pat_5049_, v_inst_5050_);
    crate::leanh::lean_dec(v_pat_5049_);
    return v_res_5051_;
}
pub unsafe fn l_String_Slice_find_x3f___redArg___lam__1(
    mut v___x_5052_: *mut crate::leanh::LeanObject,
    mut v_x1_5053_: *mut crate::leanh::LeanObject,
    mut v_x2_5054_: *mut crate::leanh::LeanObject,
    mut v_x3_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x1_5053_) == 0 {
        let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5056_, 0, v___x_5052_);
        return v___x_5056_;
    } else {
        let mut v_startPos_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5052_);
        v_startPos_5057_ = crate::leanh::lean_ctor_get(v_x1_5053_, 0);
        crate::leanh::lean_inc(v_startPos_5057_);
        v___x_5058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5058_, 0, v_startPos_5057_);
        v___x_5059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5059_, 0, v___x_5058_);
        return v___x_5059_;
    }
}
pub unsafe fn l_String_Slice_find_x3f___redArg___lam__1___boxed(
    mut v___x_5060_: *mut crate::leanh::LeanObject,
    mut v_x1_5061_: *mut crate::leanh::LeanObject,
    mut v_x2_5062_: *mut crate::leanh::LeanObject,
    mut v_x3_5063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5064_ =
        l_String_Slice_find_x3f___redArg___lam__1(v___x_5060_, v_x1_5061_, v_x2_5062_, v_x3_5063_);
    crate::leanh::lean_dec(v_x3_5063_);
    crate::leanh::lean_dec_ref(v_x1_5061_);
    return v_res_5064_;
}
pub unsafe fn l_String_Slice_find_x3f___redArg(
    mut v_inst_5067_: *mut crate::leanh::LeanObject,
    mut v_s_5068_: *mut crate::leanh::LeanObject,
    mut v_inst_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5070_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_s_5068_);
    v_searcher_5071_ = crate::leanh::lean_apply_1(v_inst_5069_, v_s_5068_);
    v___x_5072_ = crate::leanh::lean_box(0);
    v___f_5073_ = l_String_Slice_find_x3f___redArg___closed__0;
    v___x_5074_ = crate::leanh::lean_apply_7(
        v_inst_5067_,
        v_s_5068_,
        v___f_5070_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_5071_,
        v___x_5072_,
        v___f_5073_,
    );
    return v___x_5074_;
}
pub unsafe fn l_String_Slice_find_x3f(
    mut v_00_u03c1_5075_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5076_: *mut crate::leanh::LeanObject,
    mut v_inst_5077_: *mut crate::leanh::LeanObject,
    mut v_inst_5078_: *mut crate::leanh::LeanObject,
    mut v_s_5079_: *mut crate::leanh::LeanObject,
    mut v_pat_5080_: *mut crate::leanh::LeanObject,
    mut v_inst_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5082_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_s_5079_);
    v_searcher_5083_ = crate::leanh::lean_apply_1(v_inst_5081_, v_s_5079_);
    v___x_5084_ = crate::leanh::lean_box(0);
    v___f_5085_ = l_String_Slice_find_x3f___redArg___closed__0;
    v___x_5086_ = crate::leanh::lean_apply_7(
        v_inst_5078_,
        v_s_5079_,
        v___f_5082_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_5083_,
        v___x_5084_,
        v___f_5085_,
    );
    return v___x_5086_;
}
pub unsafe fn l_String_Slice_find_x3f___boxed(
    mut v_00_u03c1_5087_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5088_: *mut crate::leanh::LeanObject,
    mut v_inst_5089_: *mut crate::leanh::LeanObject,
    mut v_inst_5090_: *mut crate::leanh::LeanObject,
    mut v_s_5091_: *mut crate::leanh::LeanObject,
    mut v_pat_5092_: *mut crate::leanh::LeanObject,
    mut v_inst_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_String_Slice_find_x3f(
        v_00_u03c1_5087_,
        v_00_u03c3_5088_,
        v_inst_5089_,
        v_inst_5090_,
        v_s_5091_,
        v_pat_5092_,
        v_inst_5093_,
    );
    crate::leanh::lean_dec(v_pat_5092_);
    crate::leanh::lean_dec(v_inst_5089_);
    return v_res_5094_;
}
pub unsafe fn l_String_Slice_find___redArg(
    mut v_inst_5095_: *mut crate::leanh::LeanObject,
    mut v_s_5096_: *mut crate::leanh::LeanObject,
    mut v_inst_5097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5098_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_s_5096_, 2);
    v_searcher_5099_ = crate::leanh::lean_apply_1(v_inst_5097_, v_s_5096_);
    v___x_5100_ = crate::leanh::lean_box(0);
    v___f_5101_ = l_String_Slice_find_x3f___redArg___closed__0;
    v___x_5102_ = crate::leanh::lean_apply_7(
        v_inst_5095_,
        v_s_5096_,
        v___f_5098_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_5099_,
        v___x_5100_,
        v___f_5101_,
    );
    if crate::leanh::lean_obj_tag(v___x_5102_) == 0 {
        let mut v_startInclusive_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_startInclusive_5103_ = crate::leanh::lean_ctor_get(v_s_5096_, 1);
        crate::leanh::lean_inc(v_startInclusive_5103_);
        v_endExclusive_5104_ = crate::leanh::lean_ctor_get(v_s_5096_, 2);
        crate::leanh::lean_inc(v_endExclusive_5104_);
        crate::leanh::lean_dec_ref(v_s_5096_);
        v___x_5105_ = lean_nat_sub(v_endExclusive_5104_, v_startInclusive_5103_);
        crate::leanh::lean_dec(v_startInclusive_5103_);
        crate::leanh::lean_dec(v_endExclusive_5104_);
        return v___x_5105_;
    } else {
        let mut v_val_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_5096_);
        v_val_5106_ = crate::leanh::lean_ctor_get(v___x_5102_, 0);
        crate::leanh::lean_inc(v_val_5106_);
        crate::leanh::lean_dec_ref_known(v___x_5102_, 1);
        return v_val_5106_;
    }
}
pub unsafe fn l_String_Slice_find(
    mut v_00_u03c1_5107_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5108_: *mut crate::leanh::LeanObject,
    mut v_inst_5109_: *mut crate::leanh::LeanObject,
    mut v_inst_5110_: *mut crate::leanh::LeanObject,
    mut v_s_5111_: *mut crate::leanh::LeanObject,
    mut v_pat_5112_: *mut crate::leanh::LeanObject,
    mut v_inst_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5114_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_s_5111_, 2);
    v_searcher_5115_ = crate::leanh::lean_apply_1(v_inst_5113_, v_s_5111_);
    v___x_5116_ = crate::leanh::lean_box(0);
    v___f_5117_ = l_String_Slice_find_x3f___redArg___closed__0;
    v___x_5118_ = crate::leanh::lean_apply_7(
        v_inst_5110_,
        v_s_5111_,
        v___f_5114_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_5115_,
        v___x_5116_,
        v___f_5117_,
    );
    if crate::leanh::lean_obj_tag(v___x_5118_) == 0 {
        let mut v_startInclusive_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_startInclusive_5119_ = crate::leanh::lean_ctor_get(v_s_5111_, 1);
        crate::leanh::lean_inc(v_startInclusive_5119_);
        v_endExclusive_5120_ = crate::leanh::lean_ctor_get(v_s_5111_, 2);
        crate::leanh::lean_inc(v_endExclusive_5120_);
        crate::leanh::lean_dec_ref(v_s_5111_);
        v___x_5121_ = lean_nat_sub(v_endExclusive_5120_, v_startInclusive_5119_);
        crate::leanh::lean_dec(v_startInclusive_5119_);
        crate::leanh::lean_dec(v_endExclusive_5120_);
        return v___x_5121_;
    } else {
        let mut v_val_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_5111_);
        v_val_5122_ = crate::leanh::lean_ctor_get(v___x_5118_, 0);
        crate::leanh::lean_inc(v_val_5122_);
        crate::leanh::lean_dec_ref_known(v___x_5118_, 1);
        return v_val_5122_;
    }
}
pub unsafe fn l_String_Slice_find___boxed(
    mut v_00_u03c1_5123_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5124_: *mut crate::leanh::LeanObject,
    mut v_inst_5125_: *mut crate::leanh::LeanObject,
    mut v_inst_5126_: *mut crate::leanh::LeanObject,
    mut v_s_5127_: *mut crate::leanh::LeanObject,
    mut v_pat_5128_: *mut crate::leanh::LeanObject,
    mut v_inst_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_String_Slice_find(
        v_00_u03c1_5123_,
        v_00_u03c3_5124_,
        v_inst_5125_,
        v_inst_5126_,
        v_s_5127_,
        v_pat_5128_,
        v_inst_5129_,
    );
    crate::leanh::lean_dec(v_pat_5128_);
    crate::leanh::lean_dec(v_inst_5125_);
    return v_res_5130_;
}
pub unsafe fn l_String_Slice_contains___redArg___lam__1(
    mut v___x_5134_: u8,
    mut v_x1_5135_: *mut crate::leanh::LeanObject,
    mut v_x2_5136_: *mut crate::leanh::LeanObject,
    mut v_x3_5137_: u8,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x1_5135_) == 1 {
        let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5138_ = l_String_Slice_contains___redArg___lam__1___closed__0;
        return v___x_5138_;
    } else {
        let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5139_ = crate::leanh::lean_box((v___x_5134_) as usize);
        v___x_5140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5140_, 0, v___x_5139_);
        return v___x_5140_;
    }
}
pub unsafe fn l_String_Slice_contains___redArg___lam__1___boxed(
    mut v___x_5141_: *mut crate::leanh::LeanObject,
    mut v_x1_5142_: *mut crate::leanh::LeanObject,
    mut v_x2_5143_: *mut crate::leanh::LeanObject,
    mut v_x3_5144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_86__boxed_5145_: u8 = 0;
    let mut v_x3_89__boxed_5146_: u8 = 0;
    let mut v_res_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_86__boxed_5145_ = (crate::leanh::lean_unbox(v___x_5141_) as u8);
    v_x3_89__boxed_5146_ = (crate::leanh::lean_unbox(v_x3_5144_) as u8);
    v_res_5147_ = l_String_Slice_contains___redArg___lam__1(
        v___x_86__boxed_5145_,
        v_x1_5142_,
        v_x2_5143_,
        v_x3_89__boxed_5146_,
    );
    crate::leanh::lean_dec_ref(v_x1_5142_);
    return v_res_5147_;
}
pub unsafe fn l_String_Slice_contains___redArg(
    mut v_inst_5151_: *mut crate::leanh::LeanObject,
    mut v_s_5152_: *mut crate::leanh::LeanObject,
    mut v_inst_5153_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: u8 = 0;
    let mut v___f_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u8 = 0;
    v___f_5154_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_s_5152_);
    v_searcher_5155_ = crate::leanh::lean_apply_1(v_inst_5153_, v_s_5152_);
    v___x_5156_ = 0;
    v___f_5157_ = l_String_Slice_contains___redArg___closed__0;
    v___x_5158_ = crate::leanh::lean_box((v___x_5156_) as usize);
    v___x_5159_ = crate::leanh::lean_apply_7(
        v_inst_5151_,
        v_s_5152_,
        v___f_5154_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_5155_,
        v___x_5158_,
        v___f_5157_,
    );
    v___x_5160_ = (crate::leanh::lean_unbox(v___x_5159_) as u8);
    return v___x_5160_;
}
pub unsafe fn l_String_Slice_contains___redArg___boxed(
    mut v_inst_5161_: *mut crate::leanh::LeanObject,
    mut v_s_5162_: *mut crate::leanh::LeanObject,
    mut v_inst_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5164_: u8 = 0;
    let mut v_r_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ = l_String_Slice_contains___redArg(v_inst_5161_, v_s_5162_, v_inst_5163_);
    v_r_5165_ = crate::leanh::lean_box((v_res_5164_) as usize);
    return v_r_5165_;
}
pub unsafe fn l_String_Slice_contains(
    mut v_00_u03c1_5166_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5167_: *mut crate::leanh::LeanObject,
    mut v_inst_5168_: *mut crate::leanh::LeanObject,
    mut v_inst_5169_: *mut crate::leanh::LeanObject,
    mut v_s_5170_: *mut crate::leanh::LeanObject,
    mut v_pat_5171_: *mut crate::leanh::LeanObject,
    mut v_inst_5172_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5173_: u8 = 0;
    v___x_5173_ = l_String_Slice_contains___redArg(v_inst_5169_, v_s_5170_, v_inst_5172_);
    return v___x_5173_;
}
pub unsafe fn l_String_Slice_contains___boxed(
    mut v_00_u03c1_5174_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5175_: *mut crate::leanh::LeanObject,
    mut v_inst_5176_: *mut crate::leanh::LeanObject,
    mut v_inst_5177_: *mut crate::leanh::LeanObject,
    mut v_s_5178_: *mut crate::leanh::LeanObject,
    mut v_pat_5179_: *mut crate::leanh::LeanObject,
    mut v_inst_5180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5181_: u8 = 0;
    let mut v_r_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5181_ = l_String_Slice_contains(
        v_00_u03c1_5174_,
        v_00_u03c3_5175_,
        v_inst_5176_,
        v_inst_5177_,
        v_s_5178_,
        v_pat_5179_,
        v_inst_5180_,
    );
    crate::leanh::lean_dec(v_pat_5179_);
    crate::leanh::lean_dec(v_inst_5176_);
    v_r_5182_ = crate::leanh::lean_box((v_res_5181_) as usize);
    return v_r_5182_;
}
pub unsafe fn l_String_Slice_any___redArg(
    mut v_inst_5183_: *mut crate::leanh::LeanObject,
    mut v_s_5184_: *mut crate::leanh::LeanObject,
    mut v_inst_5185_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5186_: u8 = 0;
    v___x_5186_ = l_String_Slice_contains___redArg(v_inst_5183_, v_s_5184_, v_inst_5185_);
    return v___x_5186_;
}
pub unsafe fn l_String_Slice_any___redArg___boxed(
    mut v_inst_5187_: *mut crate::leanh::LeanObject,
    mut v_s_5188_: *mut crate::leanh::LeanObject,
    mut v_inst_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5190_: u8 = 0;
    let mut v_r_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_String_Slice_any___redArg(v_inst_5187_, v_s_5188_, v_inst_5189_);
    v_r_5191_ = crate::leanh::lean_box((v_res_5190_) as usize);
    return v_r_5191_;
}
pub unsafe fn l_String_Slice_any(
    mut v_00_u03c1_5192_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5193_: *mut crate::leanh::LeanObject,
    mut v_inst_5194_: *mut crate::leanh::LeanObject,
    mut v_inst_5195_: *mut crate::leanh::LeanObject,
    mut v_s_5196_: *mut crate::leanh::LeanObject,
    mut v_pat_5197_: *mut crate::leanh::LeanObject,
    mut v_inst_5198_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5199_: u8 = 0;
    v___x_5199_ = l_String_Slice_contains___redArg(v_inst_5195_, v_s_5196_, v_inst_5198_);
    return v___x_5199_;
}
pub unsafe fn l_String_Slice_any___boxed(
    mut v_00_u03c1_5200_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5201_: *mut crate::leanh::LeanObject,
    mut v_inst_5202_: *mut crate::leanh::LeanObject,
    mut v_inst_5203_: *mut crate::leanh::LeanObject,
    mut v_s_5204_: *mut crate::leanh::LeanObject,
    mut v_pat_5205_: *mut crate::leanh::LeanObject,
    mut v_inst_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5207_: u8 = 0;
    let mut v_r_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5207_ = l_String_Slice_any(
        v_00_u03c1_5200_,
        v_00_u03c3_5201_,
        v_inst_5202_,
        v_inst_5203_,
        v_s_5204_,
        v_pat_5205_,
        v_inst_5206_,
    );
    crate::leanh::lean_dec(v_pat_5205_);
    crate::leanh::lean_dec(v_inst_5202_);
    v_r_5208_ = crate::leanh::lean_box((v_res_5207_) as usize);
    return v_r_5208_;
}
pub unsafe fn l_String_Slice_all___redArg(
    mut v_s_5209_: *mut crate::leanh::LeanObject,
    mut v_inst_5210_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: u8 = 0;
    v_startInclusive_5211_ = crate::leanh::lean_ctor_get(v_s_5209_, 1);
    v_endExclusive_5212_ = crate::leanh::lean_ctor_get(v_s_5209_, 2);
    v___x_5213_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5214_ = l_String_Slice_Pos_skipWhile___redArg(v_s_5209_, v___x_5213_, v_inst_5210_);
    v___x_5215_ = lean_nat_sub(v_endExclusive_5212_, v_startInclusive_5211_);
    v___x_5216_ = lean_nat_dec_eq(v___x_5214_, v___x_5215_);
    crate::leanh::lean_dec(v___x_5215_);
    crate::leanh::lean_dec(v___x_5214_);
    return v___x_5216_;
}
pub unsafe fn l_String_Slice_all___redArg___boxed(
    mut v_s_5217_: *mut crate::leanh::LeanObject,
    mut v_inst_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5219_: u8 = 0;
    let mut v_r_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5219_ = l_String_Slice_all___redArg(v_s_5217_, v_inst_5218_);
    crate::leanh::lean_dec_ref(v_s_5217_);
    v_r_5220_ = crate::leanh::lean_box((v_res_5219_) as usize);
    return v_r_5220_;
}
pub unsafe fn l_String_Slice_all(
    mut v_00_u03c1_5221_: *mut crate::leanh::LeanObject,
    mut v_s_5222_: *mut crate::leanh::LeanObject,
    mut v_pat_5223_: *mut crate::leanh::LeanObject,
    mut v_inst_5224_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    v_startInclusive_5225_ = crate::leanh::lean_ctor_get(v_s_5222_, 1);
    v_endExclusive_5226_ = crate::leanh::lean_ctor_get(v_s_5222_, 2);
    v___x_5227_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5228_ = l_String_Slice_Pos_skipWhile___redArg(v_s_5222_, v___x_5227_, v_inst_5224_);
    v___x_5229_ = lean_nat_sub(v_endExclusive_5226_, v_startInclusive_5225_);
    v___x_5230_ = lean_nat_dec_eq(v___x_5228_, v___x_5229_);
    crate::leanh::lean_dec(v___x_5229_);
    crate::leanh::lean_dec(v___x_5228_);
    return v___x_5230_;
}
pub unsafe fn l_String_Slice_all___boxed(
    mut v_00_u03c1_5231_: *mut crate::leanh::LeanObject,
    mut v_s_5232_: *mut crate::leanh::LeanObject,
    mut v_pat_5233_: *mut crate::leanh::LeanObject,
    mut v_inst_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5235_: u8 = 0;
    let mut v_r_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5235_ = l_String_Slice_all(v_00_u03c1_5231_, v_s_5232_, v_pat_5233_, v_inst_5234_);
    crate::leanh::lean_dec(v_pat_5233_);
    crate::leanh::lean_dec_ref(v_s_5232_);
    v_r_5236_ = crate::leanh::lean_box((v_res_5235_) as usize);
    return v_r_5236_;
}
pub unsafe fn l_String_Slice_endsWith___redArg(
    mut v_s_5237_: *mut crate::leanh::LeanObject,
    mut v_inst_5238_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_endsWith_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    v_endsWith_5239_ = crate::leanh::lean_ctor_get(v_inst_5238_, 2);
    crate::leanh::lean_inc_ref(v_endsWith_5239_);
    crate::leanh::lean_dec_ref(v_inst_5238_);
    v___x_5240_ = crate::leanh::lean_apply_1(v_endsWith_5239_, v_s_5237_);
    v___x_5241_ = (crate::leanh::lean_unbox(v___x_5240_) as u8);
    return v___x_5241_;
}
pub unsafe fn l_String_Slice_endsWith___redArg___boxed(
    mut v_s_5242_: *mut crate::leanh::LeanObject,
    mut v_inst_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5244_: u8 = 0;
    let mut v_r_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_String_Slice_endsWith___redArg(v_s_5242_, v_inst_5243_);
    v_r_5245_ = crate::leanh::lean_box((v_res_5244_) as usize);
    return v_r_5245_;
}
pub unsafe fn l_String_Slice_endsWith(
    mut v_00_u03c1_5246_: *mut crate::leanh::LeanObject,
    mut v_s_5247_: *mut crate::leanh::LeanObject,
    mut v_pat_5248_: *mut crate::leanh::LeanObject,
    mut v_inst_5249_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_endsWith_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    v_endsWith_5250_ = crate::leanh::lean_ctor_get(v_inst_5249_, 2);
    crate::leanh::lean_inc_ref(v_endsWith_5250_);
    crate::leanh::lean_dec_ref(v_inst_5249_);
    v___x_5251_ = crate::leanh::lean_apply_1(v_endsWith_5250_, v_s_5247_);
    v___x_5252_ = (crate::leanh::lean_unbox(v___x_5251_) as u8);
    return v___x_5252_;
}
pub unsafe fn l_String_Slice_endsWith___boxed(
    mut v_00_u03c1_5253_: *mut crate::leanh::LeanObject,
    mut v_s_5254_: *mut crate::leanh::LeanObject,
    mut v_pat_5255_: *mut crate::leanh::LeanObject,
    mut v_inst_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5257_: u8 = 0;
    let mut v_r_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5257_ = l_String_Slice_endsWith(v_00_u03c1_5253_, v_s_5254_, v_pat_5255_, v_inst_5256_);
    crate::leanh::lean_dec(v_pat_5255_);
    v_r_5258_ = crate::leanh::lean_box((v_res_5257_) as usize);
    return v_r_5258_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorIdx___redArg(
    mut v_x_5259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5259_) == 0 {
        let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5260_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5260_;
    } else {
        let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5261_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_5261_;
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(
    mut v_x_5262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5263_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_5262_);
    crate::leanh::lean_dec(v_x_5262_);
    return v_res_5263_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorIdx(
    mut v_00_u03c3_5264_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5265_: *mut crate::leanh::LeanObject,
    mut v_pat_5266_: *mut crate::leanh::LeanObject,
    mut v_s_5267_: *mut crate::leanh::LeanObject,
    mut v_inst_5268_: *mut crate::leanh::LeanObject,
    mut v_x_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_5269_);
    return v___x_5270_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorIdx___boxed(
    mut v_00_u03c3_5271_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5272_: *mut crate::leanh::LeanObject,
    mut v_pat_5273_: *mut crate::leanh::LeanObject,
    mut v_s_5274_: *mut crate::leanh::LeanObject,
    mut v_inst_5275_: *mut crate::leanh::LeanObject,
    mut v_x_5276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5277_ = l_String_Slice_RevSplitIterator_ctorIdx(
        v_00_u03c3_5271_,
        v_00_u03c1_5272_,
        v_pat_5273_,
        v_s_5274_,
        v_inst_5275_,
        v_x_5276_,
    );
    crate::leanh::lean_dec(v_x_5276_);
    crate::leanh::lean_dec(v_inst_5275_);
    crate::leanh::lean_dec_ref(v_s_5274_);
    crate::leanh::lean_dec(v_pat_5273_);
    return v_res_5277_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorElim___redArg(
    mut v_t_5278_: *mut crate::leanh::LeanObject,
    mut v_k_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5278_) == 0 {
        let mut v_currPos_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_currPos_5280_ = crate::leanh::lean_ctor_get(v_t_5278_, 0);
        crate::leanh::lean_inc(v_currPos_5280_);
        v_searcher_5281_ = crate::leanh::lean_ctor_get(v_t_5278_, 1);
        crate::leanh::lean_inc(v_searcher_5281_);
        crate::leanh::lean_dec_ref_known(v_t_5278_, 2);
        v___x_5282_ = crate::leanh::lean_apply_2(v_k_5279_, v_currPos_5280_, v_searcher_5281_);
        return v___x_5282_;
    } else {
        return v_k_5279_;
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorElim(
    mut v_00_u03c3_5283_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5284_: *mut crate::leanh::LeanObject,
    mut v_pat_5285_: *mut crate::leanh::LeanObject,
    mut v_s_5286_: *mut crate::leanh::LeanObject,
    mut v_inst_5287_: *mut crate::leanh::LeanObject,
    mut v_motive_5288_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5289_: *mut crate::leanh::LeanObject,
    mut v_t_5290_: *mut crate::leanh::LeanObject,
    mut v_h_5291_: *mut crate::leanh::LeanObject,
    mut v_k_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5293_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_5290_, v_k_5292_);
    return v___x_5293_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_ctorElim___boxed(
    mut v_00_u03c3_5294_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5295_: *mut crate::leanh::LeanObject,
    mut v_pat_5296_: *mut crate::leanh::LeanObject,
    mut v_s_5297_: *mut crate::leanh::LeanObject,
    mut v_inst_5298_: *mut crate::leanh::LeanObject,
    mut v_motive_5299_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5300_: *mut crate::leanh::LeanObject,
    mut v_t_5301_: *mut crate::leanh::LeanObject,
    mut v_h_5302_: *mut crate::leanh::LeanObject,
    mut v_k_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5304_ = l_String_Slice_RevSplitIterator_ctorElim(
        v_00_u03c3_5294_,
        v_00_u03c1_5295_,
        v_pat_5296_,
        v_s_5297_,
        v_inst_5298_,
        v_motive_5299_,
        v_ctorIdx_5300_,
        v_t_5301_,
        v_h_5302_,
        v_k_5303_,
    );
    crate::leanh::lean_dec(v_ctorIdx_5300_);
    crate::leanh::lean_dec(v_inst_5298_);
    crate::leanh::lean_dec_ref(v_s_5297_);
    crate::leanh::lean_dec(v_pat_5296_);
    return v_res_5304_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_operating_elim___redArg(
    mut v_t_5305_: *mut crate::leanh::LeanObject,
    mut v_operating_5306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5307_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_5305_, v_operating_5306_);
    return v___x_5307_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_operating_elim(
    mut v_00_u03c3_5308_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5309_: *mut crate::leanh::LeanObject,
    mut v_pat_5310_: *mut crate::leanh::LeanObject,
    mut v_s_5311_: *mut crate::leanh::LeanObject,
    mut v_inst_5312_: *mut crate::leanh::LeanObject,
    mut v_motive_5313_: *mut crate::leanh::LeanObject,
    mut v_t_5314_: *mut crate::leanh::LeanObject,
    mut v_h_5315_: *mut crate::leanh::LeanObject,
    mut v_operating_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_5314_, v_operating_5316_);
    return v___x_5317_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_operating_elim___boxed(
    mut v_00_u03c3_5318_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5319_: *mut crate::leanh::LeanObject,
    mut v_pat_5320_: *mut crate::leanh::LeanObject,
    mut v_s_5321_: *mut crate::leanh::LeanObject,
    mut v_inst_5322_: *mut crate::leanh::LeanObject,
    mut v_motive_5323_: *mut crate::leanh::LeanObject,
    mut v_t_5324_: *mut crate::leanh::LeanObject,
    mut v_h_5325_: *mut crate::leanh::LeanObject,
    mut v_operating_5326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5327_ = l_String_Slice_RevSplitIterator_operating_elim(
        v_00_u03c3_5318_,
        v_00_u03c1_5319_,
        v_pat_5320_,
        v_s_5321_,
        v_inst_5322_,
        v_motive_5323_,
        v_t_5324_,
        v_h_5325_,
        v_operating_5326_,
    );
    crate::leanh::lean_dec(v_inst_5322_);
    crate::leanh::lean_dec_ref(v_s_5321_);
    crate::leanh::lean_dec(v_pat_5320_);
    return v_res_5327_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_atEnd_elim___redArg(
    mut v_t_5328_: *mut crate::leanh::LeanObject,
    mut v_atEnd_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5330_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_5328_, v_atEnd_5329_);
    return v___x_5330_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_atEnd_elim(
    mut v_00_u03c3_5331_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5332_: *mut crate::leanh::LeanObject,
    mut v_pat_5333_: *mut crate::leanh::LeanObject,
    mut v_s_5334_: *mut crate::leanh::LeanObject,
    mut v_inst_5335_: *mut crate::leanh::LeanObject,
    mut v_motive_5336_: *mut crate::leanh::LeanObject,
    mut v_t_5337_: *mut crate::leanh::LeanObject,
    mut v_h_5338_: *mut crate::leanh::LeanObject,
    mut v_atEnd_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5340_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_5337_, v_atEnd_5339_);
    return v___x_5340_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_atEnd_elim___boxed(
    mut v_00_u03c3_5341_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5342_: *mut crate::leanh::LeanObject,
    mut v_pat_5343_: *mut crate::leanh::LeanObject,
    mut v_s_5344_: *mut crate::leanh::LeanObject,
    mut v_inst_5345_: *mut crate::leanh::LeanObject,
    mut v_motive_5346_: *mut crate::leanh::LeanObject,
    mut v_t_5347_: *mut crate::leanh::LeanObject,
    mut v_h_5348_: *mut crate::leanh::LeanObject,
    mut v_atEnd_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5350_ = l_String_Slice_RevSplitIterator_atEnd_elim(
        v_00_u03c3_5341_,
        v_00_u03c1_5342_,
        v_pat_5343_,
        v_s_5344_,
        v_inst_5345_,
        v_motive_5346_,
        v_t_5347_,
        v_h_5348_,
        v_atEnd_5349_,
    );
    crate::leanh::lean_dec(v_inst_5345_);
    crate::leanh::lean_dec_ref(v_s_5344_);
    crate::leanh::lean_dec(v_pat_5343_);
    return v_res_5350_;
}
pub unsafe fn l_String_Slice_instInhabitedRevSplitIterator_default(
    mut v_00_u03c3_5351_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5352_: *mut crate::leanh::LeanObject,
    mut v_pat_5353_: *mut crate::leanh::LeanObject,
    mut v_s_5354_: *mut crate::leanh::LeanObject,
    mut v_inst_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ = crate::leanh::lean_box(1);
    return v___x_5356_;
}
pub unsafe fn l_String_Slice_instInhabitedRevSplitIterator_default___boxed(
    mut v_00_u03c3_5357_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5358_: *mut crate::leanh::LeanObject,
    mut v_pat_5359_: *mut crate::leanh::LeanObject,
    mut v_s_5360_: *mut crate::leanh::LeanObject,
    mut v_inst_5361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5362_ = l_String_Slice_instInhabitedRevSplitIterator_default(
        v_00_u03c3_5357_,
        v_00_u03c1_5358_,
        v_pat_5359_,
        v_s_5360_,
        v_inst_5361_,
    );
    crate::leanh::lean_dec(v_inst_5361_);
    crate::leanh::lean_dec_ref(v_s_5360_);
    crate::leanh::lean_dec(v_pat_5359_);
    return v_res_5362_;
}
pub unsafe fn l_String_Slice_instInhabitedRevSplitIterator(
    mut v_a_5363_: *mut crate::leanh::LeanObject,
    mut v_a_5364_: *mut crate::leanh::LeanObject,
    mut v_a_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5368_ = crate::leanh::lean_box(1);
    return v___x_5368_;
}
pub unsafe fn l_String_Slice_instInhabitedRevSplitIterator___boxed(
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_a_5372_: *mut crate::leanh::LeanObject,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5374_ = l_String_Slice_instInhabitedRevSplitIterator(
        v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_,
    );
    crate::leanh::lean_dec(v_a_5373_);
    crate::leanh::lean_dec_ref(v_a_5372_);
    crate::leanh::lean_dec(v_a_5371_);
    return v_res_5374_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(
    mut v_inst_5375_: *mut crate::leanh::LeanObject,
    mut v_s_5376_: *mut crate::leanh::LeanObject,
    mut v_inst_5377_: *mut crate::leanh::LeanObject,
    mut v_x_5378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currPos_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5395_: u8 = 0;
    let mut v_startPos_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5406_: u8 = 0;
    let mut v_unused_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5419_: u8 = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: u8 = 0;
    let mut v_str_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5426_: u8 = 0;
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5434_: u8 = 0;
    let mut v_unused_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5378_) == 0 {
                    v_currPos_5379_ = crate::leanh::lean_ctor_get(v_x_5378_, 0);
                    v_searcher_5380_ = crate::leanh::lean_ctor_get(v_x_5378_, 1);
                    v_isSharedCheck_5438_ = (!crate::leanh::lean_is_exclusive(v_x_5378_)) as u8;
                    if v_isSharedCheck_5438_ == 0 {
                        v___x_5382_ = v_x_5378_;
                        v_isShared_5383_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_5380_);
                        crate::leanh::lean_inc(v_currPos_5379_);
                        crate::leanh::lean_dec(v_x_5378_);
                        v___x_5382_ = crate::leanh::lean_box(0);
                        v_isShared_5383_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_5376_);
                    crate::leanh::lean_dec(v_inst_5375_);
                    v___x_5439_ = crate::leanh::lean_box(2);
                    v___x_5440_ = crate::leanh::lean_apply_2(
                        v_inst_5377_,
                        crate::leanh::lean_box(0),
                        v___x_5439_,
                    );
                    return v___x_5440_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_5376_);
                v___x_5384_ = crate::leanh::lean_apply_2(v_inst_5375_, v_s_5376_, v_searcher_5380_);
                match crate::leanh::lean_obj_tag(v___x_5384_) {
                    0 => {
                        v_out_5385_ = crate::leanh::lean_ctor_get(v___x_5384_, 1);
                        crate::leanh::lean_inc(v_out_5385_);
                        if crate::leanh::lean_obj_tag(v_out_5385_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_5385_, 2);
                            crate::leanh::lean_dec_ref(v_s_5376_);
                            v_it_5386_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                            crate::leanh::lean_inc(v_it_5386_);
                            crate::leanh::lean_dec_ref_known(v___x_5384_, 2);
                            if v_isShared_5383_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5382_, 1, v_it_5386_);
                                v___x_5388_ = v___x_5382_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_5391_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5391_,
                                    0,
                                    v_currPos_5379_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5391_, 1, v_it_5386_);
                                v___x_5388_ = v_reuseFailAlloc_5391_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_5392_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                            v_isSharedCheck_5406_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5384_)) as u8;
                            if v_isSharedCheck_5406_ == 0 {
                                v_unused_5407_ = crate::leanh::lean_ctor_get(v___x_5384_, 1);
                                crate::leanh::lean_dec(v_unused_5407_);
                                v___x_5394_ = v___x_5384_;
                                v_isShared_5395_ = v_isSharedCheck_5406_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_5392_);
                                crate::leanh::lean_dec(v___x_5384_);
                                v___x_5394_ = crate::leanh::lean_box(0);
                                v_isShared_5395_ = v_isSharedCheck_5406_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_5376_);
                        v_it_5408_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                        v_isSharedCheck_5419_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5384_)) as u8;
                        if v_isSharedCheck_5419_ == 0 {
                            v___x_5410_ = v___x_5384_;
                            v_isShared_5411_ = v_isSharedCheck_5419_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_5408_);
                            crate::leanh::lean_dec(v___x_5384_);
                            v___x_5410_ = crate::leanh::lean_box(0);
                            v_isShared_5411_ = v_isSharedCheck_5419_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_5382_);
                        v___x_5420_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5421_ = lean_nat_dec_eq(v_currPos_5379_, v___x_5420_);
                        if v___x_5421_ == 0 {
                            v_str_5422_ = crate::leanh::lean_ctor_get(v_s_5376_, 0);
                            v_startInclusive_5423_ = crate::leanh::lean_ctor_get(v_s_5376_, 1);
                            v_isSharedCheck_5434_ =
                                (!crate::leanh::lean_is_exclusive(v_s_5376_)) as u8;
                            if v_isSharedCheck_5434_ == 0 {
                                v_unused_5435_ = crate::leanh::lean_ctor_get(v_s_5376_, 2);
                                crate::leanh::lean_dec(v_unused_5435_);
                                v___x_5425_ = v_s_5376_;
                                v_isShared_5426_ = v_isSharedCheck_5434_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_startInclusive_5423_);
                                crate::leanh::lean_inc(v_str_5422_);
                                crate::leanh::lean_dec(v_s_5376_);
                                v___x_5425_ = crate::leanh::lean_box(0);
                                v_isShared_5426_ = v_isSharedCheck_5434_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_currPos_5379_);
                            crate::leanh::lean_dec_ref(v_s_5376_);
                            v___x_5436_ = crate::leanh::lean_box(2);
                            v___x_5437_ = crate::leanh::lean_apply_2(
                                v_inst_5377_,
                                crate::leanh::lean_box(0),
                                v___x_5436_,
                            );
                            return v___x_5437_;
                        }
                    }
                }
            }
            2 => {
                v___x_5389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5389_, 0, v___x_5388_);
                v___x_5390_ = crate::leanh::lean_apply_2(
                    v_inst_5377_,
                    crate::leanh::lean_box(0),
                    v___x_5389_,
                );
                return v___x_5390_;
            }
            3 => {
                v_startPos_5396_ = crate::leanh::lean_ctor_get(v_out_5385_, 0);
                crate::leanh::lean_inc(v_startPos_5396_);
                v_endPos_5397_ = crate::leanh::lean_ctor_get(v_out_5385_, 1);
                crate::leanh::lean_inc(v_endPos_5397_);
                crate::leanh::lean_dec_ref_known(v_out_5385_, 2);
                v_slice_5398_ =
                    l_String_Slice_slice_x21(v_s_5376_, v_endPos_5397_, v_currPos_5379_);
                crate::leanh::lean_dec(v_currPos_5379_);
                crate::leanh::lean_dec(v_endPos_5397_);
                if v_isShared_5383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5382_, 1, v_it_5392_);
                    crate::leanh::lean_ctor_set(v___x_5382_, 0, v_startPos_5396_);
                    v_nextIt_5400_ = v___x_5382_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_startPos_5396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5405_, 1, v_it_5392_);
                    v_nextIt_5400_ = v_reuseFailAlloc_5405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5394_, 1, v_slice_5398_);
                    crate::leanh::lean_ctor_set(v___x_5394_, 0, v_nextIt_5400_);
                    v___x_5402_ = v___x_5394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_nextIt_5400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5404_, 1, v_slice_5398_);
                    v___x_5402_ = v_reuseFailAlloc_5404_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5403_ = crate::leanh::lean_apply_2(
                    v_inst_5377_,
                    crate::leanh::lean_box(0),
                    v___x_5402_,
                );
                return v___x_5403_;
            }
            6 => {
                if v_isShared_5383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5382_, 1, v_it_5408_);
                    v___x_5413_ = v___x_5382_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_currPos_5379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_it_5408_);
                    v___x_5413_ = v_reuseFailAlloc_5418_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5413_);
                    v___x_5415_ = v___x_5410_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5413_);
                    v___x_5415_ = v_reuseFailAlloc_5417_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5416_ = crate::leanh::lean_apply_2(
                    v_inst_5377_,
                    crate::leanh::lean_box(0),
                    v___x_5415_,
                );
                return v___x_5416_;
            }
            9 => {
                v___x_5427_ = lean_nat_add(v_startInclusive_5423_, v_currPos_5379_);
                crate::leanh::lean_dec(v_currPos_5379_);
                if v_isShared_5426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5425_, 2, v___x_5427_);
                    v_slice_5429_ = v___x_5425_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5433_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_str_5422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5433_, 1, v_startInclusive_5423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5433_, 2, v___x_5427_);
                    v_slice_5429_ = v_reuseFailAlloc_5433_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5430_ = crate::leanh::lean_box(1);
                v___x_5431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5431_, 0, v___x_5430_);
                crate::leanh::lean_ctor_set(v___x_5431_, 1, v_slice_5429_);
                v___x_5432_ = crate::leanh::lean_apply_2(
                    v_inst_5377_,
                    crate::leanh::lean_box(0),
                    v___x_5431_,
                );
                return v___x_5432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(
    mut v_inst_5441_: *mut crate::leanh::LeanObject,
    mut v_s_5442_: *mut crate::leanh::LeanObject,
    mut v_inst_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5444_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5444_, 0, v_inst_5441_);
    crate::leanh::lean_closure_set(v___f_5444_, 1, v_s_5442_);
    crate::leanh::lean_closure_set(v___f_5444_, 2, v_inst_5443_);
    return v___f_5444_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorOfPure(
    mut v_00_u03c1_5445_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5446_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5447_: *mut crate::leanh::LeanObject,
    mut v_inst_5448_: *mut crate::leanh::LeanObject,
    mut v_inst_5449_: *mut crate::leanh::LeanObject,
    mut v_m_5450_: *mut crate::leanh::LeanObject,
    mut v_s_5451_: *mut crate::leanh::LeanObject,
    mut v_inst_5452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5453_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5453_, 0, v_inst_5448_);
    crate::leanh::lean_closure_set(v___f_5453_, 1, v_s_5451_);
    crate::leanh::lean_closure_set(v___f_5453_, 2, v_inst_5452_);
    return v___f_5453_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(
    mut v_00_u03c1_5454_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5455_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5456_: *mut crate::leanh::LeanObject,
    mut v_inst_5457_: *mut crate::leanh::LeanObject,
    mut v_inst_5458_: *mut crate::leanh::LeanObject,
    mut v_m_5459_: *mut crate::leanh::LeanObject,
    mut v_s_5460_: *mut crate::leanh::LeanObject,
    mut v_inst_5461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5462_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(
        v_00_u03c1_5454_,
        v_00_u03c1_5455_,
        v_00_u03c3_5456_,
        v_inst_5457_,
        v_inst_5458_,
        v_m_5459_,
        v_s_5460_,
        v_inst_5461_,
    );
    crate::leanh::lean_dec(v_inst_5458_);
    crate::leanh::lean_dec(v_00_u03c1_5455_);
    return v_res_5462_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(
    mut v_x_5463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5463_) == 0 {
        let mut v_searcher_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_searcher_5464_ = crate::leanh::lean_ctor_get(v_x_5463_, 1);
        crate::leanh::lean_inc(v_searcher_5464_);
        v___x_5465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5465_, 0, v_searcher_5464_);
        return v___x_5465_;
    } else {
        let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5466_ = crate::leanh::lean_box(0);
        return v___x_5466_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(
    mut v_x_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5468_ =
        l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(
            v_x_5467_,
        );
    crate::leanh::lean_dec(v_x_5467_);
    return v_res_5468_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(
    mut v_00_u03c1_5469_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5470_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5471_: *mut crate::leanh::LeanObject,
    mut v_inst_5472_: *mut crate::leanh::LeanObject,
    mut v_s_5473_: *mut crate::leanh::LeanObject,
    mut v_x_5474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5475_ =
        l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(
            v_x_5474_,
        );
    return v___x_5475_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(
    mut v_00_u03c1_5476_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5477_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5478_: *mut crate::leanh::LeanObject,
    mut v_inst_5479_: *mut crate::leanh::LeanObject,
    mut v_s_5480_: *mut crate::leanh::LeanObject,
    mut v_x_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(
        v_00_u03c1_5476_,
        v_00_u03c1_5477_,
        v_00_u03c3_5478_,
        v_inst_5479_,
        v_s_5480_,
        v_x_5481_,
    );
    crate::leanh::lean_dec(v_x_5481_);
    crate::leanh::lean_dec_ref(v_s_5480_);
    crate::leanh::lean_dec(v_inst_5479_);
    crate::leanh::lean_dec(v_00_u03c1_5477_);
    return v_res_5482_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(
    mut v_x_5483_: *mut crate::leanh::LeanObject,
    mut v_h__1_5484_: *mut crate::leanh::LeanObject,
    mut v_h__2_5485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5483_) == 0 {
        let mut v_currPos_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5485_);
        v_currPos_5486_ = crate::leanh::lean_ctor_get(v_x_5483_, 0);
        crate::leanh::lean_inc(v_currPos_5486_);
        v_searcher_5487_ = crate::leanh::lean_ctor_get(v_x_5483_, 1);
        crate::leanh::lean_inc(v_searcher_5487_);
        crate::leanh::lean_dec_ref_known(v_x_5483_, 2);
        v___x_5488_ = crate::leanh::lean_apply_2(v_h__1_5484_, v_currPos_5486_, v_searcher_5487_);
        return v___x_5488_;
    } else {
        let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5484_);
        v___x_5489_ = crate::leanh::lean_box(0);
        v___x_5490_ = crate::leanh::lean_apply_1(v_h__2_5485_, v___x_5489_);
        return v___x_5490_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(
    mut v_00_u03c1_5491_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5492_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5493_: *mut crate::leanh::LeanObject,
    mut v_inst_5494_: *mut crate::leanh::LeanObject,
    mut v_m_5495_: *mut crate::leanh::LeanObject,
    mut v_s_5496_: *mut crate::leanh::LeanObject,
    mut v_motive_5497_: *mut crate::leanh::LeanObject,
    mut v_x_5498_: *mut crate::leanh::LeanObject,
    mut v_h__1_5499_: *mut crate::leanh::LeanObject,
    mut v_h__2_5500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5498_) == 0 {
        let mut v_currPos_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5500_);
        v_currPos_5501_ = crate::leanh::lean_ctor_get(v_x_5498_, 0);
        crate::leanh::lean_inc(v_currPos_5501_);
        v_searcher_5502_ = crate::leanh::lean_ctor_get(v_x_5498_, 1);
        crate::leanh::lean_inc(v_searcher_5502_);
        crate::leanh::lean_dec_ref_known(v_x_5498_, 2);
        v___x_5503_ = crate::leanh::lean_apply_2(v_h__1_5499_, v_currPos_5501_, v_searcher_5502_);
        return v___x_5503_;
    } else {
        let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5499_);
        v___x_5504_ = crate::leanh::lean_box(0);
        v___x_5505_ = crate::leanh::lean_apply_1(v_h__2_5500_, v___x_5504_);
        return v___x_5505_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(
    mut v_00_u03c1_5506_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5507_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5508_: *mut crate::leanh::LeanObject,
    mut v_inst_5509_: *mut crate::leanh::LeanObject,
    mut v_m_5510_: *mut crate::leanh::LeanObject,
    mut v_s_5511_: *mut crate::leanh::LeanObject,
    mut v_motive_5512_: *mut crate::leanh::LeanObject,
    mut v_x_5513_: *mut crate::leanh::LeanObject,
    mut v_h__1_5514_: *mut crate::leanh::LeanObject,
    mut v_h__2_5515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5516_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_5506_, v_00_u03c1_5507_, v_00_u03c3_5508_, v_inst_5509_, v_m_5510_, v_s_5511_, v_motive_5512_, v_x_5513_, v_h__1_5514_, v_h__2_5515_);
    crate::leanh::lean_dec_ref(v_s_5511_);
    crate::leanh::lean_dec(v_inst_5509_);
    crate::leanh::lean_dec(v_00_u03c1_5507_);
    return v_res_5516_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(
    mut v_x_5517_: *mut crate::leanh::LeanObject,
    mut v_x_5518_: *mut crate::leanh::LeanObject,
    mut v_h__1_5519_: *mut crate::leanh::LeanObject,
    mut v_h__2_5520_: *mut crate::leanh::LeanObject,
    mut v_h__3_5521_: *mut crate::leanh::LeanObject,
    mut v_h__4_5522_: *mut crate::leanh::LeanObject,
    mut v_h__5_5523_: *mut crate::leanh::LeanObject,
    mut v_h__6_5524_: *mut crate::leanh::LeanObject,
    mut v_h__7_5525_: *mut crate::leanh::LeanObject,
    mut v_h__8_5526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5517_) == 0 {
        crate::leanh::lean_dec(v_h__8_5526_);
        crate::leanh::lean_dec(v_h__7_5525_);
        crate::leanh::lean_dec(v_h__6_5524_);
        match crate::leanh::lean_obj_tag(v_x_5518_) {
            0 => {
                let mut v_it_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_5523_);
                crate::leanh::lean_dec(v_h__4_5522_);
                crate::leanh::lean_dec(v_h__3_5521_);
                v_it_5527_ = crate::leanh::lean_ctor_get(v_x_5518_, 0);
                if crate::leanh::lean_obj_tag(v_it_5527_) == 0 {
                    let mut v_currPos_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_5527_);
                    crate::leanh::lean_dec(v_h__2_5520_);
                    v_currPos_5528_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
                    crate::leanh::lean_inc(v_currPos_5528_);
                    v_searcher_5529_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
                    crate::leanh::lean_inc(v_searcher_5529_);
                    crate::leanh::lean_dec_ref_known(v_x_5517_, 2);
                    v_out_5530_ = crate::leanh::lean_ctor_get(v_x_5518_, 1);
                    crate::leanh::lean_inc(v_out_5530_);
                    crate::leanh::lean_dec_ref_known(v_x_5518_, 2);
                    v_currPos_5531_ = crate::leanh::lean_ctor_get(v_it_5527_, 0);
                    crate::leanh::lean_inc(v_currPos_5531_);
                    v_searcher_5532_ = crate::leanh::lean_ctor_get(v_it_5527_, 1);
                    crate::leanh::lean_inc(v_searcher_5532_);
                    crate::leanh::lean_dec_ref_known(v_it_5527_, 2);
                    v___x_5533_ = crate::leanh::lean_apply_5(
                        v_h__1_5519_,
                        v_currPos_5528_,
                        v_searcher_5529_,
                        v_currPos_5531_,
                        v_searcher_5532_,
                        v_out_5530_,
                    );
                    return v___x_5533_;
                } else {
                    let mut v_currPos_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_5519_);
                    v_currPos_5534_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
                    crate::leanh::lean_inc(v_currPos_5534_);
                    v_searcher_5535_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
                    crate::leanh::lean_inc(v_searcher_5535_);
                    crate::leanh::lean_dec_ref_known(v_x_5517_, 2);
                    v_out_5536_ = crate::leanh::lean_ctor_get(v_x_5518_, 1);
                    crate::leanh::lean_inc(v_out_5536_);
                    crate::leanh::lean_dec_ref_known(v_x_5518_, 2);
                    v___x_5537_ = crate::leanh::lean_apply_3(
                        v_h__2_5520_,
                        v_currPos_5534_,
                        v_searcher_5535_,
                        v_out_5536_,
                    );
                    return v___x_5537_;
                }
            }
            1 => {
                let mut v_it_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_5523_);
                crate::leanh::lean_dec(v_h__2_5520_);
                crate::leanh::lean_dec(v_h__1_5519_);
                v_it_5538_ = crate::leanh::lean_ctor_get(v_x_5518_, 0);
                crate::leanh::lean_inc(v_it_5538_);
                crate::leanh::lean_dec_ref_known(v_x_5518_, 1);
                if crate::leanh::lean_obj_tag(v_it_5538_) == 0 {
                    let mut v_currPos_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_5522_);
                    v_currPos_5539_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
                    crate::leanh::lean_inc(v_currPos_5539_);
                    v_searcher_5540_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
                    crate::leanh::lean_inc(v_searcher_5540_);
                    crate::leanh::lean_dec_ref_known(v_x_5517_, 2);
                    v_currPos_5541_ = crate::leanh::lean_ctor_get(v_it_5538_, 0);
                    crate::leanh::lean_inc(v_currPos_5541_);
                    v_searcher_5542_ = crate::leanh::lean_ctor_get(v_it_5538_, 1);
                    crate::leanh::lean_inc(v_searcher_5542_);
                    crate::leanh::lean_dec_ref_known(v_it_5538_, 2);
                    v___x_5543_ = crate::leanh::lean_apply_4(
                        v_h__3_5521_,
                        v_currPos_5539_,
                        v_searcher_5540_,
                        v_currPos_5541_,
                        v_searcher_5542_,
                    );
                    return v___x_5543_;
                } else {
                    let mut v_currPos_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_5521_);
                    v_currPos_5544_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
                    crate::leanh::lean_inc(v_currPos_5544_);
                    v_searcher_5545_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
                    crate::leanh::lean_inc(v_searcher_5545_);
                    crate::leanh::lean_dec_ref_known(v_x_5517_, 2);
                    v___x_5546_ =
                        crate::leanh::lean_apply_2(v_h__4_5522_, v_currPos_5544_, v_searcher_5545_);
                    return v___x_5546_;
                }
            }
            _ => {
                let mut v_currPos_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_5522_);
                crate::leanh::lean_dec(v_h__3_5521_);
                crate::leanh::lean_dec(v_h__2_5520_);
                crate::leanh::lean_dec(v_h__1_5519_);
                v_currPos_5547_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
                crate::leanh::lean_inc(v_currPos_5547_);
                v_searcher_5548_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
                crate::leanh::lean_inc(v_searcher_5548_);
                crate::leanh::lean_dec_ref_known(v_x_5517_, 2);
                v___x_5549_ =
                    crate::leanh::lean_apply_2(v_h__5_5523_, v_currPos_5547_, v_searcher_5548_);
                return v___x_5549_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_5523_);
        crate::leanh::lean_dec(v_h__4_5522_);
        crate::leanh::lean_dec(v_h__3_5521_);
        crate::leanh::lean_dec(v_h__2_5520_);
        crate::leanh::lean_dec(v_h__1_5519_);
        match crate::leanh::lean_obj_tag(v_x_5518_) {
            0 => {
                let mut v_it_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_5526_);
                crate::leanh::lean_dec(v_h__7_5525_);
                v_it_5550_ = crate::leanh::lean_ctor_get(v_x_5518_, 0);
                crate::leanh::lean_inc(v_it_5550_);
                v_out_5551_ = crate::leanh::lean_ctor_get(v_x_5518_, 1);
                crate::leanh::lean_inc(v_out_5551_);
                crate::leanh::lean_dec_ref_known(v_x_5518_, 2);
                v___x_5552_ = crate::leanh::lean_apply_2(v_h__6_5524_, v_it_5550_, v_out_5551_);
                return v___x_5552_;
            }
            1 => {
                let mut v_it_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_5526_);
                crate::leanh::lean_dec(v_h__6_5524_);
                v_it_5553_ = crate::leanh::lean_ctor_get(v_x_5518_, 0);
                crate::leanh::lean_inc(v_it_5553_);
                crate::leanh::lean_dec_ref_known(v_x_5518_, 1);
                v___x_5554_ = crate::leanh::lean_apply_1(v_h__7_5525_, v_it_5553_);
                return v___x_5554_;
            }
            _ => {
                let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_5525_);
                crate::leanh::lean_dec(v_h__6_5524_);
                v___x_5555_ = crate::leanh::lean_box(0);
                v___x_5556_ = crate::leanh::lean_apply_1(v_h__8_5526_, v___x_5555_);
                return v___x_5556_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(
    mut v_00_u03c1_5557_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5558_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5559_: *mut crate::leanh::LeanObject,
    mut v_inst_5560_: *mut crate::leanh::LeanObject,
    mut v_m_5561_: *mut crate::leanh::LeanObject,
    mut v_s_5562_: *mut crate::leanh::LeanObject,
    mut v_motive_5563_: *mut crate::leanh::LeanObject,
    mut v_x_5564_: *mut crate::leanh::LeanObject,
    mut v_x_5565_: *mut crate::leanh::LeanObject,
    mut v_h__1_5566_: *mut crate::leanh::LeanObject,
    mut v_h__2_5567_: *mut crate::leanh::LeanObject,
    mut v_h__3_5568_: *mut crate::leanh::LeanObject,
    mut v_h__4_5569_: *mut crate::leanh::LeanObject,
    mut v_h__5_5570_: *mut crate::leanh::LeanObject,
    mut v_h__6_5571_: *mut crate::leanh::LeanObject,
    mut v_h__7_5572_: *mut crate::leanh::LeanObject,
    mut v_h__8_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5564_) == 0 {
        crate::leanh::lean_dec(v_h__8_5573_);
        crate::leanh::lean_dec(v_h__7_5572_);
        crate::leanh::lean_dec(v_h__6_5571_);
        match crate::leanh::lean_obj_tag(v_x_5565_) {
            0 => {
                let mut v_it_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_5570_);
                crate::leanh::lean_dec(v_h__4_5569_);
                crate::leanh::lean_dec(v_h__3_5568_);
                v_it_5574_ = crate::leanh::lean_ctor_get(v_x_5565_, 0);
                if crate::leanh::lean_obj_tag(v_it_5574_) == 0 {
                    let mut v_currPos_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc_ref(v_it_5574_);
                    crate::leanh::lean_dec(v_h__2_5567_);
                    v_currPos_5575_ = crate::leanh::lean_ctor_get(v_x_5564_, 0);
                    crate::leanh::lean_inc(v_currPos_5575_);
                    v_searcher_5576_ = crate::leanh::lean_ctor_get(v_x_5564_, 1);
                    crate::leanh::lean_inc(v_searcher_5576_);
                    crate::leanh::lean_dec_ref_known(v_x_5564_, 2);
                    v_out_5577_ = crate::leanh::lean_ctor_get(v_x_5565_, 1);
                    crate::leanh::lean_inc(v_out_5577_);
                    crate::leanh::lean_dec_ref_known(v_x_5565_, 2);
                    v_currPos_5578_ = crate::leanh::lean_ctor_get(v_it_5574_, 0);
                    crate::leanh::lean_inc(v_currPos_5578_);
                    v_searcher_5579_ = crate::leanh::lean_ctor_get(v_it_5574_, 1);
                    crate::leanh::lean_inc(v_searcher_5579_);
                    crate::leanh::lean_dec_ref_known(v_it_5574_, 2);
                    v___x_5580_ = crate::leanh::lean_apply_5(
                        v_h__1_5566_,
                        v_currPos_5575_,
                        v_searcher_5576_,
                        v_currPos_5578_,
                        v_searcher_5579_,
                        v_out_5577_,
                    );
                    return v___x_5580_;
                } else {
                    let mut v_currPos_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_out_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__1_5566_);
                    v_currPos_5581_ = crate::leanh::lean_ctor_get(v_x_5564_, 0);
                    crate::leanh::lean_inc(v_currPos_5581_);
                    v_searcher_5582_ = crate::leanh::lean_ctor_get(v_x_5564_, 1);
                    crate::leanh::lean_inc(v_searcher_5582_);
                    crate::leanh::lean_dec_ref_known(v_x_5564_, 2);
                    v_out_5583_ = crate::leanh::lean_ctor_get(v_x_5565_, 1);
                    crate::leanh::lean_inc(v_out_5583_);
                    crate::leanh::lean_dec_ref_known(v_x_5565_, 2);
                    v___x_5584_ = crate::leanh::lean_apply_3(
                        v_h__2_5567_,
                        v_currPos_5581_,
                        v_searcher_5582_,
                        v_out_5583_,
                    );
                    return v___x_5584_;
                }
            }
            1 => {
                let mut v_it_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_5570_);
                crate::leanh::lean_dec(v_h__2_5567_);
                crate::leanh::lean_dec(v_h__1_5566_);
                v_it_5585_ = crate::leanh::lean_ctor_get(v_x_5565_, 0);
                crate::leanh::lean_inc(v_it_5585_);
                crate::leanh::lean_dec_ref_known(v_x_5565_, 1);
                if crate::leanh::lean_obj_tag(v_it_5585_) == 0 {
                    let mut v_currPos_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_currPos_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_5569_);
                    v_currPos_5586_ = crate::leanh::lean_ctor_get(v_x_5564_, 0);
                    crate::leanh::lean_inc(v_currPos_5586_);
                    v_searcher_5587_ = crate::leanh::lean_ctor_get(v_x_5564_, 1);
                    crate::leanh::lean_inc(v_searcher_5587_);
                    crate::leanh::lean_dec_ref_known(v_x_5564_, 2);
                    v_currPos_5588_ = crate::leanh::lean_ctor_get(v_it_5585_, 0);
                    crate::leanh::lean_inc(v_currPos_5588_);
                    v_searcher_5589_ = crate::leanh::lean_ctor_get(v_it_5585_, 1);
                    crate::leanh::lean_inc(v_searcher_5589_);
                    crate::leanh::lean_dec_ref_known(v_it_5585_, 2);
                    v___x_5590_ = crate::leanh::lean_apply_4(
                        v_h__3_5568_,
                        v_currPos_5586_,
                        v_searcher_5587_,
                        v_currPos_5588_,
                        v_searcher_5589_,
                    );
                    return v___x_5590_;
                } else {
                    let mut v_currPos_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_searcher_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_5568_);
                    v_currPos_5591_ = crate::leanh::lean_ctor_get(v_x_5564_, 0);
                    crate::leanh::lean_inc(v_currPos_5591_);
                    v_searcher_5592_ = crate::leanh::lean_ctor_get(v_x_5564_, 1);
                    crate::leanh::lean_inc(v_searcher_5592_);
                    crate::leanh::lean_dec_ref_known(v_x_5564_, 2);
                    v___x_5593_ =
                        crate::leanh::lean_apply_2(v_h__4_5569_, v_currPos_5591_, v_searcher_5592_);
                    return v___x_5593_;
                }
            }
            _ => {
                let mut v_currPos_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_5569_);
                crate::leanh::lean_dec(v_h__3_5568_);
                crate::leanh::lean_dec(v_h__2_5567_);
                crate::leanh::lean_dec(v_h__1_5566_);
                v_currPos_5594_ = crate::leanh::lean_ctor_get(v_x_5564_, 0);
                crate::leanh::lean_inc(v_currPos_5594_);
                v_searcher_5595_ = crate::leanh::lean_ctor_get(v_x_5564_, 1);
                crate::leanh::lean_inc(v_searcher_5595_);
                crate::leanh::lean_dec_ref_known(v_x_5564_, 2);
                v___x_5596_ =
                    crate::leanh::lean_apply_2(v_h__5_5570_, v_currPos_5594_, v_searcher_5595_);
                return v___x_5596_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__5_5570_);
        crate::leanh::lean_dec(v_h__4_5569_);
        crate::leanh::lean_dec(v_h__3_5568_);
        crate::leanh::lean_dec(v_h__2_5567_);
        crate::leanh::lean_dec(v_h__1_5566_);
        match crate::leanh::lean_obj_tag(v_x_5565_) {
            0 => {
                let mut v_it_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_out_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_5573_);
                crate::leanh::lean_dec(v_h__7_5572_);
                v_it_5597_ = crate::leanh::lean_ctor_get(v_x_5565_, 0);
                crate::leanh::lean_inc(v_it_5597_);
                v_out_5598_ = crate::leanh::lean_ctor_get(v_x_5565_, 1);
                crate::leanh::lean_inc(v_out_5598_);
                crate::leanh::lean_dec_ref_known(v_x_5565_, 2);
                v___x_5599_ = crate::leanh::lean_apply_2(v_h__6_5571_, v_it_5597_, v_out_5598_);
                return v___x_5599_;
            }
            1 => {
                let mut v_it_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__8_5573_);
                crate::leanh::lean_dec(v_h__6_5571_);
                v_it_5600_ = crate::leanh::lean_ctor_get(v_x_5565_, 0);
                crate::leanh::lean_inc(v_it_5600_);
                crate::leanh::lean_dec_ref_known(v_x_5565_, 1);
                v___x_5601_ = crate::leanh::lean_apply_1(v_h__7_5572_, v_it_5600_);
                return v___x_5601_;
            }
            _ => {
                let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_5572_);
                crate::leanh::lean_dec(v_h__6_5571_);
                v___x_5602_ = crate::leanh::lean_box(0);
                v___x_5603_ = crate::leanh::lean_apply_1(v_h__8_5573_, v___x_5602_);
                return v___x_5603_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c1_5604_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c1_5605_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3_5606_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_5607_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_m_5608_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_s_5609_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_motive_5610_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_x_5611_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_5612_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_h__1_5613_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_h__2_5614_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_h__3_5615_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_h__4_5616_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_h__5_5617_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_h__6_5618_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_h__7_5619_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_h__8_5620_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5621_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_5604_, v_00_u03c1_5605_, v_00_u03c3_5606_, v_inst_5607_, v_m_5608_, v_s_5609_, v_motive_5610_, v_x_5611_, v_x_5612_, v_h__1_5613_, v_h__2_5614_, v_h__3_5615_, v_h__4_5616_, v_h__5_5617_, v_h__6_5618_, v_h__7_5619_, v_h__8_5620_);
    crate::leanh::lean_dec_ref(v_s_5609_);
    crate::leanh::lean_dec(v_inst_5607_);
    crate::leanh::lean_dec(v_00_u03c1_5605_);
    return v_res_5621_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(
    mut v_x_5622_: *mut crate::leanh::LeanObject,
    mut v_h__1_5623_: *mut crate::leanh::LeanObject,
    mut v_h__2_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5622_) == 0 {
        let mut v_currPos_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5624_);
        v_currPos_5625_ = crate::leanh::lean_ctor_get(v_x_5622_, 0);
        crate::leanh::lean_inc(v_currPos_5625_);
        v_searcher_5626_ = crate::leanh::lean_ctor_get(v_x_5622_, 1);
        crate::leanh::lean_inc(v_searcher_5626_);
        crate::leanh::lean_dec_ref_known(v_x_5622_, 2);
        v___x_5627_ = crate::leanh::lean_apply_2(v_h__1_5623_, v_currPos_5625_, v_searcher_5626_);
        return v___x_5627_;
    } else {
        let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5623_);
        v___x_5628_ = crate::leanh::lean_box(0);
        v___x_5629_ = crate::leanh::lean_apply_1(v_h__2_5624_, v___x_5628_);
        return v___x_5629_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(
    mut v_00_u03c1_5630_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5631_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5632_: *mut crate::leanh::LeanObject,
    mut v_inst_5633_: *mut crate::leanh::LeanObject,
    mut v_s_5634_: *mut crate::leanh::LeanObject,
    mut v_motive_5635_: *mut crate::leanh::LeanObject,
    mut v_x_5636_: *mut crate::leanh::LeanObject,
    mut v_h__1_5637_: *mut crate::leanh::LeanObject,
    mut v_h__2_5638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5636_) == 0 {
        let mut v_currPos_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_searcher_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5638_);
        v_currPos_5639_ = crate::leanh::lean_ctor_get(v_x_5636_, 0);
        crate::leanh::lean_inc(v_currPos_5639_);
        v_searcher_5640_ = crate::leanh::lean_ctor_get(v_x_5636_, 1);
        crate::leanh::lean_inc(v_searcher_5640_);
        crate::leanh::lean_dec_ref_known(v_x_5636_, 2);
        v___x_5641_ = crate::leanh::lean_apply_2(v_h__1_5637_, v_currPos_5639_, v_searcher_5640_);
        return v___x_5641_;
    } else {
        let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5637_);
        v___x_5642_ = crate::leanh::lean_box(0);
        v___x_5643_ = crate::leanh::lean_apply_1(v_h__2_5638_, v___x_5642_);
        return v___x_5643_;
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(
    mut v_00_u03c1_5644_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5645_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5646_: *mut crate::leanh::LeanObject,
    mut v_inst_5647_: *mut crate::leanh::LeanObject,
    mut v_s_5648_: *mut crate::leanh::LeanObject,
    mut v_motive_5649_: *mut crate::leanh::LeanObject,
    mut v_x_5650_: *mut crate::leanh::LeanObject,
    mut v_h__1_5651_: *mut crate::leanh::LeanObject,
    mut v_h__2_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5653_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_5644_, v_00_u03c1_5645_, v_00_u03c3_5646_, v_inst_5647_, v_s_5648_, v_motive_5649_, v_x_5650_, v_h__1_5651_, v_h__2_5652_);
    crate::leanh::lean_dec_ref(v_s_5648_);
    crate::leanh::lean_dec(v_inst_5647_);
    crate::leanh::lean_dec(v_00_u03c1_5645_);
    return v_res_5653_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(
    mut v_00_u03c1_5654_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5655_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5656_: *mut crate::leanh::LeanObject,
    mut v_inst_5657_: *mut crate::leanh::LeanObject,
    mut v_inst_5658_: *mut crate::leanh::LeanObject,
    mut v_s_5659_: *mut crate::leanh::LeanObject,
    mut v_inst_5660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5661_ = crate::leanh::lean_box(0);
    return v___x_5661_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(
    mut v_00_u03c1_5662_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5663_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5664_: *mut crate::leanh::LeanObject,
    mut v_inst_5665_: *mut crate::leanh::LeanObject,
    mut v_inst_5666_: *mut crate::leanh::LeanObject,
    mut v_s_5667_: *mut crate::leanh::LeanObject,
    mut v_inst_5668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5669_ =
        l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(
            v_00_u03c1_5662_,
            v_00_u03c1_5663_,
            v_00_u03c3_5664_,
            v_inst_5665_,
            v_inst_5666_,
            v_s_5667_,
            v_inst_5668_,
        );
    crate::leanh::lean_dec_ref(v_s_5667_);
    crate::leanh::lean_dec(v_inst_5666_);
    crate::leanh::lean_dec(v_inst_5665_);
    crate::leanh::lean_dec(v_00_u03c1_5663_);
    return v_res_5669_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(
    mut v_toPure_5670_: *mut crate::leanh::LeanObject,
    mut v_recur_5671_: *mut crate::leanh::LeanObject,
    mut v_it_5672_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_5673_) == 0 {
        let mut v_a_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_5672_);
        crate::leanh::lean_dec(v_recur_5671_);
        v_a_5674_ = crate::leanh::lean_ctor_get(v_____do__lift_5673_, 0);
        crate::leanh::lean_inc(v_a_5674_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5673_, 1);
        v___x_5675_ =
            crate::leanh::lean_apply_2(v_toPure_5670_, crate::leanh::lean_box(0), v_a_5674_);
        return v___x_5675_;
    } else {
        let mut v_a_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_5670_);
        v_a_5676_ = crate::leanh::lean_ctor_get(v_____do__lift_5673_, 0);
        crate::leanh::lean_inc(v_a_5676_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_5673_, 1);
        v___x_5677_ = crate::leanh::lean_apply_4(
            v_recur_5671_,
            v_it_5672_,
            v_a_5676_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_5677_;
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(
    mut v_toPure_5678_: *mut crate::leanh::LeanObject,
    mut v_recur_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
    mut v_acc_5681_: *mut crate::leanh::LeanObject,
    mut v_toBind_5682_: *mut crate::leanh::LeanObject,
    mut v_s_5683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_5683_) {
        0 => {
            let mut v_it_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_5684_ = crate::leanh::lean_ctor_get(v_s_5683_, 0);
            crate::leanh::lean_inc(v_it_5684_);
            v_out_5685_ = crate::leanh::lean_ctor_get(v_s_5683_, 1);
            crate::leanh::lean_inc(v_out_5685_);
            crate::leanh::lean_dec_ref_known(v_s_5683_, 2);
            v___f_5686_ = crate::leanh::lean_alloc_closure(
                l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5686_, 0, v_toPure_5678_);
            crate::leanh::lean_closure_set(v___f_5686_, 1, v_recur_5679_);
            crate::leanh::lean_closure_set(v___f_5686_, 2, v_it_5684_);
            v___x_5687_ = crate::leanh::lean_apply_3(
                v___y_5680_,
                v_out_5685_,
                crate::leanh::lean_box(0),
                v_acc_5681_,
            );
            v___x_5688_ = crate::leanh::lean_apply_4(
                v_toBind_5682_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5687_,
                v___f_5686_,
            );
            return v___x_5688_;
        }
        1 => {
            let mut v_it_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_5682_);
            crate::leanh::lean_dec(v___y_5680_);
            crate::leanh::lean_dec(v_toPure_5678_);
            v_it_5689_ = crate::leanh::lean_ctor_get(v_s_5683_, 0);
            crate::leanh::lean_inc(v_it_5689_);
            crate::leanh::lean_dec_ref_known(v_s_5683_, 1);
            v___x_5690_ = crate::leanh::lean_apply_4(
                v_recur_5679_,
                v_it_5689_,
                v_acc_5681_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_5690_;
        }
        _ => {
            let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_5682_);
            crate::leanh::lean_dec(v___y_5680_);
            crate::leanh::lean_dec(v_recur_5679_);
            v___x_5691_ =
                crate::leanh::lean_apply_2(v_toPure_5678_, crate::leanh::lean_box(0), v_acc_5681_);
            return v___x_5691_;
        }
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(
    mut v_toPure_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v_toBind_5694_: *mut crate::leanh::LeanObject,
    mut v_inst_5695_: *mut crate::leanh::LeanObject,
    mut v_s_5696_: *mut crate::leanh::LeanObject,
    mut v_toPure_5697_: *mut crate::leanh::LeanObject,
    mut v_lift_5698_: *mut crate::leanh::LeanObject,
    mut v_it_5699_: *mut crate::leanh::LeanObject,
    mut v_acc_5700_: *mut crate::leanh::LeanObject,
    mut v_hP_5701_: *mut crate::leanh::LeanObject,
    mut v_recur_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v_startPos_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut v_unused_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5738_: u8 = 0;
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: u8 = 0;
    let mut v_str_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5763_: u8 = 0;
    let mut v_unused_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5768_: u8 = 0;
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5703_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_5703_, 0, v_toPure_5692_);
                crate::leanh::lean_closure_set(v___f_5703_, 1, v_recur_5702_);
                crate::leanh::lean_closure_set(v___f_5703_, 2, v___y_5693_);
                crate::leanh::lean_closure_set(v___f_5703_, 3, v_acc_5700_);
                crate::leanh::lean_closure_set(v___f_5703_, 4, v_toBind_5694_);
                if crate::leanh::lean_obj_tag(v_it_5699_) == 0 {
                    v_currPos_5704_ = crate::leanh::lean_ctor_get(v_it_5699_, 0);
                    v_searcher_5705_ = crate::leanh::lean_ctor_get(v_it_5699_, 1);
                    v_isSharedCheck_5768_ = (!crate::leanh::lean_is_exclusive(v_it_5699_)) as u8;
                    if v_isSharedCheck_5768_ == 0 {
                        v___x_5707_ = v_it_5699_;
                        v_isShared_5708_ = v_isSharedCheck_5768_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_5705_);
                        crate::leanh::lean_inc(v_currPos_5704_);
                        crate::leanh::lean_dec(v_it_5699_);
                        v___x_5707_ = crate::leanh::lean_box(0);
                        v_isShared_5708_ = v_isSharedCheck_5768_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_s_5696_);
                    crate::leanh::lean_dec(v_inst_5695_);
                    v___x_5769_ = crate::leanh::lean_box(2);
                    v___x_5770_ = crate::leanh::lean_apply_2(
                        v_toPure_5697_,
                        crate::leanh::lean_box(0),
                        v___x_5769_,
                    );
                    v___x_5771_ = crate::leanh::lean_apply_4(
                        v_lift_5698_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_5703_,
                        v___x_5770_,
                    );
                    return v___x_5771_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_5696_);
                v___x_5709_ = crate::leanh::lean_apply_2(v_inst_5695_, v_s_5696_, v_searcher_5705_);
                match crate::leanh::lean_obj_tag(v___x_5709_) {
                    0 => {
                        v_out_5710_ = crate::leanh::lean_ctor_get(v___x_5709_, 1);
                        crate::leanh::lean_inc(v_out_5710_);
                        if crate::leanh::lean_obj_tag(v_out_5710_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_out_5710_, 2);
                            crate::leanh::lean_dec_ref(v_s_5696_);
                            v_it_5711_ = crate::leanh::lean_ctor_get(v___x_5709_, 0);
                            crate::leanh::lean_inc(v_it_5711_);
                            crate::leanh::lean_dec_ref_known(v___x_5709_, 2);
                            if v_isShared_5708_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5707_, 1, v_it_5711_);
                                v___x_5713_ = v___x_5707_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_5717_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5717_,
                                    0,
                                    v_currPos_5704_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 1, v_it_5711_);
                                v___x_5713_ = v_reuseFailAlloc_5717_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_it_5718_ = crate::leanh::lean_ctor_get(v___x_5709_, 0);
                            v_isSharedCheck_5733_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5709_)) as u8;
                            if v_isSharedCheck_5733_ == 0 {
                                v_unused_5734_ = crate::leanh::lean_ctor_get(v___x_5709_, 1);
                                crate::leanh::lean_dec(v_unused_5734_);
                                v___x_5720_ = v___x_5709_;
                                v_isShared_5721_ = v_isSharedCheck_5733_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_it_5718_);
                                crate::leanh::lean_dec(v___x_5709_);
                                v___x_5720_ = crate::leanh::lean_box(0);
                                v_isShared_5721_ = v_isSharedCheck_5733_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_s_5696_);
                        v_it_5735_ = crate::leanh::lean_ctor_get(v___x_5709_, 0);
                        v_isSharedCheck_5747_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5709_)) as u8;
                        if v_isSharedCheck_5747_ == 0 {
                            v___x_5737_ = v___x_5709_;
                            v_isShared_5738_ = v_isSharedCheck_5747_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_5735_);
                            crate::leanh::lean_dec(v___x_5709_);
                            v___x_5737_ = crate::leanh::lean_box(0);
                            v_isShared_5738_ = v_isSharedCheck_5747_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_5707_);
                        v___x_5748_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5749_ = lean_nat_dec_eq(v_currPos_5704_, v___x_5748_);
                        if v___x_5749_ == 0 {
                            v_str_5750_ = crate::leanh::lean_ctor_get(v_s_5696_, 0);
                            v_startInclusive_5751_ = crate::leanh::lean_ctor_get(v_s_5696_, 1);
                            v_isSharedCheck_5763_ =
                                (!crate::leanh::lean_is_exclusive(v_s_5696_)) as u8;
                            if v_isSharedCheck_5763_ == 0 {
                                v_unused_5764_ = crate::leanh::lean_ctor_get(v_s_5696_, 2);
                                crate::leanh::lean_dec(v_unused_5764_);
                                v___x_5753_ = v_s_5696_;
                                v_isShared_5754_ = v_isSharedCheck_5763_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_startInclusive_5751_);
                                crate::leanh::lean_inc(v_str_5750_);
                                crate::leanh::lean_dec(v_s_5696_);
                                v___x_5753_ = crate::leanh::lean_box(0);
                                v_isShared_5754_ = v_isSharedCheck_5763_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_currPos_5704_);
                            crate::leanh::lean_dec_ref(v_s_5696_);
                            v___x_5765_ = crate::leanh::lean_box(2);
                            v___x_5766_ = crate::leanh::lean_apply_2(
                                v_toPure_5697_,
                                crate::leanh::lean_box(0),
                                v___x_5765_,
                            );
                            v___x_5767_ = crate::leanh::lean_apply_4(
                                v_lift_5698_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___f_5703_,
                                v___x_5766_,
                            );
                            return v___x_5767_;
                        }
                    }
                }
            }
            2 => {
                v___x_5714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5714_, 0, v___x_5713_);
                v___x_5715_ = crate::leanh::lean_apply_2(
                    v_toPure_5697_,
                    crate::leanh::lean_box(0),
                    v___x_5714_,
                );
                v___x_5716_ = crate::leanh::lean_apply_4(
                    v_lift_5698_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_5703_,
                    v___x_5715_,
                );
                return v___x_5716_;
            }
            3 => {
                v_startPos_5722_ = crate::leanh::lean_ctor_get(v_out_5710_, 0);
                crate::leanh::lean_inc(v_startPos_5722_);
                v_endPos_5723_ = crate::leanh::lean_ctor_get(v_out_5710_, 1);
                crate::leanh::lean_inc(v_endPos_5723_);
                crate::leanh::lean_dec_ref_known(v_out_5710_, 2);
                v_slice_5724_ =
                    l_String_Slice_slice_x21(v_s_5696_, v_endPos_5723_, v_currPos_5704_);
                crate::leanh::lean_dec(v_currPos_5704_);
                crate::leanh::lean_dec(v_endPos_5723_);
                if v_isShared_5708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5707_, 1, v_it_5718_);
                    crate::leanh::lean_ctor_set(v___x_5707_, 0, v_startPos_5722_);
                    v_nextIt_5726_ = v___x_5707_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_startPos_5722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 1, v_it_5718_);
                    v_nextIt_5726_ = v_reuseFailAlloc_5732_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5720_, 1, v_slice_5724_);
                    crate::leanh::lean_ctor_set(v___x_5720_, 0, v_nextIt_5726_);
                    v___x_5728_ = v___x_5720_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_nextIt_5726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 1, v_slice_5724_);
                    v___x_5728_ = v_reuseFailAlloc_5731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5729_ = crate::leanh::lean_apply_2(
                    v_toPure_5697_,
                    crate::leanh::lean_box(0),
                    v___x_5728_,
                );
                v___x_5730_ = crate::leanh::lean_apply_4(
                    v_lift_5698_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_5703_,
                    v___x_5729_,
                );
                return v___x_5730_;
            }
            6 => {
                if v_isShared_5708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5707_, 1, v_it_5735_);
                    v___x_5740_ = v___x_5707_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_currPos_5704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5746_, 1, v_it_5735_);
                    v___x_5740_ = v_reuseFailAlloc_5746_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5737_, 0, v___x_5740_);
                    v___x_5742_ = v___x_5737_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5745_, 0, v___x_5740_);
                    v___x_5742_ = v_reuseFailAlloc_5745_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5743_ = crate::leanh::lean_apply_2(
                    v_toPure_5697_,
                    crate::leanh::lean_box(0),
                    v___x_5742_,
                );
                v___x_5744_ = crate::leanh::lean_apply_4(
                    v_lift_5698_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_5703_,
                    v___x_5743_,
                );
                return v___x_5744_;
            }
            9 => {
                v___x_5755_ = lean_nat_add(v_startInclusive_5751_, v_currPos_5704_);
                crate::leanh::lean_dec(v_currPos_5704_);
                if v_isShared_5754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5753_, 2, v___x_5755_);
                    v_slice_5757_ = v___x_5753_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5762_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_str_5750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 1, v_startInclusive_5751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 2, v___x_5755_);
                    v_slice_5757_ = v_reuseFailAlloc_5762_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5758_ = crate::leanh::lean_box(1);
                v___x_5759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5759_, 0, v___x_5758_);
                crate::leanh::lean_ctor_set(v___x_5759_, 1, v_slice_5757_);
                v___x_5760_ = crate::leanh::lean_apply_2(
                    v_toPure_5697_,
                    crate::leanh::lean_box(0),
                    v___x_5759_,
                );
                v___x_5761_ = crate::leanh::lean_apply_4(
                    v_lift_5698_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_5703_,
                    v___x_5760_,
                );
                return v___x_5761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(
    mut v_inst_5772_: *mut crate::leanh::LeanObject,
    mut v_inst_5773_: *mut crate::leanh::LeanObject,
    mut v_s_5774_: *mut crate::leanh::LeanObject,
    mut v_toPure_5775_: *mut crate::leanh::LeanObject,
    mut v_lift_5776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_5777_: *mut crate::leanh::LeanObject,
    mut v_Pl_5778_: *mut crate::leanh::LeanObject,
    mut v_it_5779_: *mut crate::leanh::LeanObject,
    mut v_init_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5782_ = crate::leanh::lean_ctor_get(v_inst_5772_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5782_);
    v_toBind_5783_ = crate::leanh::lean_ctor_get(v_inst_5772_, 1);
    crate::leanh::lean_inc(v_toBind_5783_);
    crate::leanh::lean_dec_ref(v_inst_5772_);
    v_toPure_5784_ = crate::leanh::lean_ctor_get(v_toApplicative_5782_, 1);
    crate::leanh::lean_inc(v_toPure_5784_);
    crate::leanh::lean_dec_ref(v_toApplicative_5782_);
    v___f_5785_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_5785_, 0, v_toPure_5784_);
    crate::leanh::lean_closure_set(v___f_5785_, 1, v___y_5781_);
    crate::leanh::lean_closure_set(v___f_5785_, 2, v_toBind_5783_);
    crate::leanh::lean_closure_set(v___f_5785_, 3, v_inst_5773_);
    crate::leanh::lean_closure_set(v___f_5785_, 4, v_s_5774_);
    crate::leanh::lean_closure_set(v___f_5785_, 5, v_toPure_5775_);
    crate::leanh::lean_closure_set(v___f_5785_, 6, v_lift_5776_);
    v___x_5786_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_5785_,
        v_it_5779_,
        v_init_5780_,
        crate::leanh::lean_box(0),
    );
    return v___x_5786_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(
    mut v_inst_5787_: *mut crate::leanh::LeanObject,
    mut v_s_5788_: *mut crate::leanh::LeanObject,
    mut v_inst_5789_: *mut crate::leanh::LeanObject,
    mut v_inst_5790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5791_ = crate::leanh::lean_ctor_get(v_inst_5789_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5791_);
    crate::leanh::lean_dec_ref(v_inst_5789_);
    v_toPure_5792_ = crate::leanh::lean_ctor_get(v_toApplicative_5791_, 1);
    crate::leanh::lean_inc(v_toPure_5792_);
    crate::leanh::lean_dec_ref(v_toApplicative_5791_);
    v___f_5793_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5793_, 0, v_inst_5790_);
    crate::leanh::lean_closure_set(v___f_5793_, 1, v_inst_5787_);
    crate::leanh::lean_closure_set(v___f_5793_, 2, v_s_5788_);
    crate::leanh::lean_closure_set(v___f_5793_, 3, v_toPure_5792_);
    return v___f_5793_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(
    mut v_00_u03c1_5794_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5795_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5796_: *mut crate::leanh::LeanObject,
    mut v_inst_5797_: *mut crate::leanh::LeanObject,
    mut v_inst_5798_: *mut crate::leanh::LeanObject,
    mut v_m_5799_: *mut crate::leanh::LeanObject,
    mut v_n_5800_: *mut crate::leanh::LeanObject,
    mut v_s_5801_: *mut crate::leanh::LeanObject,
    mut v_inst_5802_: *mut crate::leanh::LeanObject,
    mut v_inst_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5804_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(
        v_inst_5797_,
        v_s_5801_,
        v_inst_5802_,
        v_inst_5803_,
    );
    return v___x_5804_;
}
pub unsafe fn l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(
    mut v_00_u03c1_5805_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5806_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5807_: *mut crate::leanh::LeanObject,
    mut v_inst_5808_: *mut crate::leanh::LeanObject,
    mut v_inst_5809_: *mut crate::leanh::LeanObject,
    mut v_m_5810_: *mut crate::leanh::LeanObject,
    mut v_n_5811_: *mut crate::leanh::LeanObject,
    mut v_s_5812_: *mut crate::leanh::LeanObject,
    mut v_inst_5813_: *mut crate::leanh::LeanObject,
    mut v_inst_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5815_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(
        v_00_u03c1_5805_,
        v_00_u03c1_5806_,
        v_00_u03c3_5807_,
        v_inst_5808_,
        v_inst_5809_,
        v_m_5810_,
        v_n_5811_,
        v_s_5812_,
        v_inst_5813_,
        v_inst_5814_,
    );
    crate::leanh::lean_dec(v_inst_5809_);
    crate::leanh::lean_dec(v_00_u03c1_5806_);
    return v_res_5815_;
}
pub unsafe fn l_String_Slice_revSplit___redArg(
    mut v_s_5816_: *mut crate::leanh::LeanObject,
    mut v_inst_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_5818_ = crate::leanh::lean_ctor_get(v_s_5816_, 1);
    v_endExclusive_5819_ = crate::leanh::lean_ctor_get(v_s_5816_, 2);
    v___x_5820_ = lean_nat_sub(v_endExclusive_5819_, v_startInclusive_5818_);
    v___x_5821_ = crate::leanh::lean_apply_1(v_inst_5817_, v_s_5816_);
    v___x_5822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5822_, 0, v___x_5820_);
    crate::leanh::lean_ctor_set(v___x_5822_, 1, v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn l_String_Slice_revSplit(
    mut v_00_u03c3_5823_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5824_: *mut crate::leanh::LeanObject,
    mut v_s_5825_: *mut crate::leanh::LeanObject,
    mut v_pat_5826_: *mut crate::leanh::LeanObject,
    mut v_inst_5827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_String_Slice_revSplit___redArg(v_s_5825_, v_inst_5827_);
    return v___x_5828_;
}
pub unsafe fn l_String_Slice_revSplit___boxed(
    mut v_00_u03c3_5829_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_5830_: *mut crate::leanh::LeanObject,
    mut v_s_5831_: *mut crate::leanh::LeanObject,
    mut v_pat_5832_: *mut crate::leanh::LeanObject,
    mut v_inst_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5834_ = l_String_Slice_revSplit(
        v_00_u03c3_5829_,
        v_00_u03c1_5830_,
        v_s_5831_,
        v_pat_5832_,
        v_inst_5833_,
    );
    crate::leanh::lean_dec(v_pat_5832_);
    return v_res_5834_;
}
pub unsafe fn l_String_Slice_skipSuffix_x3f___redArg(
    mut v_s_5835_: *mut crate::leanh::LeanObject,
    mut v_inst_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipSuffix_x3f_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipSuffix_x3f_5837_ = crate::leanh::lean_ctor_get(v_inst_5836_, 0);
    crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5837_);
    crate::leanh::lean_dec_ref(v_inst_5836_);
    v___x_5838_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5837_, v_s_5835_);
    return v___x_5838_;
}
pub unsafe fn l_String_Slice_skipSuffix_x3f(
    mut v_00_u03c1_5839_: *mut crate::leanh::LeanObject,
    mut v_s_5840_: *mut crate::leanh::LeanObject,
    mut v_pat_5841_: *mut crate::leanh::LeanObject,
    mut v_inst_5842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipSuffix_x3f_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipSuffix_x3f_5843_ = crate::leanh::lean_ctor_get(v_inst_5842_, 0);
    crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5843_);
    crate::leanh::lean_dec_ref(v_inst_5842_);
    v___x_5844_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5843_, v_s_5840_);
    return v___x_5844_;
}
pub unsafe fn l_String_Slice_skipSuffix_x3f___boxed(
    mut v_00_u03c1_5845_: *mut crate::leanh::LeanObject,
    mut v_s_5846_: *mut crate::leanh::LeanObject,
    mut v_pat_5847_: *mut crate::leanh::LeanObject,
    mut v_inst_5848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5849_ =
        l_String_Slice_skipSuffix_x3f(v_00_u03c1_5845_, v_s_5846_, v_pat_5847_, v_inst_5848_);
    crate::leanh::lean_dec(v_pat_5847_);
    return v_res_5849_;
}
pub unsafe fn l_String_Slice_Pos_revSkip_x3f___redArg(
    mut v_s_5850_: *mut crate::leanh::LeanObject,
    mut v_pos_5851_: *mut crate::leanh::LeanObject,
    mut v_inst_5852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v_skipSuffix_x3f_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_reuseFailAlloc_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5872_: u8 = 0;
    let mut v_unused_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5853_ = crate::leanh::lean_ctor_get(v_s_5850_, 0);
                v_startInclusive_5854_ = crate::leanh::lean_ctor_get(v_s_5850_, 1);
                v_isSharedCheck_5872_ = (!crate::leanh::lean_is_exclusive(v_s_5850_)) as u8;
                if v_isSharedCheck_5872_ == 0 {
                    v_unused_5873_ = crate::leanh::lean_ctor_get(v_s_5850_, 2);
                    crate::leanh::lean_dec(v_unused_5873_);
                    v___x_5856_ = v_s_5850_;
                    v_isShared_5857_ = v_isSharedCheck_5872_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_5854_);
                    crate::leanh::lean_inc(v_str_5853_);
                    crate::leanh::lean_dec(v_s_5850_);
                    v___x_5856_ = crate::leanh::lean_box(0);
                    v_isShared_5857_ = v_isSharedCheck_5872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_skipSuffix_x3f_5858_ = crate::leanh::lean_ctor_get(v_inst_5852_, 0);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5858_);
                crate::leanh::lean_dec_ref(v_inst_5852_);
                v___x_5859_ = lean_nat_add(v_startInclusive_5854_, v_pos_5851_);
                if v_isShared_5857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5856_, 2, v___x_5859_);
                    v___x_5861_ = v___x_5856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5871_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_str_5853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5871_, 1, v_startInclusive_5854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5871_, 2, v___x_5859_);
                    v___x_5861_ = v_reuseFailAlloc_5871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5862_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5858_, v___x_5861_);
                if crate::leanh::lean_obj_tag(v___x_5862_) == 0 {
                    return v___x_5862_;
                } else {
                    v_val_5863_ = crate::leanh::lean_ctor_get(v___x_5862_, 0);
                    v_isSharedCheck_5870_ = (!crate::leanh::lean_is_exclusive(v___x_5862_)) as u8;
                    if v_isSharedCheck_5870_ == 0 {
                        v___x_5865_ = v___x_5862_;
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5863_);
                        crate::leanh::lean_dec(v___x_5862_);
                        v___x_5865_ = crate::leanh::lean_box(0);
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5866_ == 0 {
                    v___x_5868_ = v___x_5865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_val_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkip_x3f___redArg___boxed(
    mut v_s_5874_: *mut crate::leanh::LeanObject,
    mut v_pos_5875_: *mut crate::leanh::LeanObject,
    mut v_inst_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_5874_, v_pos_5875_, v_inst_5876_);
    crate::leanh::lean_dec(v_pos_5875_);
    return v_res_5877_;
}
pub unsafe fn l_String_Slice_Pos_revSkip_x3f(
    mut v_00_u03c1_5878_: *mut crate::leanh::LeanObject,
    mut v_s_5879_: *mut crate::leanh::LeanObject,
    mut v_pos_5880_: *mut crate::leanh::LeanObject,
    mut v_pat_5881_: *mut crate::leanh::LeanObject,
    mut v_inst_5882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v_skipSuffix_x3f_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5896_: u8 = 0;
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5900_: u8 = 0;
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_unused_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5883_ = crate::leanh::lean_ctor_get(v_s_5879_, 0);
                v_startInclusive_5884_ = crate::leanh::lean_ctor_get(v_s_5879_, 1);
                v_isSharedCheck_5902_ = (!crate::leanh::lean_is_exclusive(v_s_5879_)) as u8;
                if v_isSharedCheck_5902_ == 0 {
                    v_unused_5903_ = crate::leanh::lean_ctor_get(v_s_5879_, 2);
                    crate::leanh::lean_dec(v_unused_5903_);
                    v___x_5886_ = v_s_5879_;
                    v_isShared_5887_ = v_isSharedCheck_5902_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_5884_);
                    crate::leanh::lean_inc(v_str_5883_);
                    crate::leanh::lean_dec(v_s_5879_);
                    v___x_5886_ = crate::leanh::lean_box(0);
                    v_isShared_5887_ = v_isSharedCheck_5902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_skipSuffix_x3f_5888_ = crate::leanh::lean_ctor_get(v_inst_5882_, 0);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5888_);
                crate::leanh::lean_dec_ref(v_inst_5882_);
                v___x_5889_ = lean_nat_add(v_startInclusive_5884_, v_pos_5880_);
                if v_isShared_5887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5886_, 2, v___x_5889_);
                    v___x_5891_ = v___x_5886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_str_5883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 1, v_startInclusive_5884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 2, v___x_5889_);
                    v___x_5891_ = v_reuseFailAlloc_5901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5892_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5888_, v___x_5891_);
                if crate::leanh::lean_obj_tag(v___x_5892_) == 0 {
                    return v___x_5892_;
                } else {
                    v_val_5893_ = crate::leanh::lean_ctor_get(v___x_5892_, 0);
                    v_isSharedCheck_5900_ = (!crate::leanh::lean_is_exclusive(v___x_5892_)) as u8;
                    if v_isSharedCheck_5900_ == 0 {
                        v___x_5895_ = v___x_5892_;
                        v_isShared_5896_ = v_isSharedCheck_5900_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5893_);
                        crate::leanh::lean_dec(v___x_5892_);
                        v___x_5895_ = crate::leanh::lean_box(0);
                        v_isShared_5896_ = v_isSharedCheck_5900_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5896_ == 0 {
                    v___x_5898_ = v___x_5895_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_val_5893_);
                    v___x_5898_ = v_reuseFailAlloc_5899_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkip_x3f___boxed(
    mut v_00_u03c1_5904_: *mut crate::leanh::LeanObject,
    mut v_s_5905_: *mut crate::leanh::LeanObject,
    mut v_pos_5906_: *mut crate::leanh::LeanObject,
    mut v_pat_5907_: *mut crate::leanh::LeanObject,
    mut v_inst_5908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5909_ = l_String_Slice_Pos_revSkip_x3f(
        v_00_u03c1_5904_,
        v_s_5905_,
        v_pos_5906_,
        v_pat_5907_,
        v_inst_5908_,
    );
    crate::leanh::lean_dec(v_pat_5907_);
    crate::leanh::lean_dec(v_pos_5906_);
    return v_res_5909_;
}
pub unsafe fn l_String_Slice_dropSuffix_x3f___redArg(
    mut v_s_5910_: *mut crate::leanh::LeanObject,
    mut v_inst_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipSuffix_x3f_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5918_: u8 = 0;
    let mut v_str_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5923_: u8 = 0;
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5931_: u8 = 0;
    let mut v_unused_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_5912_ = crate::leanh::lean_ctor_get(v_inst_5911_, 0);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5912_);
                crate::leanh::lean_dec_ref(v_inst_5911_);
                crate::leanh::lean_inc_ref(v_s_5910_);
                v___x_5913_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5912_, v_s_5910_);
                if crate::leanh::lean_obj_tag(v___x_5913_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_5910_);
                    v___x_5914_ = crate::leanh::lean_box(0);
                    return v___x_5914_;
                } else {
                    v_val_5915_ = crate::leanh::lean_ctor_get(v___x_5913_, 0);
                    v_isSharedCheck_5933_ = (!crate::leanh::lean_is_exclusive(v___x_5913_)) as u8;
                    if v_isSharedCheck_5933_ == 0 {
                        v___x_5917_ = v___x_5913_;
                        v_isShared_5918_ = v_isSharedCheck_5933_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5915_);
                        crate::leanh::lean_dec(v___x_5913_);
                        v___x_5917_ = crate::leanh::lean_box(0);
                        v_isShared_5918_ = v_isSharedCheck_5933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_5919_ = crate::leanh::lean_ctor_get(v_s_5910_, 0);
                v_startInclusive_5920_ = crate::leanh::lean_ctor_get(v_s_5910_, 1);
                v_isSharedCheck_5931_ = (!crate::leanh::lean_is_exclusive(v_s_5910_)) as u8;
                if v_isSharedCheck_5931_ == 0 {
                    v_unused_5932_ = crate::leanh::lean_ctor_get(v_s_5910_, 2);
                    crate::leanh::lean_dec(v_unused_5932_);
                    v___x_5922_ = v_s_5910_;
                    v_isShared_5923_ = v_isSharedCheck_5931_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_5920_);
                    crate::leanh::lean_inc(v_str_5919_);
                    crate::leanh::lean_dec(v_s_5910_);
                    v___x_5922_ = crate::leanh::lean_box(0);
                    v_isShared_5923_ = v_isSharedCheck_5931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5924_ = lean_nat_add(v_startInclusive_5920_, v_val_5915_);
                crate::leanh::lean_dec(v_val_5915_);
                if v_isShared_5923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5922_, 2, v___x_5924_);
                    v___x_5926_ = v___x_5922_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5930_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_str_5919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 1, v_startInclusive_5920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 2, v___x_5924_);
                    v___x_5926_ = v_reuseFailAlloc_5930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5917_, 0, v___x_5926_);
                    v___x_5928_ = v___x_5917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5926_);
                    v___x_5928_ = v_reuseFailAlloc_5929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropSuffix_x3f(
    mut v_00_u03c1_5934_: *mut crate::leanh::LeanObject,
    mut v_s_5935_: *mut crate::leanh::LeanObject,
    mut v_pat_5936_: *mut crate::leanh::LeanObject,
    mut v_inst_5937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipSuffix_x3f_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5944_: u8 = 0;
    let mut v_str_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5957_: u8 = 0;
    let mut v_unused_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_5938_ = crate::leanh::lean_ctor_get(v_inst_5937_, 0);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5938_);
                crate::leanh::lean_dec_ref(v_inst_5937_);
                crate::leanh::lean_inc_ref(v_s_5935_);
                v___x_5939_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5938_, v_s_5935_);
                if crate::leanh::lean_obj_tag(v___x_5939_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_5935_);
                    v___x_5940_ = crate::leanh::lean_box(0);
                    return v___x_5940_;
                } else {
                    v_val_5941_ = crate::leanh::lean_ctor_get(v___x_5939_, 0);
                    v_isSharedCheck_5959_ = (!crate::leanh::lean_is_exclusive(v___x_5939_)) as u8;
                    if v_isSharedCheck_5959_ == 0 {
                        v___x_5943_ = v___x_5939_;
                        v_isShared_5944_ = v_isSharedCheck_5959_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5941_);
                        crate::leanh::lean_dec(v___x_5939_);
                        v___x_5943_ = crate::leanh::lean_box(0);
                        v_isShared_5944_ = v_isSharedCheck_5959_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_5945_ = crate::leanh::lean_ctor_get(v_s_5935_, 0);
                v_startInclusive_5946_ = crate::leanh::lean_ctor_get(v_s_5935_, 1);
                v_isSharedCheck_5957_ = (!crate::leanh::lean_is_exclusive(v_s_5935_)) as u8;
                if v_isSharedCheck_5957_ == 0 {
                    v_unused_5958_ = crate::leanh::lean_ctor_get(v_s_5935_, 2);
                    crate::leanh::lean_dec(v_unused_5958_);
                    v___x_5948_ = v_s_5935_;
                    v_isShared_5949_ = v_isSharedCheck_5957_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_5946_);
                    crate::leanh::lean_inc(v_str_5945_);
                    crate::leanh::lean_dec(v_s_5935_);
                    v___x_5948_ = crate::leanh::lean_box(0);
                    v_isShared_5949_ = v_isSharedCheck_5957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5950_ = lean_nat_add(v_startInclusive_5946_, v_val_5941_);
                crate::leanh::lean_dec(v_val_5941_);
                if v_isShared_5949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5948_, 2, v___x_5950_);
                    v___x_5952_ = v___x_5948_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5956_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5956_, 0, v_str_5945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5956_, 1, v_startInclusive_5946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5956_, 2, v___x_5950_);
                    v___x_5952_ = v_reuseFailAlloc_5956_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5943_, 0, v___x_5952_);
                    v___x_5954_ = v___x_5943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5955_, 0, v___x_5952_);
                    v___x_5954_ = v_reuseFailAlloc_5955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropSuffix_x3f___boxed(
    mut v_00_u03c1_5960_: *mut crate::leanh::LeanObject,
    mut v_s_5961_: *mut crate::leanh::LeanObject,
    mut v_pat_5962_: *mut crate::leanh::LeanObject,
    mut v_inst_5963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5964_ =
        l_String_Slice_dropSuffix_x3f(v_00_u03c1_5960_, v_s_5961_, v_pat_5962_, v_inst_5963_);
    crate::leanh::lean_dec(v_pat_5962_);
    return v_res_5964_;
}
pub unsafe fn l_String_Slice_dropSuffix___redArg(
    mut v_s_5965_: *mut crate::leanh::LeanObject,
    mut v_inst_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipSuffix_x3f_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5974_: u8 = 0;
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5979_: u8 = 0;
    let mut v_unused_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_5967_ = crate::leanh::lean_ctor_get(v_inst_5966_, 0);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_5967_);
                crate::leanh::lean_dec_ref(v_inst_5966_);
                crate::leanh::lean_inc_ref(v_s_5965_);
                v___x_5968_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_5967_, v_s_5965_);
                if crate::leanh::lean_obj_tag(v___x_5968_) == 0 {
                    return v_s_5965_;
                } else {
                    v_val_5969_ = crate::leanh::lean_ctor_get(v___x_5968_, 0);
                    crate::leanh::lean_inc(v_val_5969_);
                    crate::leanh::lean_dec_ref_known(v___x_5968_, 1);
                    v_str_5970_ = crate::leanh::lean_ctor_get(v_s_5965_, 0);
                    v_startInclusive_5971_ = crate::leanh::lean_ctor_get(v_s_5965_, 1);
                    v_isSharedCheck_5979_ = (!crate::leanh::lean_is_exclusive(v_s_5965_)) as u8;
                    if v_isSharedCheck_5979_ == 0 {
                        v_unused_5980_ = crate::leanh::lean_ctor_get(v_s_5965_, 2);
                        crate::leanh::lean_dec(v_unused_5980_);
                        v___x_5973_ = v_s_5965_;
                        v_isShared_5974_ = v_isSharedCheck_5979_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_5971_);
                        crate::leanh::lean_inc(v_str_5970_);
                        crate::leanh::lean_dec(v_s_5965_);
                        v___x_5973_ = crate::leanh::lean_box(0);
                        v_isShared_5974_ = v_isSharedCheck_5979_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5975_ = lean_nat_add(v_startInclusive_5971_, v_val_5969_);
                crate::leanh::lean_dec(v_val_5969_);
                if v_isShared_5974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5973_, 2, v___x_5975_);
                    v___x_5977_ = v___x_5973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5978_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_str_5970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_startInclusive_5971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5978_, 2, v___x_5975_);
                    v___x_5977_ = v_reuseFailAlloc_5978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropSuffix(
    mut v_00_u03c1_5981_: *mut crate::leanh::LeanObject,
    mut v_s_5982_: *mut crate::leanh::LeanObject,
    mut v_pat_5983_: *mut crate::leanh::LeanObject,
    mut v_inst_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5985_ = l_String_Slice_dropSuffix___redArg(v_s_5982_, v_inst_5984_);
    return v___x_5985_;
}
pub unsafe fn l_String_Slice_dropSuffix___boxed(
    mut v_00_u03c1_5986_: *mut crate::leanh::LeanObject,
    mut v_s_5987_: *mut crate::leanh::LeanObject,
    mut v_pat_5988_: *mut crate::leanh::LeanObject,
    mut v_inst_5989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5990_ = l_String_Slice_dropSuffix(v_00_u03c1_5986_, v_s_5987_, v_pat_5988_, v_inst_5989_);
    crate::leanh::lean_dec(v_pat_5988_);
    return v_res_5990_;
}
pub unsafe fn l_String_Slice_dropEnd(
    mut v_s_5991_: *mut crate::leanh::LeanObject,
    mut v_n_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6000_: u8 = 0;
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6005_: u8 = 0;
    let mut v_unused_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_5993_ = crate::leanh::lean_ctor_get(v_s_5991_, 0);
                crate::leanh::lean_inc_ref(v_str_5993_);
                v_startInclusive_5994_ = crate::leanh::lean_ctor_get(v_s_5991_, 1);
                crate::leanh::lean_inc(v_startInclusive_5994_);
                v_endExclusive_5995_ = crate::leanh::lean_ctor_get(v_s_5991_, 2);
                v___x_5996_ = lean_nat_sub(v_endExclusive_5995_, v_startInclusive_5994_);
                v___x_5997_ = l_String_Slice_Pos_prevn(v_s_5991_, v___x_5996_, v_n_5992_);
                v_isSharedCheck_6005_ = (!crate::leanh::lean_is_exclusive(v_s_5991_)) as u8;
                if v_isSharedCheck_6005_ == 0 {
                    v_unused_6006_ = crate::leanh::lean_ctor_get(v_s_5991_, 2);
                    crate::leanh::lean_dec(v_unused_6006_);
                    v_unused_6007_ = crate::leanh::lean_ctor_get(v_s_5991_, 1);
                    crate::leanh::lean_dec(v_unused_6007_);
                    v_unused_6008_ = crate::leanh::lean_ctor_get(v_s_5991_, 0);
                    crate::leanh::lean_dec(v_unused_6008_);
                    v___x_5999_ = v_s_5991_;
                    v_isShared_6000_ = v_isSharedCheck_6005_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_5991_);
                    v___x_5999_ = crate::leanh::lean_box(0);
                    v_isShared_6000_ = v_isSharedCheck_6005_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6001_ = lean_nat_add(v_startInclusive_5994_, v___x_5997_);
                crate::leanh::lean_dec(v___x_5997_);
                if v_isShared_6000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5999_, 2, v___x_6001_);
                    v___x_6003_ = v___x_5999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6004_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_str_5993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6004_, 1, v_startInclusive_5994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6004_, 2, v___x_6001_);
                    v___x_6003_ = v_reuseFailAlloc_6004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___redArg(
    mut v_s_6009_: *mut crate::leanh::LeanObject,
    mut v_pos_6010_: *mut crate::leanh::LeanObject,
    mut v_inst_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_skipSuffix_x3f_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6012_ = crate::leanh::lean_ctor_get(v_s_6009_, 0);
                v_startInclusive_6013_ = crate::leanh::lean_ctor_get(v_s_6009_, 1);
                v_skipSuffix_x3f_6014_ = crate::leanh::lean_ctor_get(v_inst_6011_, 0);
                v___x_6015_ = lean_nat_add(v_startInclusive_6013_, v_pos_6010_);
                crate::leanh::lean_inc(v_startInclusive_6013_);
                crate::leanh::lean_inc_ref(v_str_6012_);
                v___x_6016_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6016_, 0, v_str_6012_);
                crate::leanh::lean_ctor_set(v___x_6016_, 1, v_startInclusive_6013_);
                crate::leanh::lean_ctor_set(v___x_6016_, 2, v___x_6015_);
                crate::leanh::lean_inc_ref(v_skipSuffix_x3f_6014_);
                v___x_6017_ = crate::leanh::lean_apply_1(v_skipSuffix_x3f_6014_, v___x_6016_);
                if crate::leanh::lean_obj_tag(v___x_6017_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_6011_);
                    return v_pos_6010_;
                } else {
                    v_val_6018_ = crate::leanh::lean_ctor_get(v___x_6017_, 0);
                    crate::leanh::lean_inc(v_val_6018_);
                    crate::leanh::lean_dec_ref_known(v___x_6017_, 1);
                    v___x_6019_ = lean_nat_dec_lt(v_val_6018_, v_pos_6010_);
                    if v___x_6019_ == 0 {
                        crate::leanh::lean_dec(v_val_6018_);
                        crate::leanh::lean_dec_ref(v_inst_6011_);
                        return v_pos_6010_;
                    } else {
                        crate::leanh::lean_dec(v_pos_6010_);
                        v_pos_6010_ = v_val_6018_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___redArg___boxed(
    mut v_s_6021_: *mut crate::leanh::LeanObject,
    mut v_pos_6022_: *mut crate::leanh::LeanObject,
    mut v_inst_6023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6024_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6021_, v_pos_6022_, v_inst_6023_);
    crate::leanh::lean_dec_ref(v_s_6021_);
    return v_res_6024_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile(
    mut v_00_u03c1_6025_: *mut crate::leanh::LeanObject,
    mut v_s_6026_: *mut crate::leanh::LeanObject,
    mut v_pos_6027_: *mut crate::leanh::LeanObject,
    mut v_pat_6028_: *mut crate::leanh::LeanObject,
    mut v_inst_6029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6030_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6026_, v_pos_6027_, v_inst_6029_);
    return v___x_6030_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___boxed(
    mut v_00_u03c1_6031_: *mut crate::leanh::LeanObject,
    mut v_s_6032_: *mut crate::leanh::LeanObject,
    mut v_pos_6033_: *mut crate::leanh::LeanObject,
    mut v_pat_6034_: *mut crate::leanh::LeanObject,
    mut v_inst_6035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6036_ = l_String_Slice_Pos_revSkipWhile(
        v_00_u03c1_6031_,
        v_s_6032_,
        v_pos_6033_,
        v_pat_6034_,
        v_inst_6035_,
    );
    crate::leanh::lean_dec(v_pat_6034_);
    crate::leanh::lean_dec_ref(v_s_6032_);
    return v_res_6036_;
}
pub unsafe fn l_String_Slice_skipSuffixWhile___redArg(
    mut v_s_6037_: *mut crate::leanh::LeanObject,
    mut v_inst_6038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_6039_ = crate::leanh::lean_ctor_get(v_s_6037_, 1);
    v_endExclusive_6040_ = crate::leanh::lean_ctor_get(v_s_6037_, 2);
    v___x_6041_ = lean_nat_sub(v_endExclusive_6040_, v_startInclusive_6039_);
    v___x_6042_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6037_, v___x_6041_, v_inst_6038_);
    return v___x_6042_;
}
pub unsafe fn l_String_Slice_skipSuffixWhile___redArg___boxed(
    mut v_s_6043_: *mut crate::leanh::LeanObject,
    mut v_inst_6044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6045_ = l_String_Slice_skipSuffixWhile___redArg(v_s_6043_, v_inst_6044_);
    crate::leanh::lean_dec_ref(v_s_6043_);
    return v_res_6045_;
}
pub unsafe fn l_String_Slice_skipSuffixWhile(
    mut v_00_u03c1_6046_: *mut crate::leanh::LeanObject,
    mut v_s_6047_: *mut crate::leanh::LeanObject,
    mut v_pat_6048_: *mut crate::leanh::LeanObject,
    mut v_inst_6049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_6050_ = crate::leanh::lean_ctor_get(v_s_6047_, 1);
    v_endExclusive_6051_ = crate::leanh::lean_ctor_get(v_s_6047_, 2);
    v___x_6052_ = lean_nat_sub(v_endExclusive_6051_, v_startInclusive_6050_);
    v___x_6053_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6047_, v___x_6052_, v_inst_6049_);
    return v___x_6053_;
}
pub unsafe fn l_String_Slice_skipSuffixWhile___boxed(
    mut v_00_u03c1_6054_: *mut crate::leanh::LeanObject,
    mut v_s_6055_: *mut crate::leanh::LeanObject,
    mut v_pat_6056_: *mut crate::leanh::LeanObject,
    mut v_inst_6057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6058_ =
        l_String_Slice_skipSuffixWhile(v_00_u03c1_6054_, v_s_6055_, v_pat_6056_, v_inst_6057_);
    crate::leanh::lean_dec(v_pat_6056_);
    crate::leanh::lean_dec_ref(v_s_6055_);
    return v_res_6058_;
}
pub unsafe fn l_String_Slice_revAll___redArg(
    mut v_s_6059_: *mut crate::leanh::LeanObject,
    mut v_inst_6060_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: u8 = 0;
    v_startInclusive_6061_ = crate::leanh::lean_ctor_get(v_s_6059_, 1);
    v_endExclusive_6062_ = crate::leanh::lean_ctor_get(v_s_6059_, 2);
    v___x_6063_ = lean_nat_sub(v_endExclusive_6062_, v_startInclusive_6061_);
    v___x_6064_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6059_, v___x_6063_, v_inst_6060_);
    v___x_6065_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6066_ = lean_nat_dec_eq(v___x_6064_, v___x_6065_);
    crate::leanh::lean_dec(v___x_6064_);
    return v___x_6066_;
}
pub unsafe fn l_String_Slice_revAll___redArg___boxed(
    mut v_s_6067_: *mut crate::leanh::LeanObject,
    mut v_inst_6068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6069_: u8 = 0;
    let mut v_r_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6069_ = l_String_Slice_revAll___redArg(v_s_6067_, v_inst_6068_);
    crate::leanh::lean_dec_ref(v_s_6067_);
    v_r_6070_ = crate::leanh::lean_box((v_res_6069_) as usize);
    return v_r_6070_;
}
pub unsafe fn l_String_Slice_revAll(
    mut v_00_u03c1_6071_: *mut crate::leanh::LeanObject,
    mut v_s_6072_: *mut crate::leanh::LeanObject,
    mut v_pat_6073_: *mut crate::leanh::LeanObject,
    mut v_inst_6074_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: u8 = 0;
    v_startInclusive_6075_ = crate::leanh::lean_ctor_get(v_s_6072_, 1);
    v_endExclusive_6076_ = crate::leanh::lean_ctor_get(v_s_6072_, 2);
    v___x_6077_ = lean_nat_sub(v_endExclusive_6076_, v_startInclusive_6075_);
    v___x_6078_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_6072_, v___x_6077_, v_inst_6074_);
    v___x_6079_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6080_ = lean_nat_dec_eq(v___x_6078_, v___x_6079_);
    crate::leanh::lean_dec(v___x_6078_);
    return v___x_6080_;
}
pub unsafe fn l_String_Slice_revAll___boxed(
    mut v_00_u03c1_6081_: *mut crate::leanh::LeanObject,
    mut v_s_6082_: *mut crate::leanh::LeanObject,
    mut v_pat_6083_: *mut crate::leanh::LeanObject,
    mut v_inst_6084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6085_: u8 = 0;
    let mut v_r_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6085_ = l_String_Slice_revAll(v_00_u03c1_6081_, v_s_6082_, v_pat_6083_, v_inst_6084_);
    crate::leanh::lean_dec(v_pat_6083_);
    crate::leanh::lean_dec_ref(v_s_6082_);
    v_r_6086_ = crate::leanh::lean_box((v_res_6085_) as usize);
    return v_r_6086_;
}
pub unsafe fn l_String_Slice_dropEndWhile___redArg(
    mut v_s_6087_: *mut crate::leanh::LeanObject,
    mut v_inst_6088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6096_: u8 = 0;
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6101_: u8 = 0;
    let mut v_unused_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6089_ = crate::leanh::lean_ctor_get(v_s_6087_, 0);
                crate::leanh::lean_inc_ref(v_str_6089_);
                v_startInclusive_6090_ = crate::leanh::lean_ctor_get(v_s_6087_, 1);
                crate::leanh::lean_inc(v_startInclusive_6090_);
                v_endExclusive_6091_ = crate::leanh::lean_ctor_get(v_s_6087_, 2);
                v___x_6092_ = lean_nat_sub(v_endExclusive_6091_, v_startInclusive_6090_);
                v___x_6093_ =
                    l_String_Slice_Pos_revSkipWhile___redArg(v_s_6087_, v___x_6092_, v_inst_6088_);
                v_isSharedCheck_6101_ = (!crate::leanh::lean_is_exclusive(v_s_6087_)) as u8;
                if v_isSharedCheck_6101_ == 0 {
                    v_unused_6102_ = crate::leanh::lean_ctor_get(v_s_6087_, 2);
                    crate::leanh::lean_dec(v_unused_6102_);
                    v_unused_6103_ = crate::leanh::lean_ctor_get(v_s_6087_, 1);
                    crate::leanh::lean_dec(v_unused_6103_);
                    v_unused_6104_ = crate::leanh::lean_ctor_get(v_s_6087_, 0);
                    crate::leanh::lean_dec(v_unused_6104_);
                    v___x_6095_ = v_s_6087_;
                    v_isShared_6096_ = v_isSharedCheck_6101_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6087_);
                    v___x_6095_ = crate::leanh::lean_box(0);
                    v_isShared_6096_ = v_isSharedCheck_6101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6097_ = lean_nat_add(v_startInclusive_6090_, v___x_6093_);
                crate::leanh::lean_dec(v___x_6093_);
                if v_isShared_6096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6095_, 2, v___x_6097_);
                    v___x_6099_ = v___x_6095_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6100_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 0, v_str_6089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 1, v_startInclusive_6090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 2, v___x_6097_);
                    v___x_6099_ = v_reuseFailAlloc_6100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropEndWhile(
    mut v_00_u03c1_6105_: *mut crate::leanh::LeanObject,
    mut v_s_6106_: *mut crate::leanh::LeanObject,
    mut v_pat_6107_: *mut crate::leanh::LeanObject,
    mut v_inst_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6116_: u8 = 0;
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6121_: u8 = 0;
    let mut v_unused_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6109_ = crate::leanh::lean_ctor_get(v_s_6106_, 0);
                crate::leanh::lean_inc_ref(v_str_6109_);
                v_startInclusive_6110_ = crate::leanh::lean_ctor_get(v_s_6106_, 1);
                crate::leanh::lean_inc(v_startInclusive_6110_);
                v_endExclusive_6111_ = crate::leanh::lean_ctor_get(v_s_6106_, 2);
                v___x_6112_ = lean_nat_sub(v_endExclusive_6111_, v_startInclusive_6110_);
                v___x_6113_ =
                    l_String_Slice_Pos_revSkipWhile___redArg(v_s_6106_, v___x_6112_, v_inst_6108_);
                v_isSharedCheck_6121_ = (!crate::leanh::lean_is_exclusive(v_s_6106_)) as u8;
                if v_isSharedCheck_6121_ == 0 {
                    v_unused_6122_ = crate::leanh::lean_ctor_get(v_s_6106_, 2);
                    crate::leanh::lean_dec(v_unused_6122_);
                    v_unused_6123_ = crate::leanh::lean_ctor_get(v_s_6106_, 1);
                    crate::leanh::lean_dec(v_unused_6123_);
                    v_unused_6124_ = crate::leanh::lean_ctor_get(v_s_6106_, 0);
                    crate::leanh::lean_dec(v_unused_6124_);
                    v___x_6115_ = v_s_6106_;
                    v_isShared_6116_ = v_isSharedCheck_6121_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6106_);
                    v___x_6115_ = crate::leanh::lean_box(0);
                    v_isShared_6116_ = v_isSharedCheck_6121_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6117_ = lean_nat_add(v_startInclusive_6110_, v___x_6113_);
                crate::leanh::lean_dec(v___x_6113_);
                if v_isShared_6116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6115_, 2, v___x_6117_);
                    v___x_6119_ = v___x_6115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6120_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6120_, 0, v_str_6109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6120_, 1, v_startInclusive_6110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6120_, 2, v___x_6117_);
                    v___x_6119_ = v_reuseFailAlloc_6120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropEndWhile___boxed(
    mut v_00_u03c1_6125_: *mut crate::leanh::LeanObject,
    mut v_s_6126_: *mut crate::leanh::LeanObject,
    mut v_pat_6127_: *mut crate::leanh::LeanObject,
    mut v_inst_6128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6129_ =
        l_String_Slice_dropEndWhile(v_00_u03c1_6125_, v_s_6126_, v_pat_6127_, v_inst_6128_);
    crate::leanh::lean_dec(v_pat_6127_);
    return v_res_6129_;
}
pub unsafe fn _init_l_String_Slice_trimAsciiEnd___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6130_ = l_String_Slice_trimAsciiStart___closed__0;
    v___x_6131_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_6130_);
    return v___x_6131_;
}
pub unsafe fn l_String_Slice_trimAsciiEnd(
    mut v_s_6132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6141_: u8 = 0;
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6146_: u8 = 0;
    let mut v_unused_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6133_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_Slice_trimAsciiEnd___closed__0),
                    core::ptr::addr_of_mut!(l_String_Slice_trimAsciiEnd___closed__0_once),
                    _init_l_String_Slice_trimAsciiEnd___closed__0,
                );
                v_str_6134_ = crate::leanh::lean_ctor_get(v_s_6132_, 0);
                crate::leanh::lean_inc_ref(v_str_6134_);
                v_startInclusive_6135_ = crate::leanh::lean_ctor_get(v_s_6132_, 1);
                crate::leanh::lean_inc(v_startInclusive_6135_);
                v_endExclusive_6136_ = crate::leanh::lean_ctor_get(v_s_6132_, 2);
                v___x_6137_ = lean_nat_sub(v_endExclusive_6136_, v_startInclusive_6135_);
                v___x_6138_ =
                    l_String_Slice_Pos_revSkipWhile___redArg(v_s_6132_, v___x_6137_, v___x_6133_);
                v_isSharedCheck_6146_ = (!crate::leanh::lean_is_exclusive(v_s_6132_)) as u8;
                if v_isSharedCheck_6146_ == 0 {
                    v_unused_6147_ = crate::leanh::lean_ctor_get(v_s_6132_, 2);
                    crate::leanh::lean_dec(v_unused_6147_);
                    v_unused_6148_ = crate::leanh::lean_ctor_get(v_s_6132_, 1);
                    crate::leanh::lean_dec(v_unused_6148_);
                    v_unused_6149_ = crate::leanh::lean_ctor_get(v_s_6132_, 0);
                    crate::leanh::lean_dec(v_unused_6149_);
                    v___x_6140_ = v_s_6132_;
                    v_isShared_6141_ = v_isSharedCheck_6146_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6132_);
                    v___x_6140_ = crate::leanh::lean_box(0);
                    v_isShared_6141_ = v_isSharedCheck_6146_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6142_ = lean_nat_add(v_startInclusive_6135_, v___x_6138_);
                crate::leanh::lean_dec(v___x_6138_);
                if v_isShared_6141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6140_, 2, v___x_6142_);
                    v___x_6144_ = v___x_6140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6145_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_str_6134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6145_, 1, v_startInclusive_6135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6145_, 2, v___x_6142_);
                    v___x_6144_ = v_reuseFailAlloc_6145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeEnd(
    mut v_s_6150_: *mut crate::leanh::LeanObject,
    mut v_n_6151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v_unused_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6152_ = crate::leanh::lean_ctor_get(v_s_6150_, 0);
                crate::leanh::lean_inc_ref(v_str_6152_);
                v_startInclusive_6153_ = crate::leanh::lean_ctor_get(v_s_6150_, 1);
                crate::leanh::lean_inc(v_startInclusive_6153_);
                v_endExclusive_6154_ = crate::leanh::lean_ctor_get(v_s_6150_, 2);
                crate::leanh::lean_inc(v_endExclusive_6154_);
                v___x_6155_ = lean_nat_sub(v_endExclusive_6154_, v_startInclusive_6153_);
                v___x_6156_ = l_String_Slice_Pos_prevn(v_s_6150_, v___x_6155_, v_n_6151_);
                v_isSharedCheck_6164_ = (!crate::leanh::lean_is_exclusive(v_s_6150_)) as u8;
                if v_isSharedCheck_6164_ == 0 {
                    v_unused_6165_ = crate::leanh::lean_ctor_get(v_s_6150_, 2);
                    crate::leanh::lean_dec(v_unused_6165_);
                    v_unused_6166_ = crate::leanh::lean_ctor_get(v_s_6150_, 1);
                    crate::leanh::lean_dec(v_unused_6166_);
                    v_unused_6167_ = crate::leanh::lean_ctor_get(v_s_6150_, 0);
                    crate::leanh::lean_dec(v_unused_6167_);
                    v___x_6158_ = v_s_6150_;
                    v_isShared_6159_ = v_isSharedCheck_6164_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6150_);
                    v___x_6158_ = crate::leanh::lean_box(0);
                    v_isShared_6159_ = v_isSharedCheck_6164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6160_ = lean_nat_add(v_startInclusive_6153_, v___x_6156_);
                crate::leanh::lean_dec(v___x_6156_);
                crate::leanh::lean_dec(v_startInclusive_6153_);
                if v_isShared_6159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6158_, 1, v___x_6160_);
                    v___x_6162_ = v___x_6158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6163_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_str_6152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 1, v___x_6160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 2, v_endExclusive_6154_);
                    v___x_6162_ = v_reuseFailAlloc_6163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeEndWhile___redArg(
    mut v_s_6168_: *mut crate::leanh::LeanObject,
    mut v_inst_6169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_unused_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6170_ = crate::leanh::lean_ctor_get(v_s_6168_, 0);
                crate::leanh::lean_inc_ref(v_str_6170_);
                v_startInclusive_6171_ = crate::leanh::lean_ctor_get(v_s_6168_, 1);
                crate::leanh::lean_inc(v_startInclusive_6171_);
                v_endExclusive_6172_ = crate::leanh::lean_ctor_get(v_s_6168_, 2);
                crate::leanh::lean_inc(v_endExclusive_6172_);
                v___x_6173_ = lean_nat_sub(v_endExclusive_6172_, v_startInclusive_6171_);
                v___x_6174_ =
                    l_String_Slice_Pos_revSkipWhile___redArg(v_s_6168_, v___x_6173_, v_inst_6169_);
                v_isSharedCheck_6182_ = (!crate::leanh::lean_is_exclusive(v_s_6168_)) as u8;
                if v_isSharedCheck_6182_ == 0 {
                    v_unused_6183_ = crate::leanh::lean_ctor_get(v_s_6168_, 2);
                    crate::leanh::lean_dec(v_unused_6183_);
                    v_unused_6184_ = crate::leanh::lean_ctor_get(v_s_6168_, 1);
                    crate::leanh::lean_dec(v_unused_6184_);
                    v_unused_6185_ = crate::leanh::lean_ctor_get(v_s_6168_, 0);
                    crate::leanh::lean_dec(v_unused_6185_);
                    v___x_6176_ = v_s_6168_;
                    v_isShared_6177_ = v_isSharedCheck_6182_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6168_);
                    v___x_6176_ = crate::leanh::lean_box(0);
                    v_isShared_6177_ = v_isSharedCheck_6182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6178_ = lean_nat_add(v_startInclusive_6171_, v___x_6174_);
                crate::leanh::lean_dec(v___x_6174_);
                crate::leanh::lean_dec(v_startInclusive_6171_);
                if v_isShared_6177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6176_, 1, v___x_6178_);
                    v___x_6180_ = v___x_6176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_str_6170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 1, v___x_6178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 2, v_endExclusive_6172_);
                    v___x_6180_ = v_reuseFailAlloc_6181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeEndWhile(
    mut v_00_u03c1_6186_: *mut crate::leanh::LeanObject,
    mut v_s_6187_: *mut crate::leanh::LeanObject,
    mut v_pat_6188_: *mut crate::leanh::LeanObject,
    mut v_inst_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6197_: u8 = 0;
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_unused_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6190_ = crate::leanh::lean_ctor_get(v_s_6187_, 0);
                crate::leanh::lean_inc_ref(v_str_6190_);
                v_startInclusive_6191_ = crate::leanh::lean_ctor_get(v_s_6187_, 1);
                crate::leanh::lean_inc(v_startInclusive_6191_);
                v_endExclusive_6192_ = crate::leanh::lean_ctor_get(v_s_6187_, 2);
                crate::leanh::lean_inc(v_endExclusive_6192_);
                v___x_6193_ = lean_nat_sub(v_endExclusive_6192_, v_startInclusive_6191_);
                v___x_6194_ =
                    l_String_Slice_Pos_revSkipWhile___redArg(v_s_6187_, v___x_6193_, v_inst_6189_);
                v_isSharedCheck_6202_ = (!crate::leanh::lean_is_exclusive(v_s_6187_)) as u8;
                if v_isSharedCheck_6202_ == 0 {
                    v_unused_6203_ = crate::leanh::lean_ctor_get(v_s_6187_, 2);
                    crate::leanh::lean_dec(v_unused_6203_);
                    v_unused_6204_ = crate::leanh::lean_ctor_get(v_s_6187_, 1);
                    crate::leanh::lean_dec(v_unused_6204_);
                    v_unused_6205_ = crate::leanh::lean_ctor_get(v_s_6187_, 0);
                    crate::leanh::lean_dec(v_unused_6205_);
                    v___x_6196_ = v_s_6187_;
                    v_isShared_6197_ = v_isSharedCheck_6202_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6187_);
                    v___x_6196_ = crate::leanh::lean_box(0);
                    v_isShared_6197_ = v_isSharedCheck_6202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6198_ = lean_nat_add(v_startInclusive_6191_, v___x_6194_);
                crate::leanh::lean_dec(v___x_6194_);
                crate::leanh::lean_dec(v_startInclusive_6191_);
                if v_isShared_6197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6196_, 1, v___x_6198_);
                    v___x_6200_ = v___x_6196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6201_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_str_6190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 1, v___x_6198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 2, v_endExclusive_6192_);
                    v___x_6200_ = v_reuseFailAlloc_6201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_takeEndWhile___boxed(
    mut v_00_u03c1_6206_: *mut crate::leanh::LeanObject,
    mut v_s_6207_: *mut crate::leanh::LeanObject,
    mut v_pat_6208_: *mut crate::leanh::LeanObject,
    mut v_inst_6209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6210_ =
        l_String_Slice_takeEndWhile(v_00_u03c1_6206_, v_s_6207_, v_pat_6208_, v_inst_6209_);
    crate::leanh::lean_dec(v_pat_6208_);
    return v_res_6210_;
}
pub unsafe fn l_String_Slice_revFind_x3f___redArg(
    mut v_inst_6211_: *mut crate::leanh::LeanObject,
    mut v_s_6212_: *mut crate::leanh::LeanObject,
    mut v_inst_6213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6214_ = l_String_Slice_replace___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_s_6212_);
    v_searcher_6215_ = crate::leanh::lean_apply_1(v_inst_6213_, v_s_6212_);
    v___x_6216_ = crate::leanh::lean_box(0);
    v___f_6217_ = l_String_Slice_find_x3f___redArg___closed__0;
    v___x_6218_ = crate::leanh::lean_apply_7(
        v_inst_6211_,
        v_s_6212_,
        v___f_6214_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_searcher_6215_,
        v___x_6216_,
        v___f_6217_,
    );
    return v___x_6218_;
}
pub unsafe fn l_String_Slice_revFind_x3f(
    mut v_00_u03c3_6219_: *mut crate::leanh::LeanObject,
    mut v_inst_6220_: *mut crate::leanh::LeanObject,
    mut v_inst_6221_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_6222_: *mut crate::leanh::LeanObject,
    mut v_s_6223_: *mut crate::leanh::LeanObject,
    mut v_pat_6224_: *mut crate::leanh::LeanObject,
    mut v_inst_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6226_ = l_String_Slice_revFind_x3f___redArg(v_inst_6221_, v_s_6223_, v_inst_6225_);
    return v___x_6226_;
}
pub unsafe fn l_String_Slice_revFind_x3f___boxed(
    mut v_00_u03c3_6227_: *mut crate::leanh::LeanObject,
    mut v_inst_6228_: *mut crate::leanh::LeanObject,
    mut v_inst_6229_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_6230_: *mut crate::leanh::LeanObject,
    mut v_s_6231_: *mut crate::leanh::LeanObject,
    mut v_pat_6232_: *mut crate::leanh::LeanObject,
    mut v_inst_6233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6234_ = l_String_Slice_revFind_x3f(
        v_00_u03c3_6227_,
        v_inst_6228_,
        v_inst_6229_,
        v_00_u03c1_6230_,
        v_s_6231_,
        v_pat_6232_,
        v_inst_6233_,
    );
    crate::leanh::lean_dec(v_pat_6232_);
    crate::leanh::lean_dec(v_inst_6228_);
    return v_res_6234_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(
    mut v_s_6235_: *mut crate::leanh::LeanObject,
    mut v_pos_6236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: u8 = 0;
    let mut v___y_6248_: u8 = 0;
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: u8 = 0;
    let mut v___x_6252_: u32 = 0;
    let mut v___y_6254_: u8 = 0;
    let mut v___x_6255_: u32 = 0;
    let mut v___x_6256_: u8 = 0;
    let mut v___x_6257_: u32 = 0;
    let mut v___x_6258_: u8 = 0;
    let mut v___x_6259_: u32 = 0;
    let mut v___x_6260_: u8 = 0;
    let mut v___x_6261_: u32 = 0;
    let mut v___x_6262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6237_ = crate::leanh::lean_ctor_get(v_s_6235_, 0);
                v_startInclusive_6238_ = crate::leanh::lean_ctor_get(v_s_6235_, 1);
                v_endExclusive_6239_ = crate::leanh::lean_ctor_get(v_s_6235_, 2);
                v___x_6240_ = lean_nat_add(v_startInclusive_6238_, v_pos_6236_);
                v___x_6249_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6250_ = lean_nat_sub(v_endExclusive_6239_, v___x_6240_);
                v___x_6251_ = lean_nat_dec_eq(v___x_6249_, v___x_6250_);
                crate::leanh::lean_dec(v___x_6250_);
                if v___x_6251_ == 0 {
                    v___x_6252_ = lean_string_utf8_get_fast(v_str_6237_, v___x_6240_);
                    v___x_6259_ = 32;
                    v___x_6260_ = lean_uint32_dec_eq(v___x_6252_, v___x_6259_);
                    if v___x_6260_ == 0 {
                        v___x_6261_ = 9;
                        v___x_6262_ = lean_uint32_dec_eq(v___x_6252_, v___x_6261_);
                        v___y_6254_ = v___x_6262_;
                        state = 3;
                        continue;
                    } else {
                        v___y_6254_ = v___x_6260_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6240_);
                    return v_pos_6236_;
                }
            }
            1 => {
                v___x_6242_ = lean_string_utf8_next_fast(v_str_6237_, v___x_6240_);
                v___x_6243_ = lean_nat_sub(v___x_6242_, v___x_6240_);
                crate::leanh::lean_dec(v___x_6240_);
                v___x_6244_ = lean_nat_add(v_pos_6236_, v___x_6243_);
                crate::leanh::lean_dec(v___x_6243_);
                v___x_6245_ = lean_nat_dec_lt(v_pos_6236_, v___x_6244_);
                if v___x_6245_ == 0 {
                    crate::leanh::lean_dec(v___x_6244_);
                    return v_pos_6236_;
                } else {
                    crate::leanh::lean_dec(v_pos_6236_);
                    v_pos_6236_ = v___x_6244_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_6248_ == 0 {
                    crate::leanh::lean_dec(v___x_6240_);
                    return v_pos_6236_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_6254_ == 0 {
                    v___x_6255_ = 13;
                    v___x_6256_ = lean_uint32_dec_eq(v___x_6252_, v___x_6255_);
                    if v___x_6256_ == 0 {
                        v___x_6257_ = 10;
                        v___x_6258_ = lean_uint32_dec_eq(v___x_6252_, v___x_6257_);
                        v___y_6248_ = v___x_6258_;
                        state = 2;
                        continue;
                    } else {
                        v___y_6248_ = v___x_6256_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(
    mut v_s_6263_: *mut crate::leanh::LeanObject,
    mut v_pos_6264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6265_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(
        v_s_6263_,
        v_pos_6264_,
    );
    crate::leanh::lean_dec_ref(v_s_6263_);
    return v_res_6265_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(
    mut v_s_6266_: *mut crate::leanh::LeanObject,
    mut v_pos_6267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: u8 = 0;
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: u8 = 0;
    let mut v___y_6282_: u8 = 0;
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: u32 = 0;
    let mut v___y_6286_: u8 = 0;
    let mut v___x_6287_: u32 = 0;
    let mut v___x_6288_: u8 = 0;
    let mut v___x_6289_: u32 = 0;
    let mut v___x_6290_: u8 = 0;
    let mut v___x_6291_: u32 = 0;
    let mut v___x_6292_: u8 = 0;
    let mut v___x_6293_: u32 = 0;
    let mut v___x_6294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6268_ = crate::leanh::lean_ctor_get(v_s_6266_, 0);
                v_startInclusive_6269_ = crate::leanh::lean_ctor_get(v_s_6266_, 1);
                v___x_6270_ = lean_nat_add(v_startInclusive_6269_, v_pos_6267_);
                v___x_6271_ = lean_nat_sub(v___x_6270_, v_startInclusive_6269_);
                v___x_6272_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6273_ = lean_nat_dec_eq(v___x_6271_, v___x_6272_);
                if v___x_6273_ == 0 {
                    crate::leanh::lean_inc(v_startInclusive_6269_);
                    crate::leanh::lean_inc_ref(v_str_6268_);
                    v___x_6274_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6274_, 0, v_str_6268_);
                    crate::leanh::lean_ctor_set(v___x_6274_, 1, v_startInclusive_6269_);
                    crate::leanh::lean_ctor_set(v___x_6274_, 2, v___x_6270_);
                    v___x_6275_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6276_ = lean_nat_sub(v___x_6271_, v___x_6275_);
                    crate::leanh::lean_dec(v___x_6271_);
                    v___x_6277_ = l_String_Slice_posLE(v___x_6274_, v___x_6276_);
                    crate::leanh::lean_dec_ref_known(v___x_6274_, 3);
                    v___x_6283_ = lean_nat_add(v_startInclusive_6269_, v___x_6277_);
                    v___x_6284_ = lean_string_utf8_get_fast(v_str_6268_, v___x_6283_);
                    crate::leanh::lean_dec(v___x_6283_);
                    v___x_6291_ = 32;
                    v___x_6292_ = lean_uint32_dec_eq(v___x_6284_, v___x_6291_);
                    if v___x_6292_ == 0 {
                        v___x_6293_ = 9;
                        v___x_6294_ = lean_uint32_dec_eq(v___x_6284_, v___x_6293_);
                        v___y_6286_ = v___x_6294_;
                        state = 3;
                        continue;
                    } else {
                        v___y_6286_ = v___x_6292_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6271_);
                    crate::leanh::lean_dec(v___x_6270_);
                    return v_pos_6267_;
                }
            }
            1 => {
                v___x_6279_ = lean_nat_dec_lt(v___x_6277_, v_pos_6267_);
                if v___x_6279_ == 0 {
                    crate::leanh::lean_dec(v___x_6277_);
                    return v_pos_6267_;
                } else {
                    crate::leanh::lean_dec(v_pos_6267_);
                    v_pos_6267_ = v___x_6277_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_6282_ == 0 {
                    crate::leanh::lean_dec(v___x_6277_);
                    return v_pos_6267_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_6286_ == 0 {
                    v___x_6287_ = 13;
                    v___x_6288_ = lean_uint32_dec_eq(v___x_6284_, v___x_6287_);
                    if v___x_6288_ == 0 {
                        v___x_6289_ = 10;
                        v___x_6290_ = lean_uint32_dec_eq(v___x_6284_, v___x_6289_);
                        v___y_6282_ = v___x_6290_;
                        state = 2;
                        continue;
                    } else {
                        v___y_6282_ = v___x_6288_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(
    mut v_s_6295_: *mut crate::leanh::LeanObject,
    mut v_pos_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(
        v_s_6295_,
        v_pos_6296_,
    );
    crate::leanh::lean_dec_ref(v_s_6295_);
    return v_res_6297_;
}
pub unsafe fn l_String_Slice_trimAscii(
    mut v_s_6298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6315_: u8 = 0;
    let mut v_unused_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6299_ = crate::leanh::lean_ctor_get(v_s_6298_, 0);
                crate::leanh::lean_inc_ref(v_str_6299_);
                v_startInclusive_6300_ = crate::leanh::lean_ctor_get(v_s_6298_, 1);
                crate::leanh::lean_inc(v_startInclusive_6300_);
                v_endExclusive_6301_ = crate::leanh::lean_ctor_get(v_s_6298_, 2);
                crate::leanh::lean_inc(v_endExclusive_6301_);
                v___x_6302_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6303_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(
                    v_s_6298_,
                    v___x_6302_,
                );
                v_isSharedCheck_6315_ = (!crate::leanh::lean_is_exclusive(v_s_6298_)) as u8;
                if v_isSharedCheck_6315_ == 0 {
                    v_unused_6316_ = crate::leanh::lean_ctor_get(v_s_6298_, 2);
                    crate::leanh::lean_dec(v_unused_6316_);
                    v_unused_6317_ = crate::leanh::lean_ctor_get(v_s_6298_, 1);
                    crate::leanh::lean_dec(v_unused_6317_);
                    v_unused_6318_ = crate::leanh::lean_ctor_get(v_s_6298_, 0);
                    crate::leanh::lean_dec(v_unused_6318_);
                    v___x_6305_ = v_s_6298_;
                    v_isShared_6306_ = v_isSharedCheck_6315_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_6298_);
                    v___x_6305_ = crate::leanh::lean_box(0);
                    v_isShared_6306_ = v_isSharedCheck_6315_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6307_ = lean_nat_add(v_startInclusive_6300_, v___x_6303_);
                crate::leanh::lean_dec(v___x_6303_);
                crate::leanh::lean_dec(v_startInclusive_6300_);
                crate::leanh::lean_inc(v_endExclusive_6301_);
                crate::leanh::lean_inc(v___x_6307_);
                crate::leanh::lean_inc_ref(v_str_6299_);
                if v_isShared_6306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6305_, 1, v___x_6307_);
                    v___x_6309_ = v___x_6305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6314_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_str_6299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6314_, 1, v___x_6307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6314_, 2, v_endExclusive_6301_);
                    v___x_6309_ = v_reuseFailAlloc_6314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6310_ = lean_nat_sub(v_endExclusive_6301_, v___x_6307_);
                crate::leanh::lean_dec(v_endExclusive_6301_);
                v___x_6311_ =
                    l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(
                        v___x_6309_,
                        v___x_6310_,
                    );
                crate::leanh::lean_dec_ref(v___x_6309_);
                v___x_6312_ = lean_nat_add(v___x_6307_, v___x_6311_);
                crate::leanh::lean_dec(v___x_6311_);
                v___x_6313_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6313_, 0, v_str_6299_);
                crate::leanh::lean_ctor_set(v___x_6313_, 1, v___x_6307_);
                crate::leanh::lean_ctor_set(v___x_6313_, 2, v___x_6312_);
                return v___x_6313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(
    mut v_s1_6319_: *mut crate::leanh::LeanObject,
    mut v_s1Curr_6320_: *mut crate::leanh::LeanObject,
    mut v_s2_6321_: *mut crate::leanh::LeanObject,
    mut v_s2Curr_6322_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_6324_: u8 = 0;
    let mut v___y_6325_: u8 = 0;
    let mut v___x_6326_: u8 = 0;
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6332_: u8 = 0;
    let mut v___y_6333_: u8 = 0;
    let mut v___y_6334_: u8 = 0;
    let mut v___x_6335_: u8 = 0;
    let mut v___x_6336_: u8 = 0;
    let mut v_str_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: u8 = 0;
    let mut v_startInclusive_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6347_: u8 = 0;
    let mut v_str_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6352_: u8 = 0;
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: u8 = 0;
    let mut v___x_6355_: u8 = 0;
    let mut v___x_6356_: u8 = 0;
    let mut v___x_6357_: u8 = 0;
    let mut v___x_6358_: u8 = 0;
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: u8 = 0;
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: u8 = 0;
    let mut v___y_6364_: u8 = 0;
    let mut v___x_6365_: u8 = 0;
    let mut v___x_6366_: u8 = 0;
    let mut v___x_6367_: u8 = 0;
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: u8 = 0;
    let mut v___x_6370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6337_ = crate::leanh::lean_ctor_get(v_s1_6319_, 0);
                v_startInclusive_6338_ = crate::leanh::lean_ctor_get(v_s1_6319_, 1);
                v_endExclusive_6339_ = crate::leanh::lean_ctor_get(v_s1_6319_, 2);
                v___x_6340_ = lean_nat_sub(v_endExclusive_6339_, v_startInclusive_6338_);
                v___x_6347_ = lean_nat_dec_lt(v_s1Curr_6320_, v___x_6340_);
                if v___x_6347_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v_str_6348_ = crate::leanh::lean_ctor_get(v_s2_6321_, 0);
                    v_startInclusive_6349_ = crate::leanh::lean_ctor_get(v_s2_6321_, 1);
                    v_endExclusive_6350_ = crate::leanh::lean_ctor_get(v_s2_6321_, 2);
                    v___x_6359_ = lean_nat_sub(v_endExclusive_6350_, v_startInclusive_6349_);
                    v___x_6360_ = lean_nat_dec_lt(v_s2Curr_6322_, v___x_6359_);
                    crate::leanh::lean_dec(v___x_6359_);
                    if v___x_6360_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6340_);
                        v___x_6361_ = lean_nat_add(v_startInclusive_6338_, v_s1Curr_6320_);
                        v___x_6362_ = lean_string_get_byte_fast(v_str_6337_, v___x_6361_);
                        v___x_6367_ = 65;
                        v___x_6368_ = lean_uint8_dec_le(v___x_6367_, v___x_6362_);
                        if v___x_6368_ == 0 {
                            v___y_6364_ = v___x_6368_;
                            state = 5;
                            continue;
                        } else {
                            v___x_6369_ = 90;
                            v___x_6370_ = lean_uint8_dec_le(v___x_6362_, v___x_6369_);
                            v___y_6364_ = v___x_6370_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6326_ = lean_uint8_dec_eq(v___y_6324_, v___y_6325_);
                if v___x_6326_ == 0 {
                    crate::leanh::lean_dec(v_s2Curr_6322_);
                    crate::leanh::lean_dec(v_s1Curr_6320_);
                    return v___x_6326_;
                } else {
                    v___x_6327_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6328_ = lean_nat_add(v_s1Curr_6320_, v___x_6327_);
                    crate::leanh::lean_dec(v_s1Curr_6320_);
                    v___x_6329_ = lean_nat_add(v_s2Curr_6322_, v___x_6327_);
                    crate::leanh::lean_dec(v_s2Curr_6322_);
                    v_s1Curr_6320_ = v___x_6328_;
                    v_s2Curr_6322_ = v___x_6329_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_6334_ == 0 {
                    v___y_6324_ = v___y_6332_;
                    v___y_6325_ = v___y_6333_;
                    state = 1;
                    continue;
                } else {
                    v___x_6335_ = 32;
                    v___x_6336_ = lean_uint8_add(v___y_6333_, v___x_6335_);
                    v___y_6324_ = v___y_6332_;
                    v___y_6325_ = v___x_6336_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6342_ = lean_nat_dec_eq(v_s1Curr_6320_, v___x_6340_);
                crate::leanh::lean_dec(v___x_6340_);
                crate::leanh::lean_dec(v_s1Curr_6320_);
                if v___x_6342_ == 0 {
                    crate::leanh::lean_dec(v_s2Curr_6322_);
                    return v___x_6342_;
                } else {
                    v_startInclusive_6343_ = crate::leanh::lean_ctor_get(v_s2_6321_, 1);
                    v_endExclusive_6344_ = crate::leanh::lean_ctor_get(v_s2_6321_, 2);
                    v___x_6345_ = lean_nat_sub(v_endExclusive_6344_, v_startInclusive_6343_);
                    v___x_6346_ = lean_nat_dec_eq(v_s2Curr_6322_, v___x_6345_);
                    crate::leanh::lean_dec(v___x_6345_);
                    crate::leanh::lean_dec(v_s2Curr_6322_);
                    return v___x_6346_;
                }
            }
            4 => {
                v___x_6353_ = lean_nat_add(v_startInclusive_6349_, v_s2Curr_6322_);
                v___x_6354_ = lean_string_get_byte_fast(v_str_6348_, v___x_6353_);
                v___x_6355_ = 65;
                v___x_6356_ = lean_uint8_dec_le(v___x_6355_, v___x_6354_);
                if v___x_6356_ == 0 {
                    v___y_6332_ = v___y_6352_;
                    v___y_6333_ = v___x_6354_;
                    v___y_6334_ = v___x_6356_;
                    state = 2;
                    continue;
                } else {
                    v___x_6357_ = 90;
                    v___x_6358_ = lean_uint8_dec_le(v___x_6354_, v___x_6357_);
                    v___y_6332_ = v___y_6352_;
                    v___y_6333_ = v___x_6354_;
                    v___y_6334_ = v___x_6358_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v___y_6364_ == 0 {
                    v___y_6352_ = v___x_6362_;
                    state = 4;
                    continue;
                } else {
                    v___x_6365_ = 32;
                    v___x_6366_ = lean_uint8_add(v___x_6362_, v___x_6365_);
                    v___y_6352_ = v___x_6366_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(
    mut v_s1_6371_: *mut crate::leanh::LeanObject,
    mut v_s1Curr_6372_: *mut crate::leanh::LeanObject,
    mut v_s2_6373_: *mut crate::leanh::LeanObject,
    mut v_s2Curr_6374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6375_: u8 = 0;
    let mut v_r_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6375_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(
        v_s1_6371_,
        v_s1Curr_6372_,
        v_s2_6373_,
        v_s2Curr_6374_,
    );
    crate::leanh::lean_dec_ref(v_s2_6373_);
    crate::leanh::lean_dec_ref(v_s1_6371_);
    v_r_6376_ = crate::leanh::lean_box((v_res_6375_) as usize);
    return v_r_6376_;
}
pub unsafe fn l_String_Slice_eqIgnoreAsciiCase(
    mut v_s1_6377_: *mut crate::leanh::LeanObject,
    mut v_s2_6378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: u8 = 0;
    v_startInclusive_6379_ = crate::leanh::lean_ctor_get(v_s1_6377_, 1);
    v_endExclusive_6380_ = crate::leanh::lean_ctor_get(v_s1_6377_, 2);
    v_startInclusive_6381_ = crate::leanh::lean_ctor_get(v_s2_6378_, 1);
    v_endExclusive_6382_ = crate::leanh::lean_ctor_get(v_s2_6378_, 2);
    v___x_6383_ = lean_nat_sub(v_endExclusive_6380_, v_startInclusive_6379_);
    v___x_6384_ = lean_nat_sub(v_endExclusive_6382_, v_startInclusive_6381_);
    v___x_6385_ = lean_nat_dec_eq(v___x_6383_, v___x_6384_);
    crate::leanh::lean_dec(v___x_6384_);
    crate::leanh::lean_dec(v___x_6383_);
    if v___x_6385_ == 0 {
        return v___x_6385_;
    } else {
        let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6387_: u8 = 0;
        v___x_6386_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_6387_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(
            v_s1_6377_,
            v___x_6386_,
            v_s2_6378_,
            v___x_6386_,
        );
        return v___x_6387_;
    }
}
pub unsafe fn l_String_Slice_eqIgnoreAsciiCase___boxed(
    mut v_s1_6388_: *mut crate::leanh::LeanObject,
    mut v_s2_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6390_: u8 = 0;
    let mut v_r_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_6388_, v_s2_6389_);
    crate::leanh::lean_dec_ref(v_s2_6389_);
    crate::leanh::lean_dec_ref(v_s1_6388_);
    v_r_6391_ = crate::leanh::lean_box((v_res_6390_) as usize);
    return v_r_6391_;
}
pub unsafe fn l_String_Slice_lines_lineMap(
    mut v_s_6392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: u8 = 0;
    let mut v___x_6399_: u32 = 0;
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: u32 = 0;
    let mut v___x_6405_: u8 = 0;
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6408_: u8 = 0;
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: u8 = 0;
    let mut v___x_6413_: u32 = 0;
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: u32 = 0;
    let mut v___x_6418_: u8 = 0;
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6421_: u8 = 0;
    let mut v_unused_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6393_ = crate::leanh::lean_ctor_get(v_s_6392_, 0);
                v_startInclusive_6394_ = crate::leanh::lean_ctor_get(v_s_6392_, 1);
                v_endExclusive_6395_ = crate::leanh::lean_ctor_get(v_s_6392_, 2);
                v___x_6396_ = lean_nat_sub(v_endExclusive_6395_, v_startInclusive_6394_);
                v___x_6397_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6398_ = lean_nat_dec_eq(v___x_6396_, v___x_6397_);
                if v___x_6398_ == 0 {
                    v___x_6399_ = 10;
                    v___x_6400_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6401_ = lean_nat_sub(v___x_6396_, v___x_6400_);
                    crate::leanh::lean_dec(v___x_6396_);
                    v___x_6402_ = l_String_Slice_posLE(v_s_6392_, v___x_6401_);
                    v___x_6403_ = lean_nat_add(v_startInclusive_6394_, v___x_6402_);
                    crate::leanh::lean_dec(v___x_6402_);
                    v___x_6404_ = lean_string_utf8_get_fast(v_str_6393_, v___x_6403_);
                    v___x_6405_ = lean_uint32_dec_eq(v___x_6404_, v___x_6399_);
                    if v___x_6405_ == 0 {
                        crate::leanh::lean_dec(v___x_6403_);
                        return v_s_6392_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_6394_);
                        crate::leanh::lean_inc_ref(v_str_6393_);
                        v_isSharedCheck_6421_ = (!crate::leanh::lean_is_exclusive(v_s_6392_)) as u8;
                        if v_isSharedCheck_6421_ == 0 {
                            v_unused_6422_ = crate::leanh::lean_ctor_get(v_s_6392_, 2);
                            crate::leanh::lean_dec(v_unused_6422_);
                            v_unused_6423_ = crate::leanh::lean_ctor_get(v_s_6392_, 1);
                            crate::leanh::lean_dec(v_unused_6423_);
                            v_unused_6424_ = crate::leanh::lean_ctor_get(v_s_6392_, 0);
                            crate::leanh::lean_dec(v_unused_6424_);
                            v___x_6407_ = v_s_6392_;
                            v_isShared_6408_ = v_isSharedCheck_6421_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_6392_);
                            v___x_6407_ = crate::leanh::lean_box(0);
                            v_isShared_6408_ = v_isSharedCheck_6421_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6396_);
                    return v_s_6392_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_6403_);
                crate::leanh::lean_inc(v_startInclusive_6394_);
                crate::leanh::lean_inc_ref(v_str_6393_);
                if v_isShared_6408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6407_, 2, v___x_6403_);
                    v___x_6410_ = v___x_6407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6420_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_str_6393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 1, v_startInclusive_6394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 2, v___x_6403_);
                    v___x_6410_ = v_reuseFailAlloc_6420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6411_ = lean_nat_sub(v___x_6403_, v_startInclusive_6394_);
                crate::leanh::lean_dec(v___x_6403_);
                v___x_6412_ = lean_nat_dec_eq(v___x_6411_, v___x_6397_);
                if v___x_6412_ == 0 {
                    v___x_6413_ = 13;
                    v___x_6414_ = lean_nat_sub(v___x_6411_, v___x_6400_);
                    crate::leanh::lean_dec(v___x_6411_);
                    v___x_6415_ = l_String_Slice_posLE(v___x_6410_, v___x_6414_);
                    v___x_6416_ = lean_nat_add(v_startInclusive_6394_, v___x_6415_);
                    crate::leanh::lean_dec(v___x_6415_);
                    v___x_6417_ = lean_string_utf8_get_fast(v_str_6393_, v___x_6416_);
                    v___x_6418_ = lean_uint32_dec_eq(v___x_6417_, v___x_6413_);
                    if v___x_6418_ == 0 {
                        crate::leanh::lean_dec(v___x_6416_);
                        crate::leanh::lean_dec(v_startInclusive_6394_);
                        crate::leanh::lean_dec_ref(v_str_6393_);
                        return v___x_6410_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6410_);
                        v___x_6419_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6419_, 0, v_str_6393_);
                        crate::leanh::lean_ctor_set(v___x_6419_, 1, v_startInclusive_6394_);
                        crate::leanh::lean_ctor_set(v___x_6419_, 2, v___x_6416_);
                        return v___x_6419_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6411_);
                    crate::leanh::lean_dec(v_startInclusive_6394_);
                    crate::leanh::lean_dec_ref(v_str_6393_);
                    return v___x_6410_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(
    mut v_s_6427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0;
    return v___x_6428_;
}
pub unsafe fn l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(
    mut v_s_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_6429_);
    crate::leanh::lean_dec_ref(v_s_6429_);
    return v_res_6430_;
}
pub unsafe fn l_String_Slice_lines(
    mut v_s_6431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6432_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_6431_);
    return v___x_6432_;
}
pub unsafe fn l_String_Slice_lines___boxed(
    mut v_s_6433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6434_ = l_String_Slice_lines(v_s_6433_);
    crate::leanh::lean_dec_ref(v_s_6433_);
    return v_res_6434_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(
    mut v_s_6435_: *mut crate::leanh::LeanObject,
    mut v_a_6436_: *mut crate::leanh::LeanObject,
    mut v_b_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastWasDigit_6442_: u8 = 0;
    let mut v_snd_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6452_: u8 = 0;
    let mut v___x_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: u32 = 0;
    let mut v___x_6464_: u32 = 0;
    let mut v___x_6465_: u8 = 0;
    let mut v___x_6466_: u32 = 0;
    let mut v___x_6467_: u8 = 0;
    let mut v___x_6468_: u32 = 0;
    let mut v___x_6469_: u8 = 0;
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6477_: u8 = 0;
    let mut v_unused_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6438_ = crate::leanh::lean_ctor_get(v_s_6435_, 0);
                v_startInclusive_6439_ = crate::leanh::lean_ctor_get(v_s_6435_, 1);
                v_endExclusive_6440_ = crate::leanh::lean_ctor_get(v_s_6435_, 2);
                v___x_6441_ = lean_nat_sub(v_endExclusive_6440_, v_startInclusive_6439_);
                v_lastWasDigit_6442_ = lean_nat_dec_eq(v_a_6436_, v___x_6441_);
                crate::leanh::lean_dec(v___x_6441_);
                if v_lastWasDigit_6442_ == 0 {
                    v_snd_6443_ = crate::leanh::lean_ctor_get(v_b_6437_, 1);
                    v_isSharedCheck_6477_ = (!crate::leanh::lean_is_exclusive(v_b_6437_)) as u8;
                    if v_isSharedCheck_6477_ == 0 {
                        v_unused_6478_ = crate::leanh::lean_ctor_get(v_b_6437_, 0);
                        crate::leanh::lean_dec(v_unused_6478_);
                        v___x_6445_ = v_b_6437_;
                        v_isShared_6446_ = v_isSharedCheck_6477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6443_);
                        crate::leanh::lean_dec(v_b_6437_);
                        v___x_6445_ = crate::leanh::lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6477_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6436_);
                    return v_b_6437_;
                }
            }
            1 => {
                v___x_6447_ = crate::leanh::lean_box(0);
                v___x_6448_ = lean_nat_add(v_startInclusive_6439_, v_a_6436_);
                crate::leanh::lean_dec(v_a_6436_);
                v___x_6449_ = lean_string_utf8_next_fast(v_str_6438_, v___x_6448_);
                v___x_6450_ = lean_nat_sub(v___x_6449_, v_startInclusive_6439_);
                v___x_6463_ = lean_string_utf8_get_fast(v_str_6438_, v___x_6448_);
                crate::leanh::lean_dec(v___x_6448_);
                v___x_6464_ = 95;
                v___x_6465_ = lean_uint32_dec_eq(v___x_6463_, v___x_6464_);
                if v___x_6465_ == 0 {
                    v___x_6466_ = 48;
                    v___x_6467_ = lean_uint32_dec_le(v___x_6466_, v___x_6463_);
                    if v___x_6467_ == 0 {
                        v___y_6452_ = v___x_6467_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6468_ = 57;
                        v___x_6469_ = lean_uint32_dec_le(v___x_6463_, v___x_6468_);
                        v___y_6452_ = v___x_6469_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6445_);
                    v___x_6470_ = (crate::leanh::lean_unbox(v_snd_6443_) as u8);
                    if v___x_6470_ == 0 {
                        crate::leanh::lean_dec(v___x_6450_);
                        v___x_6471_ = crate::leanh::lean_box((v_lastWasDigit_6442_) as usize);
                        v___x_6472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6472_, 0, v___x_6471_);
                        v___x_6473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6473_, 0, v___x_6472_);
                        crate::leanh::lean_ctor_set(v___x_6473_, 1, v_snd_6443_);
                        return v___x_6473_;
                    } else {
                        crate::leanh::lean_dec(v_snd_6443_);
                        v___x_6474_ = crate::leanh::lean_box((v_lastWasDigit_6442_) as usize);
                        v___x_6475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6475_, 0, v___x_6447_);
                        crate::leanh::lean_ctor_set(v___x_6475_, 1, v___x_6474_);
                        v_a_6436_ = v___x_6450_;
                        v_b_6437_ = v___x_6475_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_6452_ == 0 {
                    crate::leanh::lean_dec(v___x_6450_);
                    v___x_6453_ = crate::leanh::lean_box((v_lastWasDigit_6442_) as usize);
                    v___x_6454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6454_, 0, v___x_6453_);
                    if v_isShared_6446_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6445_, 0, v___x_6454_);
                        v___x_6456_ = v___x_6445_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6457_, 0, v___x_6454_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6457_, 1, v_snd_6443_);
                        v___x_6456_ = v_reuseFailAlloc_6457_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_6443_);
                    v___x_6458_ = crate::leanh::lean_box((v___y_6452_) as usize);
                    if v_isShared_6446_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6445_, 1, v___x_6458_);
                        crate::leanh::lean_ctor_set(v___x_6445_, 0, v___x_6447_);
                        v___x_6460_ = v___x_6445_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6447_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6462_, 1, v___x_6458_);
                        v___x_6460_ = v_reuseFailAlloc_6462_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6456_;
            }
            4 => {
                v_a_6436_ = v___x_6450_;
                v_b_6437_ = v___x_6460_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(
    mut v_s_6479_: *mut crate::leanh::LeanObject,
    mut v_a_6480_: *mut crate::leanh::LeanObject,
    mut v_b_6481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6482_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(
        v_s_6479_, v_a_6480_, v_b_6481_,
    );
    crate::leanh::lean_dec_ref(v_s_6479_);
    return v_res_6482_;
}
pub unsafe fn l_String_Slice_isNat(mut v_s_6487_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6488_ = l_String_Slice_isNat___closed__0;
    v___x_6489_ = l_String_Slice_positions(v_s_6487_);
    v___x_6490_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(
        v_s_6487_,
        v___x_6489_,
        v___x_6488_,
    );
    v_fst_6491_ = crate::leanh::lean_ctor_get(v___x_6490_, 0);
    crate::leanh::lean_inc(v_fst_6491_);
    if crate::leanh::lean_obj_tag(v_fst_6491_) == 0 {
        let mut v_snd_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6493_: u8 = 0;
        v_snd_6492_ = crate::leanh::lean_ctor_get(v___x_6490_, 1);
        crate::leanh::lean_inc(v_snd_6492_);
        crate::leanh::lean_dec_ref(v___x_6490_);
        v___x_6493_ = (crate::leanh::lean_unbox(v_snd_6492_) as u8);
        crate::leanh::lean_dec(v_snd_6492_);
        return v___x_6493_;
    } else {
        let mut v_val_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6495_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_6490_);
        v_val_6494_ = crate::leanh::lean_ctor_get(v_fst_6491_, 0);
        crate::leanh::lean_inc(v_val_6494_);
        crate::leanh::lean_dec_ref_known(v_fst_6491_, 1);
        v___x_6495_ = (crate::leanh::lean_unbox(v_val_6494_) as u8);
        crate::leanh::lean_dec(v_val_6494_);
        return v___x_6495_;
    }
}
pub unsafe fn l_String_Slice_isNat___boxed(
    mut v_s_6496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6497_: u8 = 0;
    let mut v_r_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6497_ = l_String_Slice_isNat(v_s_6496_);
    crate::leanh::lean_dec_ref(v_s_6496_);
    v_r_6498_ = crate::leanh::lean_box((v_res_6497_) as usize);
    return v_r_6498_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(
    mut v_s_6499_: *mut crate::leanh::LeanObject,
    mut v_inst_6500_: *mut crate::leanh::LeanObject,
    mut v_R_6501_: *mut crate::leanh::LeanObject,
    mut v_a_6502_: *mut crate::leanh::LeanObject,
    mut v_b_6503_: *mut crate::leanh::LeanObject,
    mut v_c_6504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6505_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(
        v_s_6499_, v_a_6502_, v_b_6503_,
    );
    return v___x_6505_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(
    mut v_s_6506_: *mut crate::leanh::LeanObject,
    mut v_inst_6507_: *mut crate::leanh::LeanObject,
    mut v_R_6508_: *mut crate::leanh::LeanObject,
    mut v_a_6509_: *mut crate::leanh::LeanObject,
    mut v_b_6510_: *mut crate::leanh::LeanObject,
    mut v_c_6511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6512_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(
        v_s_6506_,
        v_inst_6507_,
        v_R_6508_,
        v_a_6509_,
        v_b_6510_,
        v_c_6511_,
    );
    crate::leanh::lean_dec_ref(v_s_6506_);
    return v_res_6512_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(
    mut v_s_6513_: *mut crate::leanh::LeanObject,
    mut v_a_6514_: *mut crate::leanh::LeanObject,
    mut v_b_6515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: u32 = 0;
    let mut v___x_6525_: u32 = 0;
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6516_ = crate::leanh::lean_ctor_get(v_s_6513_, 0);
                v_startInclusive_6517_ = crate::leanh::lean_ctor_get(v_s_6513_, 1);
                v_endExclusive_6518_ = crate::leanh::lean_ctor_get(v_s_6513_, 2);
                v___x_6519_ = lean_nat_sub(v_endExclusive_6518_, v_startInclusive_6517_);
                v___x_6520_ = lean_nat_dec_eq(v_a_6514_, v___x_6519_);
                crate::leanh::lean_dec(v___x_6519_);
                if v___x_6520_ == 0 {
                    v___x_6521_ = lean_nat_add(v_startInclusive_6517_, v_a_6514_);
                    crate::leanh::lean_dec(v_a_6514_);
                    v___x_6522_ = lean_string_utf8_next_fast(v_str_6516_, v___x_6521_);
                    v___x_6523_ = lean_nat_sub(v___x_6522_, v_startInclusive_6517_);
                    v___x_6524_ = lean_string_utf8_get_fast(v_str_6516_, v___x_6521_);
                    crate::leanh::lean_dec(v___x_6521_);
                    v___x_6525_ = 95;
                    v___x_6526_ = lean_uint32_dec_eq(v___x_6524_, v___x_6525_);
                    if v___x_6526_ == 0 {
                        v___x_6527_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_6528_ = lean_nat_mul(v_b_6515_, v___x_6527_);
                        crate::leanh::lean_dec(v_b_6515_);
                        v___x_6529_ = lean_uint32_to_nat(v___x_6524_);
                        v___x_6530_ = crate::leanh::lean_unsigned_to_nat(48);
                        v___x_6531_ = lean_nat_sub(v___x_6529_, v___x_6530_);
                        crate::leanh::lean_dec(v___x_6529_);
                        v___x_6532_ = lean_nat_add(v___x_6528_, v___x_6531_);
                        crate::leanh::lean_dec(v___x_6531_);
                        crate::leanh::lean_dec(v___x_6528_);
                        v_a_6514_ = v___x_6523_;
                        v_b_6515_ = v___x_6532_;
                        state = 0;
                        continue;
                    } else {
                        v_a_6514_ = v___x_6523_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6514_);
                    return v_b_6515_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(
    mut v_s_6535_: *mut crate::leanh::LeanObject,
    mut v_a_6536_: *mut crate::leanh::LeanObject,
    mut v_b_6537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6538_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(
        v_s_6535_, v_a_6536_, v_b_6537_,
    );
    crate::leanh::lean_dec_ref(v_s_6535_);
    return v_res_6538_;
}
pub unsafe fn l_String_Slice_toNat_x3f(
    mut v_s_6539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6540_: u8 = 0;
    v___x_6540_ = l_String_Slice_isNat(v_s_6539_);
    if v___x_6540_ == 0 {
        let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6541_ = crate::leanh::lean_box(0);
        return v___x_6541_;
    } else {
        let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6542_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_6543_ = l_String_Slice_positions(v_s_6539_);
        v___x_6544_ =
            l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(
                v_s_6539_,
                v___x_6543_,
                v___x_6542_,
            );
        v___x_6545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6545_, 0, v___x_6544_);
        return v___x_6545_;
    }
}
pub unsafe fn l_String_Slice_toNat_x3f___boxed(
    mut v_s_6546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6547_ = l_String_Slice_toNat_x3f(v_s_6546_);
    crate::leanh::lean_dec_ref(v_s_6546_);
    return v_res_6547_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(
    mut v_s_6548_: *mut crate::leanh::LeanObject,
    mut v_inst_6549_: *mut crate::leanh::LeanObject,
    mut v_R_6550_: *mut crate::leanh::LeanObject,
    mut v_a_6551_: *mut crate::leanh::LeanObject,
    mut v_b_6552_: *mut crate::leanh::LeanObject,
    mut v_c_6553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6554_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(
        v_s_6548_, v_a_6551_, v_b_6552_,
    );
    return v___x_6554_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(
    mut v_s_6555_: *mut crate::leanh::LeanObject,
    mut v_inst_6556_: *mut crate::leanh::LeanObject,
    mut v_R_6557_: *mut crate::leanh::LeanObject,
    mut v_a_6558_: *mut crate::leanh::LeanObject,
    mut v_b_6559_: *mut crate::leanh::LeanObject,
    mut v_c_6560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6561_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(
        v_s_6555_,
        v_inst_6556_,
        v_R_6557_,
        v_a_6558_,
        v_b_6559_,
        v_c_6560_,
    );
    crate::leanh::lean_dec_ref(v_s_6555_);
    return v_res_6561_;
}
pub unsafe fn l_panic___at___00String_Slice_toNat_x21_spec__0(
    mut v_msg_6562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6563_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6564_ = lean_panic_fn_borrowed(v___x_6563_, v_msg_6562_);
    return v___x_6564_;
}
pub unsafe fn _init_l_String_Slice_toNat_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6568_ = l_String_Slice_toNat_x21___closed__2;
    v___x_6569_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_6570_ = crate::leanh::lean_unsigned_to_nat(1040);
    v___x_6571_ = l_String_Slice_toNat_x21___closed__1;
    v___x_6572_ = l_String_Slice_toNat_x21___closed__0;
    v___x_6573_ = l_mkPanicMessageWithDecl(
        v___x_6572_,
        v___x_6571_,
        v___x_6570_,
        v___x_6569_,
        v___x_6568_,
    );
    return v___x_6573_;
}
pub unsafe fn l_String_Slice_toNat_x21(
    mut v_s_6574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6575_: u8 = 0;
    v___x_6575_ = l_String_Slice_isNat(v_s_6574_);
    if v___x_6575_ == 0 {
        let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6576_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_toNat_x21___closed__3),
            core::ptr::addr_of_mut!(l_String_Slice_toNat_x21___closed__3_once),
            _init_l_String_Slice_toNat_x21___closed__3,
        );
        v___x_6577_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_6576_);
        return v___x_6577_;
    } else {
        let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6578_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_6579_ = l_String_Slice_positions(v_s_6574_);
        v___x_6580_ =
            l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(
                v_s_6574_,
                v___x_6579_,
                v___x_6578_,
            );
        return v___x_6580_;
    }
}
pub unsafe fn l_String_Slice_toNat_x21___boxed(
    mut v_s_6581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6582_ = l_String_Slice_toNat_x21(v_s_6581_);
    crate::leanh::lean_dec_ref(v_s_6581_);
    return v_res_6582_;
}
pub unsafe fn l_String_Slice_front_x3f(
    mut v_s_6583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6584_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6585_ = l_String_Slice_Pos_get_x3f(v_s_6583_, v___x_6584_);
    return v___x_6585_;
}
pub unsafe fn l_String_Slice_front_x3f___boxed(
    mut v_s_6586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6587_ = l_String_Slice_front_x3f(v_s_6586_);
    crate::leanh::lean_dec_ref(v_s_6586_);
    return v_res_6587_;
}
pub unsafe fn l_String_Slice_front(mut v_s_6588_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6589_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6590_ = l_String_Slice_Pos_get_x3f(v_s_6588_, v___x_6589_);
    if crate::leanh::lean_obj_tag(v___x_6590_) == 0 {
        let mut v___x_6591_: u32 = 0;
        v___x_6591_ = 65;
        return v___x_6591_;
    } else {
        let mut v_val_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6593_: u32 = 0;
        v_val_6592_ = crate::leanh::lean_ctor_get(v___x_6590_, 0);
        crate::leanh::lean_inc(v_val_6592_);
        crate::leanh::lean_dec_ref_known(v___x_6590_, 1);
        v___x_6593_ = crate::leanh::lean_unbox_uint32(v_val_6592_);
        crate::leanh::lean_dec(v_val_6592_);
        return v___x_6593_;
    }
}
pub unsafe fn l_String_Slice_front___boxed(
    mut v_s_6594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6595_: u32 = 0;
    let mut v_r_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6595_ = l_String_Slice_front(v_s_6594_);
    crate::leanh::lean_dec_ref(v_s_6594_);
    v_r_6596_ = crate::leanh::lean_box_uint32(v_res_6595_);
    return v_r_6596_;
}
pub unsafe fn l_String_Slice_isInt(mut v_s_6597_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_str_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: u8 = 0;
    let mut v___x_6604_: u32 = 0;
    let mut v___x_6605_: u32 = 0;
    let mut v___x_6606_: u8 = 0;
    let mut v___x_6607_: u8 = 0;
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6610_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: u8 = 0;
    let mut v_reuseFailAlloc_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6618_: u8 = 0;
    let mut v_unused_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6598_ = crate::leanh::lean_ctor_get(v_s_6597_, 0);
                v_startInclusive_6599_ = crate::leanh::lean_ctor_get(v_s_6597_, 1);
                v_endExclusive_6600_ = crate::leanh::lean_ctor_get(v_s_6597_, 2);
                v___x_6601_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6602_ = lean_nat_sub(v_endExclusive_6600_, v_startInclusive_6599_);
                v___x_6603_ = lean_nat_dec_eq(v___x_6601_, v___x_6602_);
                crate::leanh::lean_dec(v___x_6602_);
                if v___x_6603_ == 0 {
                    v___x_6604_ = 45;
                    v___x_6605_ = lean_string_utf8_get_fast(v_str_6598_, v_startInclusive_6599_);
                    v___x_6606_ = lean_uint32_dec_eq(v___x_6605_, v___x_6604_);
                    if v___x_6606_ == 0 {
                        v___x_6607_ = l_String_Slice_isNat(v_s_6597_);
                        crate::leanh::lean_dec_ref(v_s_6597_);
                        return v___x_6607_;
                    } else {
                        crate::leanh::lean_inc(v_endExclusive_6600_);
                        crate::leanh::lean_inc(v_startInclusive_6599_);
                        crate::leanh::lean_inc_ref(v_str_6598_);
                        v_isSharedCheck_6618_ = (!crate::leanh::lean_is_exclusive(v_s_6597_)) as u8;
                        if v_isSharedCheck_6618_ == 0 {
                            v_unused_6619_ = crate::leanh::lean_ctor_get(v_s_6597_, 2);
                            crate::leanh::lean_dec(v_unused_6619_);
                            v_unused_6620_ = crate::leanh::lean_ctor_get(v_s_6597_, 1);
                            crate::leanh::lean_dec(v_unused_6620_);
                            v_unused_6621_ = crate::leanh::lean_ctor_get(v_s_6597_, 0);
                            crate::leanh::lean_dec(v_unused_6621_);
                            v___x_6609_ = v_s_6597_;
                            v_isShared_6610_ = v_isSharedCheck_6618_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_6597_);
                            v___x_6609_ = crate::leanh::lean_box(0);
                            v_isShared_6610_ = v_isSharedCheck_6618_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_6622_ = l_String_Slice_isNat(v_s_6597_);
                    crate::leanh::lean_dec_ref(v_s_6597_);
                    return v___x_6622_;
                }
            }
            1 => {
                v___x_6611_ = lean_string_utf8_next_fast(v_str_6598_, v_startInclusive_6599_);
                v___x_6612_ = lean_nat_sub(v___x_6611_, v_startInclusive_6599_);
                v___x_6613_ = lean_nat_add(v_startInclusive_6599_, v___x_6612_);
                crate::leanh::lean_dec(v___x_6612_);
                crate::leanh::lean_dec(v_startInclusive_6599_);
                if v_isShared_6610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6609_, 1, v___x_6613_);
                    v___x_6615_ = v___x_6609_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6617_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 0, v_str_6598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 1, v___x_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6617_, 2, v_endExclusive_6600_);
                    v___x_6615_ = v_reuseFailAlloc_6617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6616_ = l_String_Slice_isNat(v___x_6615_);
                crate::leanh::lean_dec_ref(v___x_6615_);
                return v___x_6616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_isInt___boxed(
    mut v_s_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6624_: u8 = 0;
    let mut v_r_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6624_ = l_String_Slice_isInt(v_s_6623_);
    v_r_6625_ = crate::leanh::lean_box((v_res_6624_) as usize);
    return v_r_6625_;
}
pub unsafe fn l_String_Slice_toInt_x3f(
    mut v_s_6626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6638_: u8 = 0;
    let mut v_str_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: u8 = 0;
    let mut v___x_6645_: u32 = 0;
    let mut v___x_6646_: u32 = 0;
    let mut v___x_6647_: u8 = 0;
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6650_: u8 = 0;
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6661_: u8 = 0;
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6666_: u8 = 0;
    let mut v_reuseFailAlloc_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6668_: u8 = 0;
    let mut v_unused_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6639_ = crate::leanh::lean_ctor_get(v_s_6626_, 0);
                v_startInclusive_6640_ = crate::leanh::lean_ctor_get(v_s_6626_, 1);
                v_endExclusive_6641_ = crate::leanh::lean_ctor_get(v_s_6626_, 2);
                v___x_6642_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6643_ = lean_nat_sub(v_endExclusive_6641_, v_startInclusive_6640_);
                v___x_6644_ = lean_nat_dec_eq(v___x_6642_, v___x_6643_);
                crate::leanh::lean_dec(v___x_6643_);
                if v___x_6644_ == 0 {
                    v___x_6645_ = 45;
                    v___x_6646_ = lean_string_utf8_get_fast(v_str_6639_, v_startInclusive_6640_);
                    v___x_6647_ = lean_uint32_dec_eq(v___x_6646_, v___x_6645_);
                    if v___x_6647_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endExclusive_6641_);
                        crate::leanh::lean_inc(v_startInclusive_6640_);
                        crate::leanh::lean_inc_ref(v_str_6639_);
                        v_isSharedCheck_6668_ = (!crate::leanh::lean_is_exclusive(v_s_6626_)) as u8;
                        if v_isSharedCheck_6668_ == 0 {
                            v_unused_6669_ = crate::leanh::lean_ctor_get(v_s_6626_, 2);
                            crate::leanh::lean_dec(v_unused_6669_);
                            v_unused_6670_ = crate::leanh::lean_ctor_get(v_s_6626_, 1);
                            crate::leanh::lean_dec(v_unused_6670_);
                            v_unused_6671_ = crate::leanh::lean_ctor_get(v_s_6626_, 0);
                            crate::leanh::lean_dec(v_unused_6671_);
                            v___x_6649_ = v_s_6626_;
                            v_isShared_6650_ = v_isSharedCheck_6668_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_6626_);
                            v___x_6649_ = crate::leanh::lean_box(0);
                            v_isShared_6650_ = v_isSharedCheck_6668_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6628_ = l_String_Slice_toNat_x3f(v_s_6626_);
                crate::leanh::lean_dec_ref(v_s_6626_);
                if crate::leanh::lean_obj_tag(v___x_6628_) == 0 {
                    v___x_6629_ = crate::leanh::lean_box(0);
                    return v___x_6629_;
                } else {
                    v_val_6630_ = crate::leanh::lean_ctor_get(v___x_6628_, 0);
                    v_isSharedCheck_6638_ = (!crate::leanh::lean_is_exclusive(v___x_6628_)) as u8;
                    if v_isSharedCheck_6638_ == 0 {
                        v___x_6632_ = v___x_6628_;
                        v_isShared_6633_ = v_isSharedCheck_6638_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6630_);
                        crate::leanh::lean_dec(v___x_6628_);
                        v___x_6632_ = crate::leanh::lean_box(0);
                        v_isShared_6633_ = v_isSharedCheck_6638_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6634_ = lean_nat_to_int(v_val_6630_);
                if v_isShared_6633_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6632_, 0, v___x_6634_);
                    v___x_6636_ = v___x_6632_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6637_, 0, v___x_6634_);
                    v___x_6636_ = v_reuseFailAlloc_6637_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6636_;
            }
            4 => {
                v___x_6651_ = lean_string_utf8_next_fast(v_str_6639_, v_startInclusive_6640_);
                v___x_6652_ = lean_nat_sub(v___x_6651_, v_startInclusive_6640_);
                v___x_6653_ = lean_nat_add(v_startInclusive_6640_, v___x_6652_);
                crate::leanh::lean_dec(v___x_6652_);
                crate::leanh::lean_dec(v_startInclusive_6640_);
                if v_isShared_6650_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6649_, 1, v___x_6653_);
                    v___x_6655_ = v___x_6649_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6667_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6667_, 0, v_str_6639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6667_, 1, v___x_6653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6667_, 2, v_endExclusive_6641_);
                    v___x_6655_ = v_reuseFailAlloc_6667_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6656_ = l_String_Slice_toNat_x3f(v___x_6655_);
                crate::leanh::lean_dec_ref(v___x_6655_);
                if crate::leanh::lean_obj_tag(v___x_6656_) == 0 {
                    v___x_6657_ = crate::leanh::lean_box(0);
                    return v___x_6657_;
                } else {
                    v_val_6658_ = crate::leanh::lean_ctor_get(v___x_6656_, 0);
                    v_isSharedCheck_6666_ = (!crate::leanh::lean_is_exclusive(v___x_6656_)) as u8;
                    if v_isSharedCheck_6666_ == 0 {
                        v___x_6660_ = v___x_6656_;
                        v_isShared_6661_ = v_isSharedCheck_6666_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6658_);
                        crate::leanh::lean_dec(v___x_6656_);
                        v___x_6660_ = crate::leanh::lean_box(0);
                        v_isShared_6661_ = v_isSharedCheck_6666_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6662_ = l_Int_negOfNat(v_val_6658_);
                crate::leanh::lean_dec(v_val_6658_);
                if v_isShared_6661_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6660_, 0, v___x_6662_);
                    v___x_6664_ = v___x_6660_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 0, v___x_6662_);
                    v___x_6664_ = v_reuseFailAlloc_6665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_toInt_x21(
    mut v_s_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6674_ = l_String_Slice_toInt_x3f(v_s_6673_);
    if crate::leanh::lean_obj_tag(v___x_6674_) == 0 {
        let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6675_ = l_Int_instInhabited;
        v___x_6676_ = l_String_Slice_toInt_x21___closed__0;
        v___x_6677_ = l_panic___redArg(v___x_6675_, v___x_6676_);
        return v___x_6677_;
    } else {
        let mut v_val_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6678_ = crate::leanh::lean_ctor_get(v___x_6674_, 0);
        crate::leanh::lean_inc(v_val_6678_);
        crate::leanh::lean_dec_ref_known(v___x_6674_, 1);
        return v_val_6678_;
    }
}
pub unsafe fn l_String_Slice_back_x3f(
    mut v_s_6679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_6680_ = crate::leanh::lean_ctor_get(v_s_6679_, 1);
    v_endExclusive_6681_ = crate::leanh::lean_ctor_get(v_s_6679_, 2);
    v___x_6682_ = lean_nat_sub(v_endExclusive_6681_, v_startInclusive_6680_);
    v___x_6683_ = l_String_Slice_Pos_prev_x3f(v_s_6679_, v___x_6682_);
    crate::leanh::lean_dec(v___x_6682_);
    if crate::leanh::lean_obj_tag(v___x_6683_) == 0 {
        let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6684_ = crate::leanh::lean_box(0);
        return v___x_6684_;
    } else {
        let mut v_val_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6685_ = crate::leanh::lean_ctor_get(v___x_6683_, 0);
        crate::leanh::lean_inc(v_val_6685_);
        crate::leanh::lean_dec_ref_known(v___x_6683_, 1);
        v___x_6686_ = l_String_Slice_Pos_get_x3f(v_s_6679_, v_val_6685_);
        crate::leanh::lean_dec(v_val_6685_);
        return v___x_6686_;
    }
}
pub unsafe fn l_String_Slice_back_x3f___boxed(
    mut v_s_6687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6688_ = l_String_Slice_back_x3f(v_s_6687_);
    crate::leanh::lean_dec_ref(v_s_6687_);
    return v_res_6688_;
}
pub unsafe fn l_String_Slice_back(mut v_s_6689_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_startInclusive_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_6690_ = crate::leanh::lean_ctor_get(v_s_6689_, 1);
    v_endExclusive_6691_ = crate::leanh::lean_ctor_get(v_s_6689_, 2);
    v___x_6692_ = lean_nat_sub(v_endExclusive_6691_, v_startInclusive_6690_);
    v___x_6693_ = l_String_Slice_Pos_prev_x3f(v_s_6689_, v___x_6692_);
    crate::leanh::lean_dec(v___x_6692_);
    if crate::leanh::lean_obj_tag(v___x_6693_) == 0 {
        let mut v___x_6694_: u32 = 0;
        v___x_6694_ = 65;
        return v___x_6694_;
    } else {
        let mut v_val_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6695_ = crate::leanh::lean_ctor_get(v___x_6693_, 0);
        crate::leanh::lean_inc(v_val_6695_);
        crate::leanh::lean_dec_ref_known(v___x_6693_, 1);
        v___x_6696_ = l_String_Slice_Pos_get_x3f(v_s_6689_, v_val_6695_);
        crate::leanh::lean_dec(v_val_6695_);
        if crate::leanh::lean_obj_tag(v___x_6696_) == 0 {
            let mut v___x_6697_: u32 = 0;
            v___x_6697_ = 65;
            return v___x_6697_;
        } else {
            let mut v_val_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6699_: u32 = 0;
            v_val_6698_ = crate::leanh::lean_ctor_get(v___x_6696_, 0);
            crate::leanh::lean_inc(v_val_6698_);
            crate::leanh::lean_dec_ref_known(v___x_6696_, 1);
            v___x_6699_ = crate::leanh::lean_unbox_uint32(v_val_6698_);
            crate::leanh::lean_dec(v_val_6698_);
            return v___x_6699_;
        }
    }
}
pub unsafe fn l_String_Slice_back___boxed(
    mut v_s_6700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6701_: u32 = 0;
    let mut v_r_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6701_ = l_String_Slice_back(v_s_6700_);
    crate::leanh::lean_dec_ref(v_s_6700_);
    v_r_6702_ = crate::leanh::lean_box_uint32(v_res_6701_);
    return v_r_6702_;
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(
    mut v_acc_6703_: *mut crate::leanh::LeanObject,
    mut v_s_6704_: *mut crate::leanh::LeanObject,
    mut v_a_6705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6705_) == 0 {
                    return v_acc_6703_;
                } else {
                    v_head_6706_ = crate::leanh::lean_ctor_get(v_a_6705_, 0);
                    v_tail_6707_ = crate::leanh::lean_ctor_get(v_a_6705_, 1);
                    v_str_6708_ = crate::leanh::lean_ctor_get(v_s_6704_, 0);
                    v_startInclusive_6709_ = crate::leanh::lean_ctor_get(v_s_6704_, 1);
                    v_endExclusive_6710_ = crate::leanh::lean_ctor_get(v_s_6704_, 2);
                    v_str_6711_ = crate::leanh::lean_ctor_get(v_head_6706_, 0);
                    v_startInclusive_6712_ = crate::leanh::lean_ctor_get(v_head_6706_, 1);
                    v_endExclusive_6713_ = crate::leanh::lean_ctor_get(v_head_6706_, 2);
                    v___x_6714_ = lean_string_utf8_extract(
                        v_str_6708_,
                        v_startInclusive_6709_,
                        v_endExclusive_6710_,
                    );
                    v___x_6715_ = lean_string_append(v_acc_6703_, v___x_6714_);
                    crate::leanh::lean_dec_ref(v___x_6714_);
                    v___x_6716_ = lean_string_utf8_extract(
                        v_str_6711_,
                        v_startInclusive_6712_,
                        v_endExclusive_6713_,
                    );
                    v___x_6717_ = lean_string_append(v___x_6715_, v___x_6716_);
                    crate::leanh::lean_dec_ref(v___x_6716_);
                    v_acc_6703_ = v___x_6717_;
                    v_a_6705_ = v_tail_6707_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(
    mut v_acc_6719_: *mut crate::leanh::LeanObject,
    mut v_s_6720_: *mut crate::leanh::LeanObject,
    mut v_a_6721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6722_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(
        v_acc_6719_,
        v_s_6720_,
        v_a_6721_,
    );
    crate::leanh::lean_dec(v_a_6721_);
    crate::leanh::lean_dec_ref(v_s_6720_);
    return v_res_6722_;
}
pub unsafe fn l_String_Slice_intercalate(
    mut v_s_6723_: *mut crate::leanh::LeanObject,
    mut v_x_6724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6724_) == 0 {
        let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6725_ = l_String_Slice_replace___redArg___closed__1;
        return v___x_6725_;
    } else {
        let mut v_head_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_6726_ = crate::leanh::lean_ctor_get(v_x_6724_, 0);
        v_tail_6727_ = crate::leanh::lean_ctor_get(v_x_6724_, 1);
        v_str_6728_ = crate::leanh::lean_ctor_get(v_head_6726_, 0);
        v_startInclusive_6729_ = crate::leanh::lean_ctor_get(v_head_6726_, 1);
        v_endExclusive_6730_ = crate::leanh::lean_ctor_get(v_head_6726_, 2);
        v___x_6731_ =
            lean_string_utf8_extract(v_str_6728_, v_startInclusive_6729_, v_endExclusive_6730_);
        v___x_6732_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(
            v___x_6731_,
            v_s_6723_,
            v_tail_6727_,
        );
        return v___x_6732_;
    }
}
pub unsafe fn l_String_Slice_intercalate___boxed(
    mut v_s_6733_: *mut crate::leanh::LeanObject,
    mut v_x_6734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6735_ = l_String_Slice_intercalate(v_s_6733_, v_x_6734_);
    crate::leanh::lean_dec(v_x_6734_);
    crate::leanh::lean_dec_ref(v_s_6733_);
    return v_res_6735_;
}
pub unsafe fn l_List_foldl___at___00String_Slice_join_spec__0(
    mut v_x_6736_: *mut crate::leanh::LeanObject,
    mut v_x_6737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6737_) == 0 {
                    return v_x_6736_;
                } else {
                    v_head_6738_ = crate::leanh::lean_ctor_get(v_x_6737_, 0);
                    v_tail_6739_ = crate::leanh::lean_ctor_get(v_x_6737_, 1);
                    v_str_6740_ = crate::leanh::lean_ctor_get(v_head_6738_, 0);
                    v_startInclusive_6741_ = crate::leanh::lean_ctor_get(v_head_6738_, 1);
                    v_endExclusive_6742_ = crate::leanh::lean_ctor_get(v_head_6738_, 2);
                    v___x_6743_ = lean_string_utf8_extract(
                        v_str_6740_,
                        v_startInclusive_6741_,
                        v_endExclusive_6742_,
                    );
                    v___x_6744_ = lean_string_append(v_x_6736_, v___x_6743_);
                    crate::leanh::lean_dec_ref(v___x_6743_);
                    v_x_6736_ = v___x_6744_;
                    v_x_6737_ = v_tail_6739_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00String_Slice_join_spec__0___boxed(
    mut v_x_6746_: *mut crate::leanh::LeanObject,
    mut v_x_6747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6748_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_6746_, v_x_6747_);
    crate::leanh::lean_dec(v_x_6747_);
    return v_res_6748_;
}
pub unsafe fn l_String_Slice_join(
    mut v_l_6749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6750_ = l_String_Slice_replace___redArg___closed__1;
    v___x_6751_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_6750_, v_l_6749_);
    return v___x_6751_;
}
pub unsafe fn l_String_Slice_join___boxed(
    mut v_l_6752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6753_ = l_String_Slice_join(v_l_6752_);
    crate::leanh::lean_dec(v_l_6752_);
    return v_res_6753_;
}
pub unsafe fn l_String_Slice_toName(
    mut v_s_6754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6755_ = l_String_Slice_toString(v_s_6754_);
    v___x_6756_ = l_String_toName(v___x_6755_);
    return v___x_6756_;
}
pub unsafe fn l_String_Slice_toName___boxed(
    mut v_s_6757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6758_ = l_String_Slice_toName(v_s_6757_);
    crate::leanh::lean_dec_ref(v_s_6757_);
    return v_res_6758_;
}
pub unsafe fn l_String_Slice_instToFormat___lam__0(
    mut v_s_6759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_6760_ = crate::leanh::lean_ctor_get(v_s_6759_, 0);
    v_startInclusive_6761_ = crate::leanh::lean_ctor_get(v_s_6759_, 1);
    v_endExclusive_6762_ = crate::leanh::lean_ctor_get(v_s_6759_, 2);
    v___x_6763_ =
        lean_string_utf8_extract(v_str_6760_, v_startInclusive_6761_, v_endExclusive_6762_);
    v___x_6764_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6764_, 0, v___x_6763_);
    return v___x_6764_;
}
pub unsafe fn l_String_Slice_instToFormat___lam__0___boxed(
    mut v_s_6765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6766_ = l_String_Slice_instToFormat___lam__0(v_s_6765_);
    crate::leanh::lean_dec_ref(v_s_6765_);
    return v_res_6766_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Slice(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_ToSlice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Subslice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_String_Slice_instLT = _init_l_String_Slice_instLT();
    crate::leanh::lean_mark_persistent(l_String_Slice_instLT);
    l_String_Slice_instLE = _init_l_String_Slice_instLE();
    crate::leanh::lean_mark_persistent(l_String_Slice_instLE);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Slice(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Slice(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_ToSlice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Subslice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Slice(builtin);
}
