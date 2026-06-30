// Lean compiler output
// Module: Lean.Compiler.LCNF.PassManager
// Imports: Lean.Compiler.LCNF.CompilerM Init.Data.Fin.Lemmas Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_st_ref_get, lean_string_append,
    lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop,
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_mkAtom, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_instDecidableEqPurity;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_Phase_toPurity,
    l_Lean_Compiler_LCNF_instDecidableEqPhase, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instInhabitedCoreM___lam__0___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::l_Lean_Environment_evalConstCheck___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
pub static l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0_value:
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
    m_data: [98, 97, 115, 101, 0],
};
static mut l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1_value:
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
    m_data: [109, 111, 110, 111, 0],
};
static mut l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2_value:
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
    m_data: [105, 109, 112, 117, 114, 101, 0],
};
static mut l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instToStringPhase___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instToStringPhase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80,
        97, 115, 115, 77, 97, 110, 97, 103, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80,
        104, 97, 115, 101, 46, 119, 105, 116, 104, 80, 117, 114, 105, 116, 121, 67, 104, 101, 99,
        107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        44, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 32, 98, 117, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        67, 111, 109, 112, 105, 108, 101, 114, 32, 101, 114, 114, 111, 114, 58, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32,
        116, 111, 32, 73, 82, 32, 112, 104, 97, 115, 101, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5_value:
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
    m_data: [112, 117, 114, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instLTPhase: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instLEPhase: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value)
            as *mut leanh::LeanObject,
        12783917532758215986 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value)
            as *mut leanh::LeanObject,
        10138443044734372301 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value)
            as *mut leanh::LeanObject,
        9555431800314169832 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20_value:
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
    m_data: [43, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value:
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
    m_data: [97, 114, 105, 116, 104, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value)
            as *mut leanh::LeanObject,
        3738010876686032200 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value:
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
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value)
            as *mut leanh::LeanObject,
        10759351130620427500 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPass___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPass___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPass: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value
        ) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPassInstaller: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPassManager_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPassManager: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 67, 78, 70, 32, 99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [32, 104, 97, 115, 32, 112, 104, 97, 115, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [32, 98, 117, 116, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 121, 32,
        111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0_value: leanh::LeanStringObject<52> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 80, 97, 115, 115, 73, 110, 115, 116, 97, 108, 108, 101, 114, 46, 119, 105, 116, 104, 69, 97, 99, 104, 79, 99, 99, 117, 114, 114, 101, 110, 99, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 104, 97, 115, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        84, 114, 105, 101, 100, 32, 116, 111, 32, 105, 110, 115, 101, 114, 116, 32, 112, 97, 115,
        115, 32, 97, 102, 116, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [44, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2_value:
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
    m_data: [32, 98, 117, 116, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 112, 97, 115, 115,
        32, 108, 105, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        84, 114, 105, 101, 100, 32, 116, 111, 32, 114, 101, 112, 108, 97, 99, 101, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 97, 115, 115, 73, 110, 115, 116, 97, 108, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value) as *mut leanh::LeanObject,15533063730467035502 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toNat(mut v_x_1388_: u8) -> *mut leanh::LeanObject {
    match v_x_1388_ {
        0 => {
            let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1389_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1389_;
        }
        1 => {
            let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1390_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1390_;
        }
        _ => {
            let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1391_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1391_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toNat___boxed(
    mut v_x_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_34__boxed_1393_: u8 = 0;
    let mut v_res_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_34__boxed_1393_ = (leanh::lean_unbox(v_x_1392_) as u8);
    v_res_1394_ = l_Lean_Compiler_LCNF_Phase_toNat(v_x_34__boxed_1393_);
    return v_res_1394_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instToStringPhase___lam__0(
    mut v_x_1398_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1398_ {
        0 => {
            let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1399_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0;
            return v___x_1399_;
        }
        1 => {
            let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1400_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1;
            return v___x_1400_;
        }
        _ => {
            let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1401_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2;
            return v___x_1401_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed(
    mut v_x_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1403_: u8 = 0;
    let mut v_res_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1403_ = (leanh::lean_unbox(v_x_1402_) as u8);
    v_res_1404_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0(v_x_36__boxed_1403_);
    return v_res_1404_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
    mut v_inst_1413_: *mut leanh::LeanObject,
    mut v_pp_1414_: u8,
    mut v_ip_1415_: u8,
    mut v_x_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1417_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_pp_1414_);
                v___x_1418_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v___x_1417_, v_ip_1415_);
                if v___x_1418_ == 0 {
                    leanh::lean_dec(v_x_1416_);
                    v___x_1419_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0;
                    v___x_1420_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1;
                    v___x_1421_ = leanh::lean_unsigned_to_nat(33);
                    v___x_1422_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1431_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3;
                    match v_pp_1414_ {
                        0 => {
                            v___x_1439_ =
                                l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0;
                            v___y_1433_ = v___x_1439_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v___x_1440_ =
                                l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1;
                            v___y_1433_ = v___x_1440_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v___x_1441_ =
                                l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2;
                            v___y_1433_ = v___x_1441_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1442_ = leanh::lean_apply_1(v_x_1416_, leanh::lean_box(0));
                    return v___x_1442_;
                }
            }
            1 => {
                v___x_1426_ = lean_string_append(v___y_1424_, v___y_1425_);
                v___x_1427_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2;
                v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
                v___x_1429_ = l_mkPanicMessageWithDecl(
                    v___x_1419_,
                    v___x_1420_,
                    v___x_1421_,
                    v___x_1422_,
                    v___x_1428_,
                );
                leanh::lean_dec_ref(v___x_1428_);
                v___x_1430_ = l_panic___redArg(v_inst_1413_, v___x_1429_);
                return v___x_1430_;
            }
            2 => {
                v___x_1434_ = lean_string_append(v___x_1431_, v___y_1433_);
                v___x_1435_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4;
                v___x_1436_ = lean_string_append(v___x_1434_, v___x_1435_);
                if v_ip_1415_ == 0 {
                    v___x_1437_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5;
                    v___y_1424_ = v___x_1436_;
                    v___y_1425_ = v___x_1437_;
                    state = 1;
                    continue;
                } else {
                    v___x_1438_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2;
                    v___y_1424_ = v___x_1436_;
                    v___y_1425_ = v___x_1438_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(
    mut v_inst_1443_: *mut leanh::LeanObject,
    mut v_pp_1444_: *mut leanh::LeanObject,
    mut v_ip_1445_: *mut leanh::LeanObject,
    mut v_x_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pp_boxed_1447_: u8 = 0;
    let mut v_ip_boxed_1448_: u8 = 0;
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pp_boxed_1447_ = (leanh::lean_unbox(v_pp_1444_) as u8);
    v_ip_boxed_1448_ = (leanh::lean_unbox(v_ip_1445_) as u8);
    v_res_1449_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v_inst_1443_,
        v_pp_boxed_1447_,
        v_ip_boxed_1448_,
        v_x_1446_,
    );
    leanh::lean_dec(v_inst_1443_);
    return v_res_1449_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_withPurityCheck(
    mut v_00_u03b1_1450_: *mut leanh::LeanObject,
    mut v_inst_1451_: *mut leanh::LeanObject,
    mut v_pp_1452_: u8,
    mut v_ip_1453_: u8,
    mut v_x_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v_inst_1451_,
        v_pp_1452_,
        v_ip_1453_,
        v_x_1454_,
    );
    return v___x_1455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(
    mut v_00_u03b1_1456_: *mut leanh::LeanObject,
    mut v_inst_1457_: *mut leanh::LeanObject,
    mut v_pp_1458_: *mut leanh::LeanObject,
    mut v_ip_1459_: *mut leanh::LeanObject,
    mut v_x_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pp_boxed_1461_: u8 = 0;
    let mut v_ip_boxed_1462_: u8 = 0;
    let mut v_res_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pp_boxed_1461_ = (leanh::lean_unbox(v_pp_1458_) as u8);
    v_ip_boxed_1462_ = (leanh::lean_unbox(v_ip_1459_) as u8);
    v_res_1463_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(
        v_00_u03b1_1456_,
        v_inst_1457_,
        v_pp_boxed_1461_,
        v_ip_boxed_1462_,
        v_x_1460_,
    );
    leanh::lean_dec(v_inst_1457_);
    return v_res_1463_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instLTPhase() -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_box(0);
    return v___x_1464_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instLEPhase() -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = leanh::lean_box(0);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableLtPhase(
    mut v_p1_1466_: u8,
    mut v_p2_1467_: u8,
) -> u8 {
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    v___x_1468_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_1466_);
    v___x_1469_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_1467_);
    v___x_1470_ = lean_nat_dec_lt(v___x_1468_, v___x_1469_);
    leanh::lean_dec(v___x_1469_);
    leanh::lean_dec(v___x_1468_);
    return v___x_1470_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(
    mut v_p1_1471_: *mut leanh::LeanObject,
    mut v_p2_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p1_boxed_1473_: u8 = 0;
    let mut v_p2_boxed_1474_: u8 = 0;
    let mut v_res_1475_: u8 = 0;
    let mut v_r_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p1_boxed_1473_ = (leanh::lean_unbox(v_p1_1471_) as u8);
    v_p2_boxed_1474_ = (leanh::lean_unbox(v_p2_1472_) as u8);
    v_res_1475_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_boxed_1473_, v_p2_boxed_1474_);
    v_r_1476_ = leanh::lean_box((v_res_1475_) as usize);
    return v_r_1476_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableLePhase(
    mut v_p1_1477_: u8,
    mut v_p2_1478_: u8,
) -> u8 {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    v___x_1479_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_1477_);
    v___x_1480_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_1478_);
    v___x_1481_ = lean_nat_dec_le(v___x_1479_, v___x_1480_);
    leanh::lean_dec(v___x_1480_);
    leanh::lean_dec(v___x_1479_);
    return v___x_1481_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(
    mut v_p1_1482_: *mut leanh::LeanObject,
    mut v_p2_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p1_boxed_1484_: u8 = 0;
    let mut v_p2_boxed_1485_: u8 = 0;
    let mut v_res_1486_: u8 = 0;
    let mut v_r_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p1_boxed_1484_ = (leanh::lean_unbox(v_p1_1482_) as u8);
    v_p2_boxed_1485_ = (leanh::lean_unbox(v_p2_1483_) as u8);
    v_res_1486_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_boxed_1484_, v_p2_boxed_1485_);
    v_r_1487_ = leanh::lean_box((v_res_1486_) as usize);
    return v_r_1487_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10;
    v___x_1515_ = l_Lean_mkAtom(v___x_1514_);
    return v___x_1515_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12,
    );
    v___x_1517_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1518_ = lean_array_push(v___x_1517_, v___x_1516_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20;
    v___x_1539_ = l_Lean_mkAtom(v___x_1538_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21,
    );
    v___x_1541_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1542_ = lean_array_push(v___x_1541_, v___x_1540_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23;
    v___x_1545_ = lean_string_utf8_byte_size(v___x_1544_);
    return v___x_1545_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24,
    );
    v___x_1547_ = leanh::lean_unsigned_to_nat(0);
    v___x_1548_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23;
    v___x_1549_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1549_, 0, v___x_1548_);
    leanh::lean_ctor_set(v___x_1549_, 1, v___x_1547_);
    leanh::lean_ctor_set(v___x_1549_, 2, v___x_1546_);
    return v___x_1549_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = leanh::lean_box(0);
    v___x_1553_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26;
    v___x_1554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25,
    );
    v___x_1555_ = leanh::lean_box(2);
    v___x_1556_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1556_, 0, v___x_1555_);
    leanh::lean_ctor_set(v___x_1556_, 1, v___x_1554_);
    leanh::lean_ctor_set(v___x_1556_, 2, v___x_1553_);
    leanh::lean_ctor_set(v___x_1556_, 3, v___x_1552_);
    return v___x_1556_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27,
    );
    v___x_1558_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22,
    );
    v___x_1559_ = lean_array_push(v___x_1558_, v___x_1557_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28,
    );
    v___x_1561_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19;
    v___x_1562_ = leanh::lean_box(2);
    v___x_1563_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1563_, 0, v___x_1562_);
    leanh::lean_ctor_set(v___x_1563_, 1, v___x_1561_);
    leanh::lean_ctor_set(v___x_1563_, 2, v___x_1560_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29,
    );
    v___x_1565_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1566_ = lean_array_push(v___x_1565_, v___x_1564_);
    return v___x_1566_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30,
    );
    v___x_1568_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17;
    v___x_1569_ = leanh::lean_box(2);
    v___x_1570_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
    leanh::lean_ctor_set(v___x_1570_, 1, v___x_1568_);
    leanh::lean_ctor_set(v___x_1570_, 2, v___x_1567_);
    return v___x_1570_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1571_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31,
    );
    v___x_1572_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1573_ = lean_array_push(v___x_1572_, v___x_1571_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33;
    v___x_1576_ = lean_string_utf8_byte_size(v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34,
    );
    v___x_1578_ = leanh::lean_unsigned_to_nat(0);
    v___x_1579_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33;
    v___x_1580_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
    leanh::lean_ctor_set(v___x_1580_, 1, v___x_1578_);
    leanh::lean_ctor_set(v___x_1580_, 2, v___x_1577_);
    return v___x_1580_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = leanh::lean_box(0);
    v___x_1584_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36;
    v___x_1585_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35,
    );
    v___x_1586_ = leanh::lean_box(2);
    v___x_1587_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    leanh::lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    leanh::lean_ctor_set(v___x_1587_, 2, v___x_1584_);
    leanh::lean_ctor_set(v___x_1587_, 3, v___x_1583_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37,
    );
    v___x_1589_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22,
    );
    v___x_1590_ = lean_array_push(v___x_1589_, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38,
    );
    v___x_1592_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19;
    v___x_1593_ = leanh::lean_box(2);
    v___x_1594_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    leanh::lean_ctor_set(v___x_1594_, 1, v___x_1592_);
    leanh::lean_ctor_set(v___x_1594_, 2, v___x_1591_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39,
    );
    v___x_1596_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1597_ = lean_array_push(v___x_1596_, v___x_1595_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40,
    );
    v___x_1599_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17;
    v___x_1600_ = leanh::lean_box(2);
    v___x_1601_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1601_, 0, v___x_1600_);
    leanh::lean_ctor_set(v___x_1601_, 1, v___x_1599_);
    leanh::lean_ctor_set(v___x_1601_, 2, v___x_1598_);
    return v___x_1601_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41,
    );
    v___x_1603_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32,
    );
    v___x_1604_ = lean_array_push(v___x_1603_, v___x_1602_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42,
    );
    v___x_1606_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9;
    v___x_1607_ = leanh::lean_box(2);
    v___x_1608_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1608_, 0, v___x_1607_);
    leanh::lean_ctor_set(v___x_1608_, 1, v___x_1606_);
    leanh::lean_ctor_set(v___x_1608_, 2, v___x_1605_);
    return v___x_1608_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43,
    );
    v___x_1610_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1611_ = lean_array_push(v___x_1610_, v___x_1609_);
    return v___x_1611_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44,
    );
    v___x_1613_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15;
    v___x_1614_ = leanh::lean_box(2);
    v___x_1615_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1615_, 0, v___x_1614_);
    leanh::lean_ctor_set(v___x_1615_, 1, v___x_1613_);
    leanh::lean_ctor_set(v___x_1615_, 2, v___x_1612_);
    return v___x_1615_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1616_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45,
    );
    v___x_1617_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13,
    );
    v___x_1618_ = lean_array_push(v___x_1617_, v___x_1616_);
    return v___x_1618_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47;
    v___x_1624_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46,
    );
    v___x_1625_ = lean_array_push(v___x_1624_, v___x_1623_);
    return v___x_1625_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47;
    v___x_1627_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48,
    );
    v___x_1628_ = lean_array_push(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47;
    v___x_1630_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49,
    );
    v___x_1631_ = lean_array_push(v___x_1630_, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47;
    v___x_1633_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50,
    );
    v___x_1634_ = lean_array_push(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51,
    );
    v___x_1636_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11;
    v___x_1637_ = leanh::lean_box(2);
    v___x_1638_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    leanh::lean_ctor_set(v___x_1638_, 1, v___x_1636_);
    leanh::lean_ctor_set(v___x_1638_, 2, v___x_1635_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52,
    );
    v___x_1640_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1641_ = lean_array_push(v___x_1640_, v___x_1639_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53,
    );
    v___x_1643_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9;
    v___x_1644_ = leanh::lean_box(2);
    v___x_1645_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
    leanh::lean_ctor_set(v___x_1645_, 1, v___x_1643_);
    leanh::lean_ctor_set(v___x_1645_, 2, v___x_1642_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55()
-> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54,
    );
    v___x_1647_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1648_ = lean_array_push(v___x_1647_, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56()
-> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55,
    );
    v___x_1650_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7;
    v___x_1651_ = leanh::lean_box(2);
    v___x_1652_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
    leanh::lean_ctor_set(v___x_1652_, 1, v___x_1650_);
    leanh::lean_ctor_set(v___x_1652_, 2, v___x_1649_);
    return v___x_1652_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56,
    );
    v___x_1654_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5;
    v___x_1655_ = lean_array_push(v___x_1654_, v___x_1653_);
    return v___x_1655_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57,
    );
    v___x_1657_ = l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4;
    v___x_1658_ = leanh::lean_box(2);
    v___x_1659_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
    leanh::lean_ctor_set(v___x_1659_, 1, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 2, v___x_1656_);
    return v___x_1659_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam() -> *mut leanh::LeanObject
{
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58_once),
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58,
    );
    return v___x_1660_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(
    mut v_decls_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1667_, 0, v_decls_1661_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(
    mut v_decls_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(
        v_decls_1668_,
        v___y_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
    );
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec_ref(v___y_1671_);
    leanh::lean_dec(v___y_1670_);
    leanh::lean_dec_ref(v___y_1669_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(
    mut v___y_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1687_, 0, v___y_1683_);
    return v___x_1687_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(
        v___y_1688_,
        v___y_1689_,
        v___y_1690_,
    );
    leanh::lean_dec(v___y_1690_);
    leanh::lean_dec_ref(v___y_1689_);
    return v_res_1692_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(
    mut v_run_1706_: *mut leanh::LeanObject,
    mut v_sz_1707_: usize,
    mut v_i_1708_: usize,
    mut v_bs_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: usize = 0;
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
                if v___x_1715_ == 0 {
                    leanh::lean_dec_ref(v_run_1706_);
                    v___x_1716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1716_, 0, v_bs_1709_);
                    return v___x_1716_;
                } else {
                    v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0;
                    v___x_1718_ = l_Lean_Core_checkSystem(v___x_1717_, v___y_1712_, v___y_1713_);
                    if leanh::lean_obj_tag(v___x_1718_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1718_, 1);
                        v_v_1719_ = lean_array_uget_borrowed(v_bs_1709_, v_i_1708_);
                        leanh::lean_inc_ref(v_run_1706_);
                        leanh::lean_inc(v___y_1713_);
                        leanh::lean_inc_ref(v___y_1712_);
                        leanh::lean_inc(v___y_1711_);
                        leanh::lean_inc_ref(v___y_1710_);
                        leanh::lean_inc(v_v_1719_);
                        v___x_1720_ = leanh::lean_apply_6(
                            v_run_1706_,
                            v_v_1719_,
                            v___y_1710_,
                            v___y_1711_,
                            v___y_1712_,
                            v___y_1713_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_1720_) == 0 {
                            v_a_1721_ = leanh::lean_ctor_get(v___x_1720_, 0);
                            leanh::lean_inc(v_a_1721_);
                            leanh::lean_dec_ref_known(v___x_1720_, 1);
                            v___x_1722_ = leanh::lean_unsigned_to_nat(0);
                            v_bs_x27_1723_ = lean_array_uset(v_bs_1709_, v_i_1708_, v___x_1722_);
                            v___x_1724_ = 1usize;
                            v___x_1725_ = lean_usize_add(v_i_1708_, v___x_1724_);
                            v___x_1726_ = lean_array_uset(v_bs_x27_1723_, v_i_1708_, v_a_1721_);
                            v_i_1708_ = v___x_1725_;
                            v_bs_1709_ = v___x_1726_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_1709_);
                            leanh::lean_dec_ref(v_run_1706_);
                            v_a_1728_ = leanh::lean_ctor_get(v___x_1720_, 0);
                            v_isSharedCheck_1735_ =
                                (!leanh::lean_is_exclusive(v___x_1720_)) as u8;
                            if v_isSharedCheck_1735_ == 0 {
                                v___x_1730_ = v___x_1720_;
                                v_isShared_1731_ = v_isSharedCheck_1735_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1728_);
                                leanh::lean_dec(v___x_1720_);
                                v___x_1730_ = leanh::lean_box(0);
                                v_isShared_1731_ = v_isSharedCheck_1735_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_1709_);
                        leanh::lean_dec_ref(v_run_1706_);
                        v_a_1736_ = leanh::lean_ctor_get(v___x_1718_, 0);
                        v_isSharedCheck_1743_ =
                            (!leanh::lean_is_exclusive(v___x_1718_)) as u8;
                        if v_isSharedCheck_1743_ == 0 {
                            v___x_1738_ = v___x_1718_;
                            v_isShared_1739_ = v_isSharedCheck_1743_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1736_);
                            leanh::lean_dec(v___x_1718_);
                            v___x_1738_ = leanh::lean_box(0);
                            v_isShared_1739_ = v_isSharedCheck_1743_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1733_;
            }
            3 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(
    mut v_run_1744_: *mut leanh::LeanObject,
    mut v_sz_1745_: *mut leanh::LeanObject,
    mut v_i_1746_: *mut leanh::LeanObject,
    mut v_bs_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1753_: usize = 0;
    let mut v_i_boxed_1754_: usize = 0;
    let mut v_res_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1753_ = leanh::lean_unbox_usize(v_sz_1745_);
    leanh::lean_dec(v_sz_1745_);
    v_i_boxed_1754_ = leanh::lean_unbox_usize(v_i_1746_);
    leanh::lean_dec(v_i_1746_);
    v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_1744_, v_sz_boxed_1753_, v_i_boxed_1754_, v_bs_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
    leanh::lean_dec(v___y_1751_);
    leanh::lean_dec_ref(v___y_1750_);
    leanh::lean_dec(v___y_1749_);
    leanh::lean_dec_ref(v___y_1748_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(
    mut v_run_1756_: *mut leanh::LeanObject,
    mut v_xs_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1763_: usize = 0;
    let mut v___x_1764_: usize = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1763_ = lean_array_size(v_xs_1757_);
    v___x_1764_ = 0usize;
    v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_1756_, v_sz_1763_, v___x_1764_, v_xs_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
    return v___x_1765_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(
    mut v_run_1766_: *mut leanh::LeanObject,
    mut v_xs_1767_: *mut leanh::LeanObject,
    mut v___y_1768_: *mut leanh::LeanObject,
    mut v___y_1769_: *mut leanh::LeanObject,
    mut v___y_1770_: *mut leanh::LeanObject,
    mut v___y_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(
        v_run_1766_,
        v_xs_1767_,
        v___y_1768_,
        v___y_1769_,
        v___y_1770_,
        v___y_1771_,
    );
    leanh::lean_dec(v___y_1771_);
    leanh::lean_dec_ref(v___y_1770_);
    leanh::lean_dec(v___y_1769_);
    leanh::lean_dec_ref(v___y_1768_);
    return v_res_1773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
    mut v_name_1774_: *mut leanh::LeanObject,
    mut v_phase_1775_: u8,
    mut v_run_1776_: *mut leanh::LeanObject,
    mut v_occurrence_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1778_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_1778_, 0, v_run_1776_);
    v___x_1779_ = 0;
    v___x_1780_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
    leanh::lean_ctor_set(v___x_1780_, 0, v_occurrence_1777_);
    leanh::lean_ctor_set(v___x_1780_, 1, v_name_1774_);
    leanh::lean_ctor_set(v___x_1780_, 2, v___f_1778_);
    leanh::lean_ctor_set_uint8(
        v___x_1780_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_phase_1775_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1780_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
        v_phase_1775_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1780_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1779_,
    );
    return v___x_1780_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(
    mut v_name_1781_: *mut leanh::LeanObject,
    mut v_phase_1782_: *mut leanh::LeanObject,
    mut v_run_1783_: *mut leanh::LeanObject,
    mut v_occurrence_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_1785_: u8 = 0;
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1785_ = (leanh::lean_unbox(v_phase_1782_) as u8);
    v_res_1786_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v_name_1781_,
        v_phase_boxed_1785_,
        v_run_1783_,
        v_occurrence_1784_,
    );
    return v_res_1786_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1787_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
    v___x_1789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1789_, 0, v___x_1788_);
    return v___x_1789_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
    v___x_1791_ = leanh::lean_unsigned_to_nat(0);
    v___x_1792_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1792_, 0, v___x_1791_);
    leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
    leanh::lean_ctor_set(v___x_1792_, 2, v___x_1791_);
    leanh::lean_ctor_set(v___x_1792_, 3, v___x_1791_);
    leanh::lean_ctor_set(v___x_1792_, 4, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 5, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 6, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 7, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 8, v___x_1790_);
    leanh::lean_ctor_set(v___x_1792_, 9, v___x_1790_);
    return v___x_1792_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = leanh::lean_unsigned_to_nat(32);
    v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
    v___x_1795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1795_, 0, v___x_1794_);
    return v___x_1795_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1796_: usize = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = 5usize;
    v___x_1797_ = leanh::lean_unsigned_to_nat(0);
    v___x_1798_ = leanh::lean_unsigned_to_nat(32);
    v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
    v___x_1800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
    v___x_1801_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1799_);
    leanh::lean_ctor_set(v___x_1801_, 2, v___x_1797_);
    leanh::lean_ctor_set(v___x_1801_, 3, v___x_1797_);
    leanh::lean_ctor_set_usize(v___x_1801_, 4, v___x_1796_);
    return v___x_1801_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = leanh::lean_box(1);
    v___x_1803_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
    v___x_1804_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
    v___x_1805_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    leanh::lean_ctor_set(v___x_1805_, 1, v___x_1803_);
    leanh::lean_ctor_set(v___x_1805_, 2, v___x_1802_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(
    mut v_msgData_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = lean_st_ref_get(v___y_1808_);
    v_env_1811_ = leanh::lean_ctor_get(v___x_1810_, 0);
    leanh::lean_inc_ref(v_env_1811_);
    leanh::lean_dec(v___x_1810_);
    v_options_1812_ = leanh::lean_ctor_get(v___y_1807_, 2);
    v___x_1813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
    v___x_1814_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_1812_);
    v___x_1815_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1815_, 0, v_env_1811_);
    leanh::lean_ctor_set(v___x_1815_, 1, v___x_1813_);
    leanh::lean_ctor_set(v___x_1815_, 2, v___x_1814_);
    leanh::lean_ctor_set(v___x_1815_, 3, v_options_1812_);
    v___x_1816_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1816_, 0, v___x_1815_);
    leanh::lean_ctor_set(v___x_1816_, 1, v_msgData_1806_);
    v___x_1817_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(
    mut v_msgData_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_1818_, v___y_1819_, v___y_1820_);
    leanh::lean_dec(v___y_1820_);
    leanh::lean_dec_ref(v___y_1819_);
    return v_res_1822_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(
    mut v_msg_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1827_ = leanh::lean_ctor_get(v___y_1824_, 5);
                v___x_1828_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_1823_, v___y_1824_, v___y_1825_);
                v_a_1829_ = leanh::lean_ctor_get(v___x_1828_, 0);
                v_isSharedCheck_1837_ = (!leanh::lean_is_exclusive(v___x_1828_)) as u8;
                if v_isSharedCheck_1837_ == 0 {
                    v___x_1831_ = v___x_1828_;
                    v_isShared_1832_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1829_);
                    leanh::lean_dec(v___x_1828_);
                    v___x_1831_ = leanh::lean_box(0);
                    v_isShared_1832_ = v_isSharedCheck_1837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1827_);
                v___x_1833_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1833_, 0, v_ref_1827_);
                leanh::lean_ctor_set(v___x_1833_, 1, v_a_1829_);
                if v_isShared_1832_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1831_, 1);
                    leanh::lean_ctor_set(v___x_1831_, 0, v___x_1833_);
                    v___x_1835_ = v___x_1831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
                    v___x_1835_ = v_reuseFailAlloc_1836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(
    mut v_msg_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_1838_, v___y_1839_, v___y_1840_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    return v_res_1842_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(
    mut v_phase_1845_: u8,
    mut v_as_1846_: *mut leanh::LeanObject,
    mut v_sz_1847_: usize,
    mut v_i_1848_: usize,
    mut v_b_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: usize = 0;
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_1861_: u8 = 0;
    let mut v_name_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1858_ = lean_usize_dec_lt(v_i_1848_, v_sz_1847_);
                if v___x_1858_ == 0 {
                    v___x_1859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1859_, 0, v_b_1849_);
                    return v___x_1859_;
                } else {
                    v_a_1860_ = lean_array_uget_borrowed(v_as_1846_, v_i_1848_);
                    v_phase_1861_ = leanh::lean_ctor_get_uint8(
                        v_a_1860_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_name_1862_ = leanh::lean_ctor_get(v_a_1860_, 1);
                    v___x_1863_ = leanh::lean_box(0);
                    v___x_1871_ =
                        l_Lean_Compiler_LCNF_instDecidableEqPhase(v_phase_1861_, v_phase_1845_);
                    if v___x_1871_ == 0 {
                        leanh::lean_inc(v_name_1862_);
                        v___x_1872_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_1862_,
                                v___x_1858_,
                            );
                        v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0;
                        v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
                        match v_phase_1861_ {
                            0 => {
                                v___x_1883_ =
                                    l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0;
                                v___y_1876_ = v___x_1883_;
                                state = 3;
                                continue;
                            }
                            1 => {
                                v___x_1884_ =
                                    l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1;
                                v___y_1876_ = v___x_1884_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                v___x_1885_ =
                                    l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2;
                                v___y_1876_ = v___x_1885_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1854_ = v___x_1863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1855_ = 1usize;
                v___x_1856_ = lean_usize_add(v_i_1848_, v___x_1855_);
                v_i_1848_ = v___x_1856_;
                v_b_1849_ = v_a_1854_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1867_ = lean_string_append(v___y_1865_, v___y_1866_);
                v___x_1868_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
                v___x_1869_ = l_Lean_MessageData_ofFormat(v___x_1868_);
                v___x_1870_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1869_, v___y_1850_, v___y_1851_);
                if leanh::lean_obj_tag(v___x_1870_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1870_, 1);
                    v_a_1854_ = v___x_1863_;
                    state = 1;
                    continue;
                } else {
                    return v___x_1870_;
                }
            }
            3 => {
                v___x_1877_ = lean_string_append(v___x_1874_, v___y_1876_);
                v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1;
                v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
                match v_phase_1845_ {
                    0 => {
                        v___x_1880_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0;
                        v___y_1865_ = v___x_1879_;
                        v___y_1866_ = v___x_1880_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v___x_1881_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1;
                        v___y_1865_ = v___x_1879_;
                        v___y_1866_ = v___x_1881_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v___x_1882_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2;
                        v___y_1865_ = v___x_1879_;
                        v___y_1866_ = v___x_1882_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(
    mut v_phase_1886_: *mut leanh::LeanObject,
    mut v_as_1887_: *mut leanh::LeanObject,
    mut v_sz_1888_: *mut leanh::LeanObject,
    mut v_i_1889_: *mut leanh::LeanObject,
    mut v_b_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_1894_: u8 = 0;
    let mut v_sz_boxed_1895_: usize = 0;
    let mut v_i_boxed_1896_: usize = 0;
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1894_ = (leanh::lean_unbox(v_phase_1886_) as u8);
    v_sz_boxed_1895_ = leanh::lean_unbox_usize(v_sz_1888_);
    leanh::lean_dec(v_sz_1888_);
    v_i_boxed_1896_ = leanh::lean_unbox_usize(v_i_1889_);
    leanh::lean_dec(v_i_1889_);
    v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_boxed_1894_, v_as_1887_, v_sz_boxed_1895_, v_i_boxed_1896_, v_b_1890_, v___y_1891_, v___y_1892_);
    leanh::lean_dec(v___y_1892_);
    leanh::lean_dec_ref(v___y_1891_);
    leanh::lean_dec_ref(v_as_1887_);
    return v_res_1897_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(
    mut v_phase_1898_: u8,
    mut v_passes_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1904_: usize = 0;
    let mut v___x_1905_: usize = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut v_unused_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1903_ = leanh::lean_box(0);
                v_sz_1904_ = lean_array_size(v_passes_1899_);
                v___x_1905_ = 0usize;
                v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_1898_, v_passes_1899_, v_sz_1904_, v___x_1905_, v___x_1903_, v_a_1900_, v_a_1901_);
                if leanh::lean_obj_tag(v___x_1906_) == 0 {
                    v_isSharedCheck_1913_ = (!leanh::lean_is_exclusive(v___x_1906_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v_unused_1914_ = leanh::lean_ctor_get(v___x_1906_, 0);
                        leanh::lean_dec(v_unused_1914_);
                        v___x_1908_ = v___x_1906_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1906_);
                        v___x_1908_ = leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1906_;
                }
            }
            1 => {
                if v_isShared_1909_ == 0 {
                    leanh::lean_ctor_set(v___x_1908_, 0, v___x_1903_);
                    v___x_1911_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1903_);
                    v___x_1911_ = v_reuseFailAlloc_1912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(
    mut v_phase_1915_: *mut leanh::LeanObject,
    mut v_passes_1916_: *mut leanh::LeanObject,
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_1920_: u8 = 0;
    let mut v_res_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1920_ = (leanh::lean_unbox(v_phase_1915_) as u8);
    v_res_1921_ =
        l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(
            v_phase_boxed_1920_,
            v_passes_1916_,
            v_a_1917_,
            v_a_1918_,
        );
    leanh::lean_dec(v_a_1918_);
    leanh::lean_dec_ref(v_a_1917_);
    leanh::lean_dec_ref(v_passes_1916_);
    return v_res_1921_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(
    mut v_00_u03b1_1922_: *mut leanh::LeanObject,
    mut v_msg_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_1923_, v___y_1924_, v___y_1925_);
    return v___x_1927_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(
    mut v_00_u03b1_1928_: *mut leanh::LeanObject,
    mut v_msg_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(v_00_u03b1_1928_, v_msg_1929_, v___y_1930_, v___y_1931_);
    leanh::lean_dec(v___y_1931_);
    leanh::lean_dec_ref(v___y_1930_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassManager_validate(
    mut v_manager_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_basePasses_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPasses_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPassesNoLambda_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_basePasses_1938_ = leanh::lean_ctor_get(v_manager_1934_, 0);
    v_monoPasses_1939_ = leanh::lean_ctor_get(v_manager_1934_, 1);
    v_monoPassesNoLambda_1940_ = leanh::lean_ctor_get(v_manager_1934_, 2);
    v___x_1941_ = 0;
    v___x_1942_ =
        l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(
            v___x_1941_,
            v_basePasses_1938_,
            v_a_1935_,
            v_a_1936_,
        );
    if leanh::lean_obj_tag(v___x_1942_) == 0 {
        let mut v___x_1943_: u8 = 0;
        let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1942_, 1);
        v___x_1943_ = 1;
        v___x_1944_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_1943_, v_monoPasses_1939_, v_a_1935_, v_a_1936_);
        if leanh::lean_obj_tag(v___x_1944_) == 0 {
            let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1944_, 1);
            v___x_1945_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_1943_, v_monoPassesNoLambda_1940_, v_a_1935_, v_a_1936_);
            return v___x_1945_;
        } else {
            return v___x_1944_;
        }
    } else {
        return v___x_1942_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassManager_validate___boxed(
    mut v_manager_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_1946_, v_a_1947_, v_a_1948_);
    leanh::lean_dec(v_a_1948_);
    leanh::lean_dec_ref(v_a_1947_);
    leanh::lean_dec_ref(v_manager_1946_);
    return v_res_1950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(
    mut v_targetName_1951_: *mut leanh::LeanObject,
    mut v_as_1952_: *mut leanh::LeanObject,
    mut v_sz_1953_: usize,
    mut v_i_1954_: usize,
    mut v_b_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v_a_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurrence_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurrence_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
                if v___x_1962_ == 0 {
                    v___x_1963_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1963_, 0, v_b_1955_);
                    return v___x_1963_;
                } else {
                    v_fst_1964_ = leanh::lean_ctor_get(v_b_1955_, 0);
                    v_snd_1965_ = leanh::lean_ctor_get(v_b_1955_, 1);
                    v_isSharedCheck_1982_ = (!leanh::lean_is_exclusive(v_b_1955_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1967_ = v_b_1955_;
                        v_isShared_1968_ = v_isSharedCheck_1982_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1965_);
                        leanh::lean_inc(v_fst_1964_);
                        leanh::lean_dec(v_b_1955_);
                        v___x_1967_ = leanh::lean_box(0);
                        v_isShared_1968_ = v_isSharedCheck_1982_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1959_ = 1usize;
                v___x_1960_ = lean_usize_add(v_i_1954_, v___x_1959_);
                v_i_1954_ = v___x_1960_;
                v_b_1955_ = v_a_1958_;
                state = 0;
                continue;
            }
            2 => {
                v_a_1969_ = lean_array_uget_borrowed(v_as_1952_, v_i_1954_);
                v_occurrence_1977_ = leanh::lean_ctor_get(v_a_1969_, 0);
                v_name_1978_ = leanh::lean_ctor_get(v_a_1969_, 1);
                v___x_1979_ = lean_name_eq(v_name_1978_, v_targetName_1951_);
                if v___x_1979_ == 0 {
                    leanh::lean_del_object(v___x_1967_);
                    v___x_1980_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1980_, 0, v_fst_1964_);
                    leanh::lean_ctor_set(v___x_1980_, 1, v_snd_1965_);
                    v_a_1958_ = v___x_1980_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_1965_);
                    if leanh::lean_obj_tag(v_fst_1964_) == 0 {
                        if v___x_1979_ == 0 {
                            v___y_1971_ = v_fst_1964_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_occurrence_1977_);
                            v___x_1981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1981_, 0, v_occurrence_1977_);
                            v___y_1971_ = v___x_1981_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_1971_ = v_fst_1964_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_occurrence_1972_ = leanh::lean_ctor_get(v_a_1969_, 0);
                leanh::lean_inc(v_occurrence_1972_);
                v___x_1973_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1973_, 0, v_occurrence_1972_);
                if v_isShared_1968_ == 0 {
                    leanh::lean_ctor_set(v___x_1967_, 1, v___x_1973_);
                    leanh::lean_ctor_set(v___x_1967_, 0, v___y_1971_);
                    v___x_1975_ = v___x_1967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___y_1971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
                    v___x_1975_ = v_reuseFailAlloc_1976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1958_ = v___x_1975_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(
    mut v_targetName_1983_: *mut leanh::LeanObject,
    mut v_as_1984_: *mut leanh::LeanObject,
    mut v_sz_1985_: *mut leanh::LeanObject,
    mut v_i_1986_: *mut leanh::LeanObject,
    mut v_b_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1989_: usize = 0;
    let mut v_i_boxed_1990_: usize = 0;
    let mut v_res_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1989_ = leanh::lean_unbox_usize(v_sz_1985_);
    leanh::lean_dec(v_sz_1985_);
    v_i_boxed_1990_ = leanh::lean_unbox_usize(v_i_1986_);
    leanh::lean_dec(v_i_1986_);
    v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_1983_, v_as_1984_, v_sz_boxed_1989_, v_i_boxed_1990_, v_b_1987_);
    leanh::lean_dec_ref(v_as_1984_);
    leanh::lean_dec(v_targetName_1983_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(
    mut v_targetName_1995_: *mut leanh::LeanObject,
    mut v_passes_1996_: *mut leanh::LeanObject,
    mut v_a_1997_: *mut leanh::LeanObject,
    mut v_a_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2011_: usize = 0;
    let mut v___x_2012_: usize = 0;
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v_fst_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v_val_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_unused_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_a_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2010_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1;
                v_sz_2011_ = lean_array_size(v_passes_1996_);
                v___x_2012_ = 0usize;
                v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_1995_, v_passes_1996_, v_sz_2011_, v___x_2012_, v___x_2010_);
                if leanh::lean_obj_tag(v___x_2013_) == 0 {
                    v_a_2014_ = leanh::lean_ctor_get(v___x_2013_, 0);
                    v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v___x_2013_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2016_ = v___x_2013_;
                        v_isShared_2017_ = v_isSharedCheck_2033_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2014_);
                        leanh::lean_dec(v___x_2013_);
                        v___x_2016_ = leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2033_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_targetName_1995_);
                    v_a_2034_ = leanh::lean_ctor_get(v___x_2013_, 0);
                    v_isSharedCheck_2041_ = (!leanh::lean_is_exclusive(v___x_2013_)) as u8;
                    if v_isSharedCheck_2041_ == 0 {
                        v___x_2036_ = v___x_2013_;
                        v_isShared_2037_ = v_isSharedCheck_2041_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2034_);
                        leanh::lean_dec(v___x_2013_);
                        v___x_2036_ = leanh::lean_box(0);
                        v_isShared_2037_ = v_isSharedCheck_2041_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2003_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0;
                v___x_2004_ = 1;
                v___x_2005_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_targetName_1995_,
                    v___x_2004_,
                );
                v___x_2006_ = lean_string_append(v___x_2003_, v___x_2005_);
                leanh::lean_dec_ref(v___x_2005_);
                v___x_2007_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2007_, 0, v___x_2006_);
                v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
                v___x_2009_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_2008_, v___y_2001_, v___y_2002_);
                return v___x_2009_;
            }
            2 => {
                v_fst_2018_ = leanh::lean_ctor_get(v_a_2014_, 0);
                leanh::lean_inc(v_fst_2018_);
                if leanh::lean_obj_tag(v_fst_2018_) == 1 {
                    v_snd_2019_ = leanh::lean_ctor_get(v_a_2014_, 1);
                    v_isSharedCheck_2031_ = (!leanh::lean_is_exclusive(v_a_2014_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v_unused_2032_ = leanh::lean_ctor_get(v_a_2014_, 0);
                        leanh::lean_dec(v_unused_2032_);
                        v___x_2021_ = v_a_2014_;
                        v_isShared_2022_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2019_);
                        leanh::lean_dec(v_a_2014_);
                        v___x_2021_ = leanh::lean_box(0);
                        v_isShared_2022_ = v_isSharedCheck_2031_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2018_);
                    leanh::lean_del_object(v___x_2016_);
                    leanh::lean_dec(v_a_2014_);
                    v___y_2001_ = v_a_1997_;
                    v___y_2002_ = v_a_1998_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_snd_2019_) == 1 {
                    leanh::lean_dec(v_targetName_1995_);
                    v_val_2023_ = leanh::lean_ctor_get(v_fst_2018_, 0);
                    leanh::lean_inc(v_val_2023_);
                    leanh::lean_dec_ref_known(v_fst_2018_, 1);
                    v_val_2024_ = leanh::lean_ctor_get(v_snd_2019_, 0);
                    leanh::lean_inc(v_val_2024_);
                    leanh::lean_dec_ref_known(v_snd_2019_, 1);
                    if v_isShared_2022_ == 0 {
                        leanh::lean_ctor_set(v___x_2021_, 1, v_val_2024_);
                        leanh::lean_ctor_set(v___x_2021_, 0, v_val_2023_);
                        v___x_2026_ = v___x_2021_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2023_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_val_2024_);
                        v___x_2026_ = v_reuseFailAlloc_2030_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2021_);
                    leanh::lean_dec_ref_known(v_fst_2018_, 1);
                    leanh::lean_dec(v_snd_2019_);
                    leanh::lean_del_object(v___x_2016_);
                    v___y_2001_ = v_a_1997_;
                    v___y_2002_ = v_a_1998_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_2017_ == 0 {
                    leanh::lean_ctor_set(v___x_2016_, 0, v___x_2026_);
                    v___x_2028_ = v___x_2016_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2028_;
            }
            6 => {
                if v_isShared_2037_ == 0 {
                    v___x_2039_ = v___x_2036_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
                    v___x_2039_ = v_reuseFailAlloc_2040_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(
    mut v_targetName_2042_: *mut leanh::LeanObject,
    mut v_passes_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(
        v_targetName_2042_,
        v_passes_2043_,
        v_a_2044_,
        v_a_2045_,
    );
    leanh::lean_dec(v_a_2045_);
    leanh::lean_dec_ref(v_a_2044_);
    leanh::lean_dec_ref(v_passes_2043_);
    return v_res_2047_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(
    mut v_targetName_2048_: *mut leanh::LeanObject,
    mut v_as_2049_: *mut leanh::LeanObject,
    mut v_sz_2050_: usize,
    mut v_i_2051_: usize,
    mut v_b_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_2048_, v_as_2049_, v_sz_2050_, v_i_2051_, v_b_2052_);
    return v___x_2056_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(
    mut v_targetName_2057_: *mut leanh::LeanObject,
    mut v_as_2058_: *mut leanh::LeanObject,
    mut v_sz_2059_: *mut leanh::LeanObject,
    mut v_i_2060_: *mut leanh::LeanObject,
    mut v_b_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2065_: usize = 0;
    let mut v_i_boxed_2066_: usize = 0;
    let mut v_res_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2065_ = leanh::lean_unbox_usize(v_sz_2059_);
    leanh::lean_dec(v_sz_2059_);
    v_i_boxed_2066_ = leanh::lean_unbox_usize(v_i_2060_);
    leanh::lean_dec(v_i_2060_);
    v_res_2067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_2057_, v_as_2058_, v_sz_boxed_2065_, v_i_boxed_2066_, v_b_2061_, v___y_2062_, v___y_2063_);
    leanh::lean_dec(v___y_2063_);
    leanh::lean_dec_ref(v___y_2062_);
    leanh::lean_dec_ref(v_as_2058_);
    leanh::lean_dec(v_targetName_2057_);
    return v_res_2067_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(
    mut v_p_2068_: *mut leanh::LeanObject,
    mut v_passes_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2073_ = lean_array_push(v_passes_2069_, v_p_2068_);
    v___x_2074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
    return v___x_2074_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(
    mut v_p_2075_: *mut leanh::LeanObject,
    mut v_passes_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(
        v_p_2075_,
        v_passes_2076_,
        v___y_2077_,
        v___y_2078_,
    );
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2080_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(
    mut v_phase_2081_: u8,
    mut v_p_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2083_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2083_, 0, v_p_2082_);
    v___x_2084_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2084_, 0, v___f_2083_);
    leanh::lean_ctor_set_uint8(
        v___x_2084_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2081_,
    );
    return v___x_2084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(
    mut v_phase_2085_: *mut leanh::LeanObject,
    mut v_p_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2087_: u8 = 0;
    let mut v_res_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2087_ = (leanh::lean_unbox(v_phase_2085_) as u8);
    v_res_2088_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_boxed_2087_, v_p_2086_);
    return v_res_2088_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(
    mut v_passesNew_2089_: *mut leanh::LeanObject,
    mut v_passes_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Array_append___redArg(v_passes_2090_, v_passesNew_2089_);
    v___x_2095_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2095_, 0, v___x_2094_);
    return v___x_2095_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(
    mut v_passesNew_2096_: *mut leanh::LeanObject,
    mut v_passes_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(
        v_passesNew_2096_,
        v_passes_2097_,
        v___y_2098_,
        v___y_2099_,
    );
    leanh::lean_dec(v___y_2099_);
    leanh::lean_dec_ref(v___y_2098_);
    leanh::lean_dec_ref(v_passesNew_2096_);
    return v_res_2101_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_append(
    mut v_phase_2102_: u8,
    mut v_passesNew_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2104_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2104_, 0, v_passesNew_2103_);
    v___x_2105_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2105_, 0, v___f_2104_);
    leanh::lean_ctor_set_uint8(
        v___x_2105_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2102_,
    );
    return v___x_2105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_append___boxed(
    mut v_phase_2106_: *mut leanh::LeanObject,
    mut v_passesNew_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2108_: u8 = 0;
    let mut v_res_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2108_ = (leanh::lean_unbox(v_phase_2106_) as u8);
    v_res_2109_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_boxed_2108_, v_passesNew_2107_);
    return v_res_2109_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(
    mut v_msg_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678__overap_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2115_ =
        l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0;
    v___x_1678__overap_2116_ = lean_panic_fn_borrowed(v___f_2115_, v_msg_2111_);
    leanh::lean_inc(v___y_2113_);
    leanh::lean_inc_ref(v___y_2112_);
    v___x_2117_ = leanh::lean_apply_3(
        v___x_1678__overap_2116_,
        v___y_2112_,
        v___y_2113_,
        leanh::lean_box(0),
    );
    return v___x_2117_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(
    mut v_msg_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(
        v_msg_2118_,
        v___y_2119_,
        v___y_2120_,
    );
    leanh::lean_dec(v___y_2120_);
    leanh::lean_dec_ref(v___y_2119_);
    return v_res_2122_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(
    mut v_install_2123_: *mut leanh::LeanObject,
    mut v_b_2124_: *mut leanh::LeanObject,
    mut v_____r_2125_: *mut leanh::LeanObject,
    mut v___y_2126_: *mut leanh::LeanObject,
    mut v___y_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_a_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_2127_);
                leanh::lean_inc_ref(v___y_2126_);
                v___x_2129_ = leanh::lean_apply_4(
                    v_install_2123_,
                    v_b_2124_,
                    v___y_2126_,
                    v___y_2127_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2129_) == 0 {
                    v_a_2130_ = leanh::lean_ctor_get(v___x_2129_, 0);
                    v_isSharedCheck_2138_ = (!leanh::lean_is_exclusive(v___x_2129_)) as u8;
                    if v_isSharedCheck_2138_ == 0 {
                        v___x_2132_ = v___x_2129_;
                        v_isShared_2133_ = v_isSharedCheck_2138_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2130_);
                        leanh::lean_dec(v___x_2129_);
                        v___x_2132_ = leanh::lean_box(0);
                        v_isShared_2133_ = v_isSharedCheck_2138_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2139_ = leanh::lean_ctor_get(v___x_2129_, 0);
                    v_isSharedCheck_2146_ = (!leanh::lean_is_exclusive(v___x_2129_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v___x_2141_ = v___x_2129_;
                        v_isShared_2142_ = v_isSharedCheck_2146_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2139_);
                        leanh::lean_dec(v___x_2129_);
                        v___x_2141_ = leanh::lean_box(0);
                        v_isShared_2142_ = v_isSharedCheck_2146_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2134_, 0, v_a_2130_);
                if v_isShared_2133_ == 0 {
                    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2134_);
                    v___x_2136_ = v___x_2132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
                    v___x_2136_ = v_reuseFailAlloc_2137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2136_;
            }
            3 => {
                if v_isShared_2142_ == 0 {
                    v___x_2144_ = v___x_2141_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
                    v___x_2144_ = v_reuseFailAlloc_2145_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(
    mut v_install_2147_: *mut leanh::LeanObject,
    mut v_b_2148_: *mut leanh::LeanObject,
    mut v_____r_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_2147_, v_b_2148_, v_____r_2149_, v___y_2150_, v___y_2151_);
    leanh::lean_dec(v___y_2151_);
    leanh::lean_dec_ref(v___y_2150_);
    return v_res_2153_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1;
    v___x_2157_ = leanh::lean_unsigned_to_nat(8);
    v___x_2158_ = leanh::lean_unsigned_to_nat(170);
    v___x_2159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0;
    v___x_2160_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0;
    v___x_2161_ = l_mkPanicMessageWithDecl(
        v___x_2160_,
        v___x_2159_,
        v___x_2158_,
        v___x_2157_,
        v___x_2156_,
    );
    return v___x_2161_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(
    mut v_upperBound_2162_: *mut leanh::LeanObject,
    mut v_f_2163_: *mut leanh::LeanObject,
    mut v_phase_2164_: u8,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_b_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v_a_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_2196_: u8 = 0;
    let mut v_install_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = lean_nat_dec_le(v_a_2165_, v_upperBound_2162_);
                if v___x_2193_ == 0 {
                    leanh::lean_dec(v_a_2165_);
                    leanh::lean_dec_ref(v_f_2163_);
                    v___x_2194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2194_, 0, v_b_2166_);
                    return v___x_2194_;
                } else {
                    leanh::lean_inc_ref(v_f_2163_);
                    leanh::lean_inc(v_a_2165_);
                    v___x_2195_ = leanh::lean_apply_1(v_f_2163_, v_a_2165_);
                    v_phase_2196_ = leanh::lean_ctor_get_uint8(
                        v___x_2195_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_install_2197_ = leanh::lean_ctor_get(v___x_2195_, 0);
                    leanh::lean_inc_ref(v_install_2197_);
                    leanh::lean_dec_ref(v___x_2195_);
                    v___x_2198_ =
                        l_Lean_Compiler_LCNF_instDecidableEqPhase(v_phase_2196_, v_phase_2164_);
                    if v___x_2198_ == 0 {
                        v___x_2199_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
                        v___x_2200_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_2199_, v___y_2167_, v___y_2168_);
                        if leanh::lean_obj_tag(v___x_2200_) == 0 {
                            v_a_2201_ = leanh::lean_ctor_get(v___x_2200_, 0);
                            leanh::lean_inc(v_a_2201_);
                            leanh::lean_dec_ref_known(v___x_2200_, 1);
                            v___x_2202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_2197_, v_b_2166_, v_a_2201_, v___y_2167_, v___y_2168_);
                            v___y_2171_ = v___x_2202_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_install_2197_);
                            leanh::lean_dec_ref(v_b_2166_);
                            leanh::lean_dec(v_a_2165_);
                            leanh::lean_dec_ref(v_f_2163_);
                            v_a_2203_ = leanh::lean_ctor_get(v___x_2200_, 0);
                            v_isSharedCheck_2210_ =
                                (!leanh::lean_is_exclusive(v___x_2200_)) as u8;
                            if v_isSharedCheck_2210_ == 0 {
                                v___x_2205_ = v___x_2200_;
                                v_isShared_2206_ = v_isSharedCheck_2210_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2203_);
                                leanh::lean_dec(v___x_2200_);
                                v___x_2205_ = leanh::lean_box(0);
                                v_isShared_2206_ = v_isSharedCheck_2210_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_2211_ = leanh::lean_box(0);
                        v___x_2212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_2197_, v_b_2166_, v___x_2211_, v___y_2167_, v___y_2168_);
                        v___y_2171_ = v___x_2212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2171_) == 0 {
                    v_a_2172_ = leanh::lean_ctor_get(v___y_2171_, 0);
                    v_isSharedCheck_2184_ = (!leanh::lean_is_exclusive(v___y_2171_)) as u8;
                    if v_isSharedCheck_2184_ == 0 {
                        v___x_2174_ = v___y_2171_;
                        v_isShared_2175_ = v_isSharedCheck_2184_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2172_);
                        leanh::lean_dec(v___y_2171_);
                        v___x_2174_ = leanh::lean_box(0);
                        v_isShared_2175_ = v_isSharedCheck_2184_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2165_);
                    leanh::lean_dec_ref(v_f_2163_);
                    v_a_2185_ = leanh::lean_ctor_get(v___y_2171_, 0);
                    v_isSharedCheck_2192_ = (!leanh::lean_is_exclusive(v___y_2171_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___y_2171_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2185_);
                        leanh::lean_dec(v___y_2171_);
                        v___x_2187_ = leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2172_) == 0 {
                    leanh::lean_dec(v_a_2165_);
                    leanh::lean_dec_ref(v_f_2163_);
                    v_a_2176_ = leanh::lean_ctor_get(v_a_2172_, 0);
                    leanh::lean_inc(v_a_2176_);
                    leanh::lean_dec_ref_known(v_a_2172_, 1);
                    if v_isShared_2175_ == 0 {
                        leanh::lean_ctor_set(v___x_2174_, 0, v_a_2176_);
                        v___x_2178_ = v___x_2174_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2179_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2176_);
                        v___x_2178_ = v_reuseFailAlloc_2179_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2174_);
                    v_a_2180_ = leanh::lean_ctor_get(v_a_2172_, 0);
                    leanh::lean_inc(v_a_2180_);
                    leanh::lean_dec_ref_known(v_a_2172_, 1);
                    v___x_2181_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2182_ = lean_nat_add(v_a_2165_, v___x_2181_);
                    leanh::lean_dec(v_a_2165_);
                    v_a_2165_ = v___x_2182_;
                    v_b_2166_ = v_a_2180_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_2178_;
            }
            4 => {
                if v_isShared_2188_ == 0 {
                    v___x_2190_ = v___x_2187_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2190_;
            }
            6 => {
                if v_isShared_2206_ == 0 {
                    v___x_2208_ = v___x_2205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(
    mut v_upperBound_2213_: *mut leanh::LeanObject,
    mut v_f_2214_: *mut leanh::LeanObject,
    mut v_phase_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_b_2217_: *mut leanh::LeanObject,
    mut v___y_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2221_: u8 = 0;
    let mut v_res_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2221_ = (leanh::lean_unbox(v_phase_2215_) as u8);
    v_res_2222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_2213_, v_f_2214_, v_phase_boxed_2221_, v_a_2216_, v_b_2217_, v___y_2218_, v___y_2219_);
    leanh::lean_dec(v___y_2219_);
    leanh::lean_dec_ref(v___y_2218_);
    leanh::lean_dec(v_upperBound_2213_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(
    mut v_targetName_2223_: *mut leanh::LeanObject,
    mut v_f_2224_: *mut leanh::LeanObject,
    mut v_phase_2225_: u8,
    mut v_passes_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2230_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(
                    v_targetName_2223_,
                    v_passes_2226_,
                    v___y_2227_,
                    v___y_2228_,
                );
                if leanh::lean_obj_tag(v___x_2230_) == 0 {
                    v_a_2231_ = leanh::lean_ctor_get(v___x_2230_, 0);
                    leanh::lean_inc(v_a_2231_);
                    leanh::lean_dec_ref_known(v___x_2230_, 1);
                    v_fst_2232_ = leanh::lean_ctor_get(v_a_2231_, 0);
                    leanh::lean_inc(v_fst_2232_);
                    v_snd_2233_ = leanh::lean_ctor_get(v_a_2231_, 1);
                    leanh::lean_inc(v_snd_2233_);
                    leanh::lean_dec(v_a_2231_);
                    v___x_2234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_2233_, v_f_2224_, v_phase_2225_, v_fst_2232_, v_passes_2226_, v___y_2227_, v___y_2228_);
                    leanh::lean_dec(v_snd_2233_);
                    return v___x_2234_;
                } else {
                    leanh::lean_dec_ref(v_passes_2226_);
                    leanh::lean_dec_ref(v_f_2224_);
                    v_a_2235_ = leanh::lean_ctor_get(v___x_2230_, 0);
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2230_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2237_ = v___x_2230_;
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2235_);
                        leanh::lean_dec(v___x_2230_);
                        v___x_2237_ = leanh::lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2238_ == 0 {
                    v___x_2240_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(
    mut v_targetName_2243_: *mut leanh::LeanObject,
    mut v_f_2244_: *mut leanh::LeanObject,
    mut v_phase_2245_: *mut leanh::LeanObject,
    mut v_passes_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2250_ = (leanh::lean_unbox(v_phase_2245_) as u8);
    v_res_2251_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(
        v_targetName_2243_,
        v_f_2244_,
        v_phase_boxed_2250_,
        v_passes_2246_,
        v___y_2247_,
        v___y_2248_,
    );
    leanh::lean_dec(v___y_2248_);
    leanh::lean_dec_ref(v___y_2247_);
    return v_res_2251_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(
    mut v_phase_2252_: u8,
    mut v_targetName_2253_: *mut leanh::LeanObject,
    mut v_f_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2255_ = leanh::lean_box((v_phase_2252_) as usize);
    v___f_2256_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___f_2256_, 0, v_targetName_2253_);
    leanh::lean_closure_set(v___f_2256_, 1, v_f_2254_);
    leanh::lean_closure_set(v___f_2256_, 2, v___x_2255_);
    v___x_2257_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2257_, 0, v___f_2256_);
    leanh::lean_ctor_set_uint8(
        v___x_2257_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2252_,
    );
    return v___x_2257_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(
    mut v_phase_2258_: *mut leanh::LeanObject,
    mut v_targetName_2259_: *mut leanh::LeanObject,
    mut v_f_2260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2261_: u8 = 0;
    let mut v_res_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2261_ = (leanh::lean_unbox(v_phase_2258_) as u8);
    v_res_2262_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(
        v_phase_boxed_2261_,
        v_targetName_2259_,
        v_f_2260_,
    );
    return v_res_2262_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(
    mut v_upperBound_2263_: *mut leanh::LeanObject,
    mut v_f_2264_: *mut leanh::LeanObject,
    mut v_phase_2265_: u8,
    mut v_inst_2266_: *mut leanh::LeanObject,
    mut v_R_2267_: *mut leanh::LeanObject,
    mut v_a_2268_: *mut leanh::LeanObject,
    mut v_b_2269_: *mut leanh::LeanObject,
    mut v_c_2270_: *mut leanh::LeanObject,
    mut v___y_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_2263_, v_f_2264_, v_phase_2265_, v_a_2268_, v_b_2269_, v___y_2271_, v___y_2272_);
    return v___x_2274_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(
    mut v_upperBound_2275_: *mut leanh::LeanObject,
    mut v_f_2276_: *mut leanh::LeanObject,
    mut v_phase_2277_: *mut leanh::LeanObject,
    mut v_inst_2278_: *mut leanh::LeanObject,
    mut v_R_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
    mut v_b_2281_: *mut leanh::LeanObject,
    mut v_c_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2286_: u8 = 0;
    let mut v_res_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2286_ = (leanh::lean_unbox(v_phase_2277_) as u8);
    v_res_2287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_2275_, v_f_2276_, v_phase_boxed_2286_, v_inst_2278_, v_R_2279_, v_a_2280_, v_b_2281_, v_c_2282_, v___y_2283_, v___y_2284_);
    leanh::lean_dec(v___y_2284_);
    leanh::lean_dec_ref(v___y_2283_);
    leanh::lean_dec(v_upperBound_2275_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(
    mut v_targetName_2288_: *mut leanh::LeanObject,
    mut v_occurrence_2289_: *mut leanh::LeanObject,
    mut v_p_2290_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_occurrence_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    v_occurrence_2291_ = leanh::lean_ctor_get(v_p_2290_, 0);
    v_name_2292_ = leanh::lean_ctor_get(v_p_2290_, 1);
    v___x_2293_ = lean_name_eq(v_name_2292_, v_targetName_2288_);
    if v___x_2293_ == 0 {
        return v___x_2293_;
    } else {
        let mut v___x_2294_: u8 = 0;
        v___x_2294_ = lean_nat_dec_eq(v_occurrence_2291_, v_occurrence_2289_);
        return v___x_2294_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(
    mut v_targetName_2295_: *mut leanh::LeanObject,
    mut v_occurrence_2296_: *mut leanh::LeanObject,
    mut v_p_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2298_: u8 = 0;
    let mut v_r_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(
        v_targetName_2295_,
        v_occurrence_2296_,
        v_p_2297_,
    );
    leanh::lean_dec_ref(v_p_2297_);
    leanh::lean_dec(v_occurrence_2296_);
    leanh::lean_dec(v_targetName_2295_);
    v_r_2299_ = leanh::lean_box((v_res_2298_) as usize);
    return v_r_2299_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(
    mut v___f_2304_: *mut leanh::LeanObject,
    mut v_p_2305_: *mut leanh::LeanObject,
    mut v_targetName_2306_: *mut leanh::LeanObject,
    mut v_occurrence_2307_: *mut leanh::LeanObject,
    mut v_passes_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v_passUnderTest_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2312_ = leanh::lean_unsigned_to_nat(0);
                v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
                    leanh::lean_box(0),
                    v___f_2304_,
                    v_passes_2308_,
                    v___x_2312_,
                );
                if leanh::lean_obj_tag(v___x_2313_) == 1 {
                    leanh::lean_dec(v_occurrence_2307_);
                    leanh::lean_dec(v_targetName_2306_);
                    v_val_2314_ = leanh::lean_ctor_get(v___x_2313_, 0);
                    v_isSharedCheck_2328_ = (!leanh::lean_is_exclusive(v___x_2313_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2316_ = v___x_2313_;
                        v_isShared_2317_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2314_);
                        leanh::lean_dec(v___x_2313_);
                        v___x_2316_ = leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2313_);
                    leanh::lean_dec_ref(v_passes_2308_);
                    leanh::lean_dec_ref(v_p_2305_);
                    v___x_2329_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0;
                    v___x_2330_ = 1;
                    v___x_2331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_targetName_2306_,
                        v___x_2330_,
                    );
                    v___x_2332_ = lean_string_append(v___x_2329_, v___x_2331_);
                    v___x_2333_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1;
                    v___x_2334_ = lean_string_append(v___x_2332_, v___x_2333_);
                    v___x_2335_ = l_Nat_reprFast(v_occurrence_2307_);
                    v___x_2336_ = lean_string_append(v___x_2334_, v___x_2335_);
                    leanh::lean_dec_ref(v___x_2335_);
                    v___x_2337_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2;
                    v___x_2338_ = lean_string_append(v___x_2336_, v___x_2337_);
                    v___x_2339_ = lean_string_append(v___x_2338_, v___x_2331_);
                    leanh::lean_dec_ref(v___x_2331_);
                    v___x_2340_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3;
                    v___x_2341_ = lean_string_append(v___x_2339_, v___x_2340_);
                    v___x_2342_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                    v___x_2343_ = l_Lean_MessageData_ofFormat(v___x_2342_);
                    v___x_2344_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_2343_, v___y_2309_, v___y_2310_);
                    return v___x_2344_;
                }
            }
            1 => {
                v_passUnderTest_2318_ = lean_array_fget_borrowed(v_passes_2308_, v_val_2314_);
                v___x_2319_ = leanh::lean_unsigned_to_nat(1);
                v___x_2320_ = lean_nat_add(v_val_2314_, v___x_2319_);
                leanh::lean_dec(v_val_2314_);
                leanh::lean_inc(v_passUnderTest_2318_);
                v___x_2321_ = leanh::lean_apply_1(v_p_2305_, v_passUnderTest_2318_);
                v_j_2322_ = lean_array_get_size(v_passes_2308_);
                v_as_2323_ = lean_array_push(v_passes_2308_, v___x_2321_);
                v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                    leanh::lean_box(0),
                    v___x_2320_,
                    v_as_2323_,
                    v_j_2322_,
                );
                leanh::lean_dec(v___x_2320_);
                if v_isShared_2317_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2316_, 0);
                    leanh::lean_ctor_set(v___x_2316_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(
    mut v___f_2345_: *mut leanh::LeanObject,
    mut v_p_2346_: *mut leanh::LeanObject,
    mut v_targetName_2347_: *mut leanh::LeanObject,
    mut v_occurrence_2348_: *mut leanh::LeanObject,
    mut v_passes_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(
        v___f_2345_,
        v_p_2346_,
        v_targetName_2347_,
        v_occurrence_2348_,
        v_passes_2349_,
        v___y_2350_,
        v___y_2351_,
    );
    leanh::lean_dec(v___y_2351_);
    leanh::lean_dec_ref(v___y_2350_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter(
    mut v_phase_2354_: u8,
    mut v_targetName_2355_: *mut leanh::LeanObject,
    mut v_p_2356_: *mut leanh::LeanObject,
    mut v_occurrence_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_occurrence_2357_);
    leanh::lean_inc(v_targetName_2355_);
    v___f_2358_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2358_, 0, v_targetName_2355_);
    leanh::lean_closure_set(v___f_2358_, 1, v_occurrence_2357_);
    v___f_2359_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___f_2359_, 0, v___f_2358_);
    leanh::lean_closure_set(v___f_2359_, 1, v_p_2356_);
    leanh::lean_closure_set(v___f_2359_, 2, v_targetName_2355_);
    leanh::lean_closure_set(v___f_2359_, 3, v_occurrence_2357_);
    v___x_2360_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2360_, 0, v___f_2359_);
    leanh::lean_ctor_set_uint8(
        v___x_2360_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2354_,
    );
    return v___x_2360_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(
    mut v_phase_2361_: *mut leanh::LeanObject,
    mut v_targetName_2362_: *mut leanh::LeanObject,
    mut v_p_2363_: *mut leanh::LeanObject,
    mut v_occurrence_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2365_: u8 = 0;
    let mut v_res_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2365_ = (leanh::lean_unbox(v_phase_2361_) as u8);
    v_res_2366_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(
        v_phase_boxed_2365_,
        v_targetName_2362_,
        v_p_2363_,
        v_occurrence_2364_,
    );
    return v_res_2366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(
    mut v_phase_2367_: u8,
    mut v_targetName_2368_: *mut leanh::LeanObject,
    mut v_p_2369_: *mut leanh::LeanObject,
    mut v_x_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(
        v_phase_2367_,
        v_targetName_2368_,
        v_p_2369_,
        v_x_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(
    mut v_phase_2372_: *mut leanh::LeanObject,
    mut v_targetName_2373_: *mut leanh::LeanObject,
    mut v_p_2374_: *mut leanh::LeanObject,
    mut v_x_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2376_: u8 = 0;
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2376_ = (leanh::lean_unbox(v_phase_2372_) as u8);
    v_res_2377_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(
        v_phase_boxed_2376_,
        v_targetName_2373_,
        v_p_2374_,
        v_x_2375_,
    );
    return v_res_2377_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(
    mut v_phase_2378_: u8,
    mut v_targetName_2379_: *mut leanh::LeanObject,
    mut v_p_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = leanh::lean_box((v_phase_2378_) as usize);
    leanh::lean_inc(v_targetName_2379_);
    v___f_2382_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2382_, 0, v___x_2381_);
    leanh::lean_closure_set(v___f_2382_, 1, v_targetName_2379_);
    leanh::lean_closure_set(v___f_2382_, 2, v_p_2380_);
    v___x_2383_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(
        v_phase_2378_,
        v_targetName_2379_,
        v___f_2382_,
    );
    return v___x_2383_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(
    mut v_phase_2384_: *mut leanh::LeanObject,
    mut v_targetName_2385_: *mut leanh::LeanObject,
    mut v_p_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2387_: u8 = 0;
    let mut v_res_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2387_ = (leanh::lean_unbox(v_phase_2384_) as u8);
    v_res_2388_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(
        v_phase_boxed_2387_,
        v_targetName_2385_,
        v_p_2386_,
    );
    return v_res_2388_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(
    mut v___f_2389_: *mut leanh::LeanObject,
    mut v_p_2390_: *mut leanh::LeanObject,
    mut v_targetName_2391_: *mut leanh::LeanObject,
    mut v_occurrence_2392_: *mut leanh::LeanObject,
    mut v_passes_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v_passUnderTest_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2397_ = leanh::lean_unsigned_to_nat(0);
                v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
                    leanh::lean_box(0),
                    v___f_2389_,
                    v_passes_2393_,
                    v___x_2397_,
                );
                if leanh::lean_obj_tag(v___x_2398_) == 1 {
                    leanh::lean_dec(v_occurrence_2392_);
                    leanh::lean_dec(v_targetName_2391_);
                    v_val_2399_ = leanh::lean_ctor_get(v___x_2398_, 0);
                    v_isSharedCheck_2411_ = (!leanh::lean_is_exclusive(v___x_2398_)) as u8;
                    if v_isSharedCheck_2411_ == 0 {
                        v___x_2401_ = v___x_2398_;
                        v_isShared_2402_ = v_isSharedCheck_2411_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2399_);
                        leanh::lean_dec(v___x_2398_);
                        v___x_2401_ = leanh::lean_box(0);
                        v_isShared_2402_ = v_isSharedCheck_2411_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2398_);
                    leanh::lean_dec_ref(v_passes_2393_);
                    leanh::lean_dec_ref(v_p_2390_);
                    v___x_2412_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0;
                    v___x_2413_ = 1;
                    v___x_2414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_targetName_2391_,
                        v___x_2413_,
                    );
                    v___x_2415_ = lean_string_append(v___x_2412_, v___x_2414_);
                    v___x_2416_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1;
                    v___x_2417_ = lean_string_append(v___x_2415_, v___x_2416_);
                    v___x_2418_ = l_Nat_reprFast(v_occurrence_2392_);
                    v___x_2419_ = lean_string_append(v___x_2417_, v___x_2418_);
                    leanh::lean_dec_ref(v___x_2418_);
                    v___x_2420_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2;
                    v___x_2421_ = lean_string_append(v___x_2419_, v___x_2420_);
                    v___x_2422_ = lean_string_append(v___x_2421_, v___x_2414_);
                    leanh::lean_dec_ref(v___x_2414_);
                    v___x_2423_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3;
                    v___x_2424_ = lean_string_append(v___x_2422_, v___x_2423_);
                    v___x_2425_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                    v___x_2426_ = l_Lean_MessageData_ofFormat(v___x_2425_);
                    v___x_2427_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_2426_, v___y_2394_, v___y_2395_);
                    return v___x_2427_;
                }
            }
            1 => {
                v_passUnderTest_2403_ = lean_array_fget_borrowed(v_passes_2393_, v_val_2399_);
                leanh::lean_inc(v_passUnderTest_2403_);
                v___x_2404_ = leanh::lean_apply_1(v_p_2390_, v_passUnderTest_2403_);
                v_j_2405_ = lean_array_get_size(v_passes_2393_);
                v_as_2406_ = lean_array_push(v_passes_2393_, v___x_2404_);
                v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                    leanh::lean_box(0),
                    v_val_2399_,
                    v_as_2406_,
                    v_j_2405_,
                );
                leanh::lean_dec(v_val_2399_);
                if v_isShared_2402_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2401_, 0);
                    leanh::lean_ctor_set(v___x_2401_, 0, v___x_2407_);
                    v___x_2409_ = v___x_2401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(
    mut v___f_2428_: *mut leanh::LeanObject,
    mut v_p_2429_: *mut leanh::LeanObject,
    mut v_targetName_2430_: *mut leanh::LeanObject,
    mut v_occurrence_2431_: *mut leanh::LeanObject,
    mut v_passes_2432_: *mut leanh::LeanObject,
    mut v___y_2433_: *mut leanh::LeanObject,
    mut v___y_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(
        v___f_2428_,
        v_p_2429_,
        v_targetName_2430_,
        v_occurrence_2431_,
        v_passes_2432_,
        v___y_2433_,
        v___y_2434_,
    );
    leanh::lean_dec(v___y_2434_);
    leanh::lean_dec_ref(v___y_2433_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBefore(
    mut v_phase_2437_: u8,
    mut v_targetName_2438_: *mut leanh::LeanObject,
    mut v_p_2439_: *mut leanh::LeanObject,
    mut v_occurrence_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_occurrence_2440_);
    leanh::lean_inc(v_targetName_2438_);
    v___f_2441_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2441_, 0, v_targetName_2438_);
    leanh::lean_closure_set(v___f_2441_, 1, v_occurrence_2440_);
    v___f_2442_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___f_2442_, 0, v___f_2441_);
    leanh::lean_closure_set(v___f_2442_, 1, v_p_2439_);
    leanh::lean_closure_set(v___f_2442_, 2, v_targetName_2438_);
    leanh::lean_closure_set(v___f_2442_, 3, v_occurrence_2440_);
    v___x_2443_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2443_, 0, v___f_2442_);
    leanh::lean_ctor_set_uint8(
        v___x_2443_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2437_,
    );
    return v___x_2443_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(
    mut v_phase_2444_: *mut leanh::LeanObject,
    mut v_targetName_2445_: *mut leanh::LeanObject,
    mut v_p_2446_: *mut leanh::LeanObject,
    mut v_occurrence_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2448_: u8 = 0;
    let mut v_res_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2448_ = (leanh::lean_unbox(v_phase_2444_) as u8);
    v_res_2449_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(
        v_phase_boxed_2448_,
        v_targetName_2445_,
        v_p_2446_,
        v_occurrence_2447_,
    );
    return v_res_2449_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(
    mut v_phase_2450_: u8,
    mut v_targetName_2451_: *mut leanh::LeanObject,
    mut v_p_2452_: *mut leanh::LeanObject,
    mut v_x_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(
        v_phase_2450_,
        v_targetName_2451_,
        v_p_2452_,
        v_x_2453_,
    );
    return v___x_2454_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(
    mut v_phase_2455_: *mut leanh::LeanObject,
    mut v_targetName_2456_: *mut leanh::LeanObject,
    mut v_p_2457_: *mut leanh::LeanObject,
    mut v_x_2458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2459_: u8 = 0;
    let mut v_res_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2459_ = (leanh::lean_unbox(v_phase_2455_) as u8);
    v_res_2460_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(
        v_phase_boxed_2459_,
        v_targetName_2456_,
        v_p_2457_,
        v_x_2458_,
    );
    return v_res_2460_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(
    mut v_phase_2461_: u8,
    mut v_targetName_2462_: *mut leanh::LeanObject,
    mut v_p_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = leanh::lean_box((v_phase_2461_) as usize);
    leanh::lean_inc(v_targetName_2462_);
    v___f_2465_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2465_, 0, v___x_2464_);
    leanh::lean_closure_set(v___f_2465_, 1, v_targetName_2462_);
    leanh::lean_closure_set(v___f_2465_, 2, v_p_2463_);
    v___x_2466_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(
        v_phase_2461_,
        v_targetName_2462_,
        v___f_2465_,
    );
    return v___x_2466_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(
    mut v_phase_2467_: *mut leanh::LeanObject,
    mut v_targetName_2468_: *mut leanh::LeanObject,
    mut v_p_2469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2470_: u8 = 0;
    let mut v_res_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2470_ = (leanh::lean_unbox(v_phase_2467_) as u8);
    v_res_2471_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(
        v_phase_boxed_2470_,
        v_targetName_2468_,
        v_p_2469_,
    );
    return v_res_2471_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(
    mut v_targetName_2472_: *mut leanh::LeanObject,
    mut v_occurrence_2473_: *mut leanh::LeanObject,
    mut v_as_2474_: *mut leanh::LeanObject,
    mut v_j_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2477_: u8 = 0;
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurrence_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2482_ = lean_array_get_size(v_as_2474_);
                v___x_2483_ = lean_nat_dec_lt(v_j_2475_, v___x_2482_);
                if v___x_2483_ == 0 {
                    leanh::lean_dec(v_j_2475_);
                    v___x_2484_ = leanh::lean_box(0);
                    return v___x_2484_;
                } else {
                    v___x_2485_ = lean_array_fget_borrowed(v_as_2474_, v_j_2475_);
                    v_occurrence_2486_ = leanh::lean_ctor_get(v___x_2485_, 0);
                    v_name_2487_ = leanh::lean_ctor_get(v___x_2485_, 1);
                    v___x_2488_ = lean_name_eq(v_name_2487_, v_targetName_2472_);
                    if v___x_2488_ == 0 {
                        v___y_2477_ = v___x_2488_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2489_ = lean_nat_dec_eq(v_occurrence_2486_, v_occurrence_2473_);
                        v___y_2477_ = v___x_2489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2477_ == 0 {
                    v___x_2478_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2479_ = lean_nat_add(v_j_2475_, v___x_2478_);
                    leanh::lean_dec(v_j_2475_);
                    v_j_2475_ = v___x_2479_;
                    state = 0;
                    continue;
                } else {
                    v___x_2481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2481_, 0, v_j_2475_);
                    return v___x_2481_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(
    mut v_targetName_2490_: *mut leanh::LeanObject,
    mut v_occurrence_2491_: *mut leanh::LeanObject,
    mut v_as_2492_: *mut leanh::LeanObject,
    mut v_j_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2494_ =
        l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(
            v_targetName_2490_,
            v_occurrence_2491_,
            v_as_2492_,
            v_j_2493_,
        );
    leanh::lean_dec_ref(v_as_2492_);
    leanh::lean_dec(v_occurrence_2491_);
    leanh::lean_dec(v_targetName_2490_);
    return v_res_2494_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(
    mut v_targetName_2496_: *mut leanh::LeanObject,
    mut v_occurrence_2497_: *mut leanh::LeanObject,
    mut v_p_2498_: *mut leanh::LeanObject,
    mut v_passes_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2503_ = leanh::lean_unsigned_to_nat(0);
                v___x_2504_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_2496_, v_occurrence_2497_, v_passes_2499_, v___x_2503_);
                if leanh::lean_obj_tag(v___x_2504_) == 1 {
                    leanh::lean_dec(v_occurrence_2497_);
                    leanh::lean_dec(v_targetName_2496_);
                    v_val_2505_ = leanh::lean_ctor_get(v___x_2504_, 0);
                    v_isSharedCheck_2522_ = (!leanh::lean_is_exclusive(v___x_2504_)) as u8;
                    if v_isSharedCheck_2522_ == 0 {
                        v___x_2507_ = v___x_2504_;
                        v_isShared_2508_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2505_);
                        leanh::lean_dec(v___x_2504_);
                        v___x_2507_ = leanh::lean_box(0);
                        v_isShared_2508_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2504_);
                    leanh::lean_dec_ref(v_passes_2499_);
                    leanh::lean_dec_ref(v_p_2498_);
                    v___x_2523_ =
                        l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0;
                    v___x_2524_ = 1;
                    v___x_2525_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_targetName_2496_,
                        v___x_2524_,
                    );
                    v___x_2526_ = lean_string_append(v___x_2523_, v___x_2525_);
                    v___x_2527_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1;
                    v___x_2528_ = lean_string_append(v___x_2526_, v___x_2527_);
                    v___x_2529_ = l_Nat_reprFast(v_occurrence_2497_);
                    v___x_2530_ = lean_string_append(v___x_2528_, v___x_2529_);
                    leanh::lean_dec_ref(v___x_2529_);
                    v___x_2531_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2;
                    v___x_2532_ = lean_string_append(v___x_2530_, v___x_2531_);
                    v___x_2533_ = lean_string_append(v___x_2532_, v___x_2525_);
                    leanh::lean_dec_ref(v___x_2525_);
                    v___x_2534_ =
                        l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3;
                    v___x_2535_ = lean_string_append(v___x_2533_, v___x_2534_);
                    v___x_2536_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2536_, 0, v___x_2535_);
                    v___x_2537_ = l_Lean_MessageData_ofFormat(v___x_2536_);
                    v___x_2538_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_2537_, v___y_2500_, v___y_2501_);
                    return v___x_2538_;
                }
            }
            1 => {
                v___x_2509_ = lean_array_get_size(v_passes_2499_);
                v___x_2510_ = lean_nat_dec_lt(v_val_2505_, v___x_2509_);
                if v___x_2510_ == 0 {
                    leanh::lean_dec(v_val_2505_);
                    leanh::lean_dec_ref(v_p_2498_);
                    if v_isShared_2508_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2507_, 0);
                        leanh::lean_ctor_set(v___x_2507_, 0, v_passes_2499_);
                        v___x_2512_ = v___x_2507_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_passes_2499_);
                        v___x_2512_ = v_reuseFailAlloc_2513_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_v_2514_ = lean_array_fget(v_passes_2499_, v_val_2505_);
                    v___x_2515_ = leanh::lean_box(0);
                    v_xs_x27_2516_ = lean_array_fset(v_passes_2499_, v_val_2505_, v___x_2515_);
                    v___x_2517_ = leanh::lean_apply_1(v_p_2498_, v_v_2514_);
                    v___x_2518_ = lean_array_fset(v_xs_x27_2516_, v_val_2505_, v___x_2517_);
                    leanh::lean_dec(v_val_2505_);
                    if v_isShared_2508_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2507_, 0);
                        leanh::lean_ctor_set(v___x_2507_, 0, v___x_2518_);
                        v___x_2520_ = v___x_2507_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                        v___x_2520_ = v_reuseFailAlloc_2521_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2512_;
            }
            3 => {
                return v___x_2520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(
    mut v_targetName_2539_: *mut leanh::LeanObject,
    mut v_occurrence_2540_: *mut leanh::LeanObject,
    mut v_p_2541_: *mut leanh::LeanObject,
    mut v_passes_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2546_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(
        v_targetName_2539_,
        v_occurrence_2540_,
        v_p_2541_,
        v_passes_2542_,
        v___y_2543_,
        v___y_2544_,
    );
    leanh::lean_dec(v___y_2544_);
    leanh::lean_dec_ref(v___y_2543_);
    return v_res_2546_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replacePass(
    mut v_phase_2547_: u8,
    mut v_targetName_2548_: *mut leanh::LeanObject,
    mut v_p_2549_: *mut leanh::LeanObject,
    mut v_occurrence_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2551_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___f_2551_, 0, v_targetName_2548_);
    leanh::lean_closure_set(v___f_2551_, 1, v_occurrence_2550_);
    leanh::lean_closure_set(v___f_2551_, 2, v_p_2549_);
    v___x_2552_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2552_, 0, v___f_2551_);
    leanh::lean_ctor_set_uint8(
        v___x_2552_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_phase_2547_,
    );
    return v___x_2552_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(
    mut v_phase_2553_: *mut leanh::LeanObject,
    mut v_targetName_2554_: *mut leanh::LeanObject,
    mut v_p_2555_: *mut leanh::LeanObject,
    mut v_occurrence_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2557_: u8 = 0;
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2557_ = (leanh::lean_unbox(v_phase_2553_) as u8);
    v_res_2558_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(
        v_phase_boxed_2557_,
        v_targetName_2554_,
        v_p_2555_,
        v_occurrence_2556_,
    );
    return v_res_2558_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(
    mut v_phase_2559_: u8,
    mut v_targetName_2560_: *mut leanh::LeanObject,
    mut v_p_2561_: *mut leanh::LeanObject,
    mut v_x_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(
        v_phase_2559_,
        v_targetName_2560_,
        v_p_2561_,
        v_x_2562_,
    );
    return v___x_2563_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(
    mut v_phase_2564_: *mut leanh::LeanObject,
    mut v_targetName_2565_: *mut leanh::LeanObject,
    mut v_p_2566_: *mut leanh::LeanObject,
    mut v_x_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2568_: u8 = 0;
    let mut v_res_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2568_ = (leanh::lean_unbox(v_phase_2564_) as u8);
    v_res_2569_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(
        v_phase_boxed_2568_,
        v_targetName_2565_,
        v_p_2566_,
        v_x_2567_,
    );
    return v_res_2569_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(
    mut v_phase_2570_: u8,
    mut v_targetName_2571_: *mut leanh::LeanObject,
    mut v_p_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = leanh::lean_box((v_phase_2570_) as usize);
    leanh::lean_inc(v_targetName_2571_);
    v___f_2574_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2574_, 0, v___x_2573_);
    leanh::lean_closure_set(v___f_2574_, 1, v_targetName_2571_);
    leanh::lean_closure_set(v___f_2574_, 2, v_p_2572_);
    v___x_2575_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(
        v_phase_2570_,
        v_targetName_2571_,
        v___f_2574_,
    );
    return v___x_2575_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(
    mut v_phase_2576_: *mut leanh::LeanObject,
    mut v_targetName_2577_: *mut leanh::LeanObject,
    mut v_p_2578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_2579_: u8 = 0;
    let mut v_res_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2579_ = (leanh::lean_unbox(v_phase_2576_) as u8);
    v_res_2580_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(
        v_phase_boxed_2579_,
        v_targetName_2577_,
        v_p_2578_,
    );
    return v_res_2580_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_run(
    mut v_manager_2581_: *mut leanh::LeanObject,
    mut v_installer_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_2586_: u8 = 0;
    let mut v_install_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePasses_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPasses_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPassesNoLambda_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impurePasses_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_a_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_install_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePasses_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPasses_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPassesNoLambda_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impurePasses_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut v_a_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_install_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePasses_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPasses_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monoPassesNoLambda_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impurePasses_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_a_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_isSharedCheck_2673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_phase_2586_ = leanh::lean_ctor_get_uint8(
                    v_installer_2582_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                match v_phase_2586_ {
                    0 => {
                        v_install_2587_ = leanh::lean_ctor_get(v_installer_2582_, 0);
                        leanh::lean_inc_ref(v_install_2587_);
                        leanh::lean_dec_ref(v_installer_2582_);
                        v_basePasses_2588_ = leanh::lean_ctor_get(v_manager_2581_, 0);
                        v_monoPasses_2589_ = leanh::lean_ctor_get(v_manager_2581_, 1);
                        v_monoPassesNoLambda_2590_ =
                            leanh::lean_ctor_get(v_manager_2581_, 2);
                        v_impurePasses_2591_ = leanh::lean_ctor_get(v_manager_2581_, 3);
                        v_isSharedCheck_2615_ =
                            (!leanh::lean_is_exclusive(v_manager_2581_)) as u8;
                        if v_isSharedCheck_2615_ == 0 {
                            v___x_2593_ = v_manager_2581_;
                            v_isShared_2594_ = v_isSharedCheck_2615_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_impurePasses_2591_);
                            leanh::lean_inc(v_monoPassesNoLambda_2590_);
                            leanh::lean_inc(v_monoPasses_2589_);
                            leanh::lean_inc(v_basePasses_2588_);
                            leanh::lean_dec(v_manager_2581_);
                            v___x_2593_ = leanh::lean_box(0);
                            v_isShared_2594_ = v_isSharedCheck_2615_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_install_2616_ = leanh::lean_ctor_get(v_installer_2582_, 0);
                        leanh::lean_inc_ref(v_install_2616_);
                        leanh::lean_dec_ref(v_installer_2582_);
                        v_basePasses_2617_ = leanh::lean_ctor_get(v_manager_2581_, 0);
                        v_monoPasses_2618_ = leanh::lean_ctor_get(v_manager_2581_, 1);
                        v_monoPassesNoLambda_2619_ =
                            leanh::lean_ctor_get(v_manager_2581_, 2);
                        v_impurePasses_2620_ = leanh::lean_ctor_get(v_manager_2581_, 3);
                        v_isSharedCheck_2644_ =
                            (!leanh::lean_is_exclusive(v_manager_2581_)) as u8;
                        if v_isSharedCheck_2644_ == 0 {
                            v___x_2622_ = v_manager_2581_;
                            v_isShared_2623_ = v_isSharedCheck_2644_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_impurePasses_2620_);
                            leanh::lean_inc(v_monoPassesNoLambda_2619_);
                            leanh::lean_inc(v_monoPasses_2618_);
                            leanh::lean_inc(v_basePasses_2617_);
                            leanh::lean_dec(v_manager_2581_);
                            v___x_2622_ = leanh::lean_box(0);
                            v_isShared_2623_ = v_isSharedCheck_2644_;
                            state = 7;
                            continue;
                        }
                    }
                    _ => {
                        v_install_2645_ = leanh::lean_ctor_get(v_installer_2582_, 0);
                        leanh::lean_inc_ref(v_install_2645_);
                        leanh::lean_dec_ref(v_installer_2582_);
                        v_basePasses_2646_ = leanh::lean_ctor_get(v_manager_2581_, 0);
                        v_monoPasses_2647_ = leanh::lean_ctor_get(v_manager_2581_, 1);
                        v_monoPassesNoLambda_2648_ =
                            leanh::lean_ctor_get(v_manager_2581_, 2);
                        v_impurePasses_2649_ = leanh::lean_ctor_get(v_manager_2581_, 3);
                        v_isSharedCheck_2673_ =
                            (!leanh::lean_is_exclusive(v_manager_2581_)) as u8;
                        if v_isSharedCheck_2673_ == 0 {
                            v___x_2651_ = v_manager_2581_;
                            v_isShared_2652_ = v_isSharedCheck_2673_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_impurePasses_2649_);
                            leanh::lean_inc(v_monoPassesNoLambda_2648_);
                            leanh::lean_inc(v_monoPasses_2647_);
                            leanh::lean_inc(v_basePasses_2646_);
                            leanh::lean_dec(v_manager_2581_);
                            v___x_2651_ = leanh::lean_box(0);
                            v_isShared_2652_ = v_isSharedCheck_2673_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_2584_);
                leanh::lean_inc_ref(v_a_2583_);
                v___x_2595_ = leanh::lean_apply_4(
                    v_install_2587_,
                    v_basePasses_2588_,
                    v_a_2583_,
                    v_a_2584_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2595_) == 0 {
                    v_a_2596_ = leanh::lean_ctor_get(v___x_2595_, 0);
                    v_isSharedCheck_2606_ = (!leanh::lean_is_exclusive(v___x_2595_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v___x_2598_ = v___x_2595_;
                        v_isShared_2599_ = v_isSharedCheck_2606_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2596_);
                        leanh::lean_dec(v___x_2595_);
                        v___x_2598_ = leanh::lean_box(0);
                        v_isShared_2599_ = v_isSharedCheck_2606_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2593_);
                    leanh::lean_dec_ref(v_impurePasses_2591_);
                    leanh::lean_dec_ref(v_monoPassesNoLambda_2590_);
                    leanh::lean_dec_ref(v_monoPasses_2589_);
                    v_a_2607_ = leanh::lean_ctor_get(v___x_2595_, 0);
                    v_isSharedCheck_2614_ = (!leanh::lean_is_exclusive(v___x_2595_)) as u8;
                    if v_isSharedCheck_2614_ == 0 {
                        v___x_2609_ = v___x_2595_;
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2607_);
                        leanh::lean_dec(v___x_2595_);
                        v___x_2609_ = leanh::lean_box(0);
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2594_ == 0 {
                    leanh::lean_ctor_set(v___x_2593_, 0, v_a_2596_);
                    v___x_2601_ = v___x_2593_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2596_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_monoPasses_2589_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2605_,
                        2,
                        v_monoPassesNoLambda_2590_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_impurePasses_2591_);
                    v___x_2601_ = v_reuseFailAlloc_2605_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2599_ == 0 {
                    leanh::lean_ctor_set(v___x_2598_, 0, v___x_2601_);
                    v___x_2603_ = v___x_2598_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2603_;
            }
            5 => {
                if v_isShared_2610_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2612_;
            }
            7 => {
                leanh::lean_inc(v_a_2584_);
                leanh::lean_inc_ref(v_a_2583_);
                v___x_2624_ = leanh::lean_apply_4(
                    v_install_2616_,
                    v_monoPasses_2618_,
                    v_a_2583_,
                    v_a_2584_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2624_) == 0 {
                    v_a_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2635_ = (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2627_ = v___x_2624_;
                        v_isShared_2628_ = v_isSharedCheck_2635_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2625_);
                        leanh::lean_dec(v___x_2624_);
                        v___x_2627_ = leanh::lean_box(0);
                        v_isShared_2628_ = v_isSharedCheck_2635_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2622_);
                    leanh::lean_dec_ref(v_impurePasses_2620_);
                    leanh::lean_dec_ref(v_monoPassesNoLambda_2619_);
                    leanh::lean_dec_ref(v_basePasses_2617_);
                    v_a_2636_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2624_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2636_);
                        leanh::lean_dec(v___x_2624_);
                        v___x_2638_ = leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2623_ == 0 {
                    leanh::lean_ctor_set(v___x_2622_, 1, v_a_2625_);
                    v___x_2630_ = v___x_2622_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_basePasses_2617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_a_2625_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2634_,
                        2,
                        v_monoPassesNoLambda_2619_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_impurePasses_2620_);
                    v___x_2630_ = v_reuseFailAlloc_2634_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2628_ == 0 {
                    leanh::lean_ctor_set(v___x_2627_, 0, v___x_2630_);
                    v___x_2632_ = v___x_2627_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2632_;
            }
            11 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2641_;
            }
            13 => {
                leanh::lean_inc(v_a_2584_);
                leanh::lean_inc_ref(v_a_2583_);
                v___x_2653_ = leanh::lean_apply_4(
                    v_install_2645_,
                    v_impurePasses_2649_,
                    v_a_2583_,
                    v_a_2584_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2653_) == 0 {
                    v_a_2654_ = leanh::lean_ctor_get(v___x_2653_, 0);
                    v_isSharedCheck_2664_ = (!leanh::lean_is_exclusive(v___x_2653_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2656_ = v___x_2653_;
                        v_isShared_2657_ = v_isSharedCheck_2664_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2654_);
                        leanh::lean_dec(v___x_2653_);
                        v___x_2656_ = leanh::lean_box(0);
                        v_isShared_2657_ = v_isSharedCheck_2664_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2651_);
                    leanh::lean_dec_ref(v_monoPassesNoLambda_2648_);
                    leanh::lean_dec_ref(v_monoPasses_2647_);
                    leanh::lean_dec_ref(v_basePasses_2646_);
                    v_a_2665_ = leanh::lean_ctor_get(v___x_2653_, 0);
                    v_isSharedCheck_2672_ = (!leanh::lean_is_exclusive(v___x_2653_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2667_ = v___x_2653_;
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2665_);
                        leanh::lean_dec(v___x_2653_);
                        v___x_2667_ = leanh::lean_box(0);
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2652_ == 0 {
                    leanh::lean_ctor_set(v___x_2651_, 3, v_a_2654_);
                    v___x_2659_ = v___x_2651_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2663_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_basePasses_2646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_monoPasses_2647_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2663_,
                        2,
                        v_monoPassesNoLambda_2648_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_a_2654_);
                    v___x_2659_ = v_reuseFailAlloc_2663_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2657_ == 0 {
                    leanh::lean_ctor_set(v___x_2656_, 0, v___x_2659_);
                    v___x_2661_ = v___x_2656_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
                    v___x_2661_ = v_reuseFailAlloc_2662_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2661_;
            }
            17 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_run___boxed(
    mut v_manager_2674_: *mut leanh::LeanObject,
    mut v_installer_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_Compiler_LCNF_PassInstaller_run(
        v_manager_2674_,
        v_installer_2675_,
        v_a_2676_,
        v_a_2677_,
    );
    leanh::lean_dec(v_a_2677_);
    leanh::lean_dec_ref(v_a_2676_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(
    mut v_x_2680_: *mut leanh::LeanObject,
    mut v___y_2681_: *mut leanh::LeanObject,
    mut v___y_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2690_: u8 = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2680_) == 0 {
                    v_a_2684_ = leanh::lean_ctor_get(v_x_2680_, 0);
                    leanh::lean_inc(v_a_2684_);
                    leanh::lean_dec_ref_known(v_x_2680_, 1);
                    v___x_2685_ = l_Lean_stringToMessageData(v_a_2684_);
                    v___x_2686_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_2685_, v___y_2681_, v___y_2682_);
                    return v___x_2686_;
                } else {
                    v_a_2687_ = leanh::lean_ctor_get(v_x_2680_, 0);
                    v_isSharedCheck_2694_ = (!leanh::lean_is_exclusive(v_x_2680_)) as u8;
                    if v_isSharedCheck_2694_ == 0 {
                        v___x_2689_ = v_x_2680_;
                        v_isShared_2690_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2687_);
                        leanh::lean_dec(v_x_2680_);
                        v___x_2689_ = leanh::lean_box(0);
                        v_isShared_2690_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2690_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2689_, 0);
                    v___x_2692_ = v___x_2689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
                    v___x_2692_ = v_reuseFailAlloc_2693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(
    mut v_x_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_2695_, v___y_2696_, v___y_2697_);
    leanh::lean_dec(v___y_2697_);
    leanh::lean_dec_ref(v___y_2696_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(
    mut v_declName_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = lean_st_ref_get(v_a_2710_);
    v_env_2713_ = leanh::lean_ctor_get(v___x_2712_, 0);
    leanh::lean_inc_ref(v_env_2713_);
    leanh::lean_dec(v___x_2712_);
    v_options_2714_ = leanh::lean_ctor_get(v_a_2709_, 2);
    v___x_2715_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3;
    v___x_2716_ = l_Lean_Environment_evalConstCheck___redArg(
        v_env_2713_,
        v_options_2714_,
        v___x_2715_,
        v_declName_2708_,
    );
    v___x_2717_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_2716_, v_a_2709_, v_a_2710_);
    return v___x_2717_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(
    mut v_declName_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
    mut v_a_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_2718_, v_a_2719_, v_a_2720_);
    leanh::lean_dec(v_a_2720_);
    leanh::lean_dec_ref(v_a_2719_);
    return v_res_2722_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(
    mut v_00_u03b1_2723_: *mut leanh::LeanObject,
    mut v_x_2724_: *mut leanh::LeanObject,
    mut v___y_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_2724_, v___y_2725_, v___y_2726_);
    return v___x_2728_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(
    mut v_00_u03b1_2729_: *mut leanh::LeanObject,
    mut v_x_2730_: *mut leanh::LeanObject,
    mut v___y_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_2729_, v_x_2730_, v___y_2731_, v___y_2732_);
    leanh::lean_dec(v___y_2732_);
    leanh::lean_dec_ref(v___y_2731_);
    return v_res_2734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(
    mut v_manager_2735_: *mut leanh::LeanObject,
    mut v_declName_2736_: *mut leanh::LeanObject,
    mut v_a_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2751_: u8 = 0;
    let mut v_unused_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut v_a_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2740_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_2736_, v_a_2737_, v_a_2738_);
                if leanh::lean_obj_tag(v___x_2740_) == 0 {
                    v_a_2741_ = leanh::lean_ctor_get(v___x_2740_, 0);
                    leanh::lean_inc(v_a_2741_);
                    leanh::lean_dec_ref_known(v___x_2740_, 1);
                    v___x_2742_ = l_Lean_Compiler_LCNF_PassInstaller_run(
                        v_manager_2735_,
                        v_a_2741_,
                        v_a_2737_,
                        v_a_2738_,
                    );
                    if leanh::lean_obj_tag(v___x_2742_) == 0 {
                        v_a_2743_ = leanh::lean_ctor_get(v___x_2742_, 0);
                        leanh::lean_inc(v_a_2743_);
                        leanh::lean_dec_ref_known(v___x_2742_, 1);
                        v___x_2744_ = l_Lean_Compiler_LCNF_PassManager_validate(
                            v_a_2743_, v_a_2737_, v_a_2738_,
                        );
                        if leanh::lean_obj_tag(v___x_2744_) == 0 {
                            v_isSharedCheck_2751_ =
                                (!leanh::lean_is_exclusive(v___x_2744_)) as u8;
                            if v_isSharedCheck_2751_ == 0 {
                                v_unused_2752_ = leanh::lean_ctor_get(v___x_2744_, 0);
                                leanh::lean_dec(v_unused_2752_);
                                v___x_2746_ = v___x_2744_;
                                v_isShared_2747_ = v_isSharedCheck_2751_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2744_);
                                v___x_2746_ = leanh::lean_box(0);
                                v_isShared_2747_ = v_isSharedCheck_2751_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2743_);
                            v_a_2753_ = leanh::lean_ctor_get(v___x_2744_, 0);
                            v_isSharedCheck_2760_ =
                                (!leanh::lean_is_exclusive(v___x_2744_)) as u8;
                            if v_isSharedCheck_2760_ == 0 {
                                v___x_2755_ = v___x_2744_;
                                v_isShared_2756_ = v_isSharedCheck_2760_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2753_);
                                leanh::lean_dec(v___x_2744_);
                                v___x_2755_ = leanh::lean_box(0);
                                v_isShared_2756_ = v_isSharedCheck_2760_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2742_;
                    }
                } else {
                    leanh::lean_dec_ref(v_manager_2735_);
                    v_a_2761_ = leanh::lean_ctor_get(v___x_2740_, 0);
                    v_isSharedCheck_2768_ = (!leanh::lean_is_exclusive(v___x_2740_)) as u8;
                    if v_isSharedCheck_2768_ == 0 {
                        v___x_2763_ = v___x_2740_;
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2761_);
                        leanh::lean_dec(v___x_2740_);
                        v___x_2763_ = leanh::lean_box(0);
                        v_isShared_2764_ = v_isSharedCheck_2768_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2747_ == 0 {
                    leanh::lean_ctor_set(v___x_2746_, 0, v_a_2743_);
                    v___x_2749_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2743_);
                    v___x_2749_ = v_reuseFailAlloc_2750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2749_;
            }
            3 => {
                if v_isShared_2756_ == 0 {
                    v___x_2758_ = v___x_2755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
                    v___x_2758_ = v_reuseFailAlloc_2759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2758_;
            }
            5 => {
                if v_isShared_2764_ == 0 {
                    v___x_2766_ = v___x_2763_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
                    v___x_2766_ = v_reuseFailAlloc_2767_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(
    mut v_manager_2769_: *mut leanh::LeanObject,
    mut v_declName_2770_: *mut leanh::LeanObject,
    mut v_a_2771_: *mut leanh::LeanObject,
    mut v_a_2772_: *mut leanh::LeanObject,
    mut v_a_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(
        v_manager_2769_,
        v_declName_2770_,
        v_a_2771_,
        v_a_2772_,
    );
    leanh::lean_dec(v_a_2772_);
    leanh::lean_dec_ref(v_a_2771_);
    return v_res_2774_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PassManager(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instLTPhase = _init_l_Lean_Compiler_LCNF_instLTPhase();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instLTPhase);
    l_Lean_Compiler_LCNF_instLEPhase = _init_l_Lean_Compiler_LCNF_instLEPhase();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instLEPhase);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PassManager(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam =
        _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PassManager(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PassManager(builtin);
}