// Lean compiler output
// Module: Init.Data.Rat.Basic
// Imports: Init.Data.Nat.Coprime Init.Data.OfScientific Init.Data.Int.DivMod.Basic Init.Data.String.Defs Init.Data.ToString.Macro Init.Data.ToString.Extra Init.Data.Hashable Init.Data.Int.DivMod.Bootstrap Init.Data.Int.DivMod.Lemmas Init.Data.Int.Lemmas Init.Data.Int.Order Init.Data.Int.Pow Init.Data.Nat.Dvd
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Bootstrap::{
    initialize_Init_Data_Int_DivMod_Bootstrap, runtime_initialize_Init_Data_Int_DivMod_Bootstrap,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Nat::Coprime::{
    initialize_Init_Data_Nat_Coprime, runtime_initialize_Init_Data_Nat_Coprime,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::OfScientific::{
    initialize_Init_Data_OfScientific, runtime_initialize_Init_Data_OfScientific,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_mkAtom, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_div_exact, lean_int_ediv};
use crate::lean_imports_rs::Init::Data::Nat::Div::Basic::lean_nat_div_exact;
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_div, lean_nat_mul, lean_nat_pow, lean_nat_sub, lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint64, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Rat_den__nz___autoParam___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__2_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__3_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__3_value) as *mut LeanObject;
static l_Rat_den__nz___autoParam___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Rat_den__nz___autoParam___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__4_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Rat_den__nz___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__5_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__6_value: LeanStringObject<19> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__6_value) as *mut LeanObject;
static l_Rat_den__nz___autoParam___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Rat_den__nz___autoParam___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__7_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__7_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Rat_den__nz___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__8_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__9_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__10_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Rat_den__nz___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__10_value) as *mut LeanObject;
static l_Rat_den__nz___autoParam___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__11_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__11_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Rat_den__nz___autoParam___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__11_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__10_value) as *mut LeanObject,
        14249328086033210933 as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__11_value) as *mut LeanObject;
static mut l_Rat_den__nz___autoParam___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Rat_den__nz___autoParam___closed__14_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Rat_den__nz___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__14_value) as *mut LeanObject;
static l_Rat_den__nz___autoParam___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__15_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Rat_den__nz___autoParam___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__15_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Rat_den__nz___autoParam___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__15_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__14_value) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__15_value) as *mut LeanObject;
pub static l_Rat_den__nz___autoParam___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Rat_den__nz___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__16_value) as *mut LeanObject;
static mut l_Rat_den__nz___autoParam___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_den__nz___autoParam___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_den__nz___autoParam___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Rat_den__nz___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Rat_reduced___autoParam: *mut LeanObject = core::ptr::null_mut();
static mut l_instHashableRat_hash___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instHashableRat_hash___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableRat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableRat_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableRat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableRat___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableRat: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableRat___closed__0_value) as *mut LeanObject;
static mut l_instInhabitedRat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedRat___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedRat: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringRat___lam__0___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_instToStringRat___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringRat___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instToStringRat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringRat___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringRat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringRat___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringRat: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringRat___closed__0_value) as *mut LeanObject;
pub static l_instReprRat___lam__0___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_instReprRat___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprRat___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instReprRat___lam__0___closed__1_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [32, 58, 32, 82, 97, 116, 41, 47, 0],
};
static mut l_instReprRat___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instReprRat___lam__0___closed__1_value) as *mut LeanObject;
pub static l_instReprRat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprRat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprRat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprRat___closed__0_value) as *mut LeanObject;
pub static mut l_instReprRat: *mut LeanObject =
    core::ptr::addr_of!(l_instReprRat___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_normalize___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Rat_instNatCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_instNatCast___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instNatCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instNatCast___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instNatCast: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instNatCast___closed__0_value) as *mut LeanObject;
pub static l_Rat_instIntCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_ofInt as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instIntCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instIntCast___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instIntCast: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instIntCast___closed__0_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [82, 97, 116, 0],
};
static mut l_Rat_term___x2f_x2e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__0_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__1_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 101, 114, 109, 95, 47, 46, 95, 0],
};
static mut l_Rat_term___x2f_x2e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__1_value) as *mut LeanObject;
static l_Rat_term___x2f_x2e___00__closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__0_value) as *mut LeanObject,
        3708748166848919527 as *mut LeanObject,
    ],
};
pub static l_Rat_term___x2f_x2e___00__closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__1_value) as *mut LeanObject,
        2580453582700741305 as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__2_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__3_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Rat_term___x2f_x2e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__3_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__4_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 47, 46, 32, 0],
};
static mut l_Rat_term___x2f_x2e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__5_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__5_value) as *mut LeanObject],
};
static mut l_Rat_term___x2f_x2e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__6_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__7_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Rat_term___x2f_x2e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__7_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__7_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__8_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__8_value) as *mut LeanObject,
        (((71 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__9_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__10_value) as *mut LeanObject;
pub static l_Rat_term___x2f_x2e___00__closed__11_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__2_value) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Rat_term___x2f_x2e___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__11_value) as *mut LeanObject;
pub static mut l_Rat_term___x2f_x2e__: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__11_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value) as *mut LeanObject;
static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Rat_den__nz___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [82, 97, 116, 46, 100, 105, 118, 73, 110, 116, 0]};
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3_value) as *mut LeanObject;
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 118, 73, 110, 116, 0]};
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value) as *mut LeanObject;
static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Rat_term___x2f_x2e___00__closed__0_value) as *mut LeanObject,3708748166848919527 as *mut LeanObject] };
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value) as *mut LeanObject,4012841252021137069 as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value) as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value) as *mut LeanObject] };
static mut l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10_value) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value:
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
static mut l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value
) as *mut LeanObject;
pub static l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1_value:
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
            l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value
        ) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1_value
) as *mut LeanObject;
pub static l_Rat_instOfScientific___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_ofScientific___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instOfScientific___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instOfScientific___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instOfScientific: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instOfScientific___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Rat_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Rat_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_instMin___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMin___closed__0_value) as *mut LeanObject;
pub static l_Rat_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_instMax___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMax___closed__0_value) as *mut LeanObject;
pub static l_Rat_instMul___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instMul___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMul___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instMul: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instMul___closed__0_value) as *mut LeanObject;
pub static l_Rat_instInv___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_inv as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instInv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instInv___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instInv: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instInv___closed__0_value) as *mut LeanObject;
pub static l_Rat_instPowNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instPowNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instPowNat___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instPowNat: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instPowNat___closed__0_value) as *mut LeanObject;
pub static l_Rat_instPowInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_zpow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instPowInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instPowInt___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instPowInt: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instPowInt___closed__0_value) as *mut LeanObject;
pub static l_Rat_instDiv___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instDiv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instDiv___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instDiv: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instDiv___closed__0_value) as *mut LeanObject;
pub static l_Rat_instAdd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_add as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instAdd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instAdd___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instAdd: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instAdd___closed__0_value) as *mut LeanObject;
pub static l_Rat_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_neg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instNeg___closed__0_value) as *mut LeanObject;
pub static l_Rat_instSub___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_sub as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Rat_instSub___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instSub___closed__0_value) as *mut LeanObject;
pub static mut l_Rat_instSub: *mut LeanObject =
    core::ptr::addr_of!(l_Rat_instSub___closed__0_value) as *mut LeanObject;
static mut l_Rat_ceil___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_ceil___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Rat_abs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Rat_abs___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__12() -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Rat_den__nz___autoParam___closed__10;
    v___x_753_ = l_Lean_mkAtom(v___x_752_);
    return v___x_753_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__13() -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__12_once),
        _init_l_Rat_den__nz___autoParam___closed__12,
    );
    v___x_755_ = l_Rat_den__nz___autoParam___closed__5;
    v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__17() -> *mut LeanObject {
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v___x_767_ = l_Rat_den__nz___autoParam___closed__16;
    v___x_768_ = l_Rat_den__nz___autoParam___closed__5;
    v___x_769_ = lean_array_push(v___x_768_, v___x_767_);
    return v___x_769_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__18() -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__17_once),
        _init_l_Rat_den__nz___autoParam___closed__17,
    );
    v___x_771_ = l_Rat_den__nz___autoParam___closed__15;
    v___x_772_ = lean_box(2);
    v___x_773_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_773_, 0, v___x_772_);
    lean_ctor_set(v___x_773_, 1, v___x_771_);
    lean_ctor_set(v___x_773_, 2, v___x_770_);
    return v___x_773_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__19() -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__18_once),
        _init_l_Rat_den__nz___autoParam___closed__18,
    );
    v___x_775_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__13_once),
        _init_l_Rat_den__nz___autoParam___closed__13,
    );
    v___x_776_ = lean_array_push(v___x_775_, v___x_774_);
    return v___x_776_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__20() -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__19_once),
        _init_l_Rat_den__nz___autoParam___closed__19,
    );
    v___x_778_ = l_Rat_den__nz___autoParam___closed__11;
    v___x_779_ = lean_box(2);
    v___x_780_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_780_, 0, v___x_779_);
    lean_ctor_set(v___x_780_, 1, v___x_778_);
    lean_ctor_set(v___x_780_, 2, v___x_777_);
    return v___x_780_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__21() -> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    v___x_781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__20_once),
        _init_l_Rat_den__nz___autoParam___closed__20,
    );
    v___x_782_ = l_Rat_den__nz___autoParam___closed__5;
    v___x_783_ = lean_array_push(v___x_782_, v___x_781_);
    return v___x_783_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__22() -> *mut LeanObject {
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    v___x_784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__21_once),
        _init_l_Rat_den__nz___autoParam___closed__21,
    );
    v___x_785_ = l_Rat_den__nz___autoParam___closed__9;
    v___x_786_ = lean_box(2);
    v___x_787_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_787_, 0, v___x_786_);
    lean_ctor_set(v___x_787_, 1, v___x_785_);
    lean_ctor_set(v___x_787_, 2, v___x_784_);
    return v___x_787_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__23() -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__22_once),
        _init_l_Rat_den__nz___autoParam___closed__22,
    );
    v___x_789_ = l_Rat_den__nz___autoParam___closed__5;
    v___x_790_ = lean_array_push(v___x_789_, v___x_788_);
    return v___x_790_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__24() -> *mut LeanObject {
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    v___x_791_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__23_once),
        _init_l_Rat_den__nz___autoParam___closed__23,
    );
    v___x_792_ = l_Rat_den__nz___autoParam___closed__7;
    v___x_793_ = lean_box(2);
    v___x_794_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_794_, 0, v___x_793_);
    lean_ctor_set(v___x_794_, 1, v___x_792_);
    lean_ctor_set(v___x_794_, 2, v___x_791_);
    return v___x_794_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__25() -> *mut LeanObject {
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_795_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__24_once),
        _init_l_Rat_den__nz___autoParam___closed__24,
    );
    v___x_796_ = l_Rat_den__nz___autoParam___closed__5;
    v___x_797_ = lean_array_push(v___x_796_, v___x_795_);
    return v___x_797_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam___closed__26() -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__25_once),
        _init_l_Rat_den__nz___autoParam___closed__25,
    );
    v___x_799_ = l_Rat_den__nz___autoParam___closed__4;
    v___x_800_ = lean_box(2);
    v___x_801_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_801_, 0, v___x_800_);
    lean_ctor_set(v___x_801_, 1, v___x_799_);
    lean_ctor_set(v___x_801_, 2, v___x_798_);
    return v___x_801_;
}
pub unsafe fn _init_l_Rat_den__nz___autoParam() -> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26_once),
        _init_l_Rat_den__nz___autoParam___closed__26,
    );
    return v___x_802_;
}
pub unsafe fn _init_l_Rat_reduced___autoParam() -> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26_once),
        _init_l_Rat_den__nz___autoParam___closed__26,
    );
    return v___x_803_;
}
pub unsafe fn l_instDecidableEqRat_decEq(
    mut v_x_804_: *mut LeanObject,
    mut v_x_805_: *mut LeanObject,
) -> u8 {
    let mut v_num_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    v_num_806_ = lean_ctor_get(v_x_804_, 0);
    v_den_807_ = lean_ctor_get(v_x_804_, 1);
    v_num_808_ = lean_ctor_get(v_x_805_, 0);
    v_den_809_ = lean_ctor_get(v_x_805_, 1);
    v___x_810_ = lean_int_dec_eq(v_num_806_, v_num_808_);
    if v___x_810_ == 0 {
        return v___x_810_;
    } else {
        let mut v___x_811_: u8 = 0;
        v___x_811_ = lean_nat_dec_eq(v_den_807_, v_den_809_);
        return v___x_811_;
    }
}
pub unsafe fn l_instDecidableEqRat_decEq___boxed(
    mut v_x_812_: *mut LeanObject,
    mut v_x_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_814_: u8 = 0;
    let mut v_r_815_: *mut LeanObject = core::ptr::null_mut();
    v_res_814_ = l_instDecidableEqRat_decEq(v_x_812_, v_x_813_);
    lean_dec_ref(v_x_813_);
    lean_dec_ref(v_x_812_);
    v_r_815_ = lean_box((v_res_814_) as usize);
    return v_r_815_;
}
pub unsafe fn l_instDecidableEqRat(
    mut v_x_816_: *mut LeanObject,
    mut v_x_817_: *mut LeanObject,
) -> u8 {
    let mut v___x_818_: u8 = 0;
    v___x_818_ = l_instDecidableEqRat_decEq(v_x_816_, v_x_817_);
    return v___x_818_;
}
pub unsafe fn l_instDecidableEqRat___boxed(
    mut v_x_819_: *mut LeanObject,
    mut v_x_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_821_: u8 = 0;
    let mut v_r_822_: *mut LeanObject = core::ptr::null_mut();
    v_res_821_ = l_instDecidableEqRat(v_x_819_, v_x_820_);
    lean_dec_ref(v_x_820_);
    lean_dec_ref(v_x_819_);
    v_r_822_ = lean_box((v_res_821_) as usize);
    return v_r_822_;
}
pub unsafe fn _init_l_instHashableRat_hash___closed__0() -> *mut LeanObject {
    let mut v_natZero_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_824_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_823_ = lean_unsigned_to_nat(0);
    v_intZero_824_ = lean_nat_to_int(v_natZero_823_);
    return v_intZero_824_;
}
pub unsafe fn l_instHashableRat_hash(mut v_x_825_: *mut LeanObject) -> u64 {
    let mut v_num_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u64 = 0;
    let mut v___y_830_: u64 = 0;
    let mut v___x_831_: u64 = 0;
    let mut v___x_832_: u64 = 0;
    let mut v___x_833_: u64 = 0;
    let mut v___x_834_: u64 = 0;
    let mut v___x_835_: u64 = 0;
    let mut v_intZero_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_837_: u8 = 0;
    let mut v_a_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u64 = 0;
    let mut v_abs_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_826_ = lean_ctor_get(v_x_825_, 0);
                v_den_827_ = lean_ctor_get(v_x_825_, 1);
                v___x_828_ = 0u64;
                v_intZero_836_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
                    _init_l_instHashableRat_hash___closed__0,
                );
                v_isNeg_837_ = lean_int_dec_lt(v_num_826_, v_intZero_836_);
                if v_isNeg_837_ == 0 {
                    v_a_838_ = lean_nat_abs(v_num_826_);
                    v___x_839_ = lean_unsigned_to_nat(2);
                    v___x_840_ = lean_nat_mul(v___x_839_, v_a_838_);
                    lean_dec(v_a_838_);
                    v___x_841_ = lean_uint64_of_nat(v___x_840_);
                    lean_dec(v___x_840_);
                    v___y_830_ = v___x_841_;
                    state = 1;
                    continue;
                } else {
                    v_abs_842_ = lean_nat_abs(v_num_826_);
                    v_one_843_ = lean_unsigned_to_nat(1);
                    v_a_844_ = lean_nat_sub(v_abs_842_, v_one_843_);
                    lean_dec(v_abs_842_);
                    v___x_845_ = lean_unsigned_to_nat(2);
                    v___x_846_ = lean_nat_mul(v___x_845_, v_a_844_);
                    lean_dec(v_a_844_);
                    v___x_847_ = lean_nat_add(v___x_846_, v_one_843_);
                    lean_dec(v___x_846_);
                    v___x_848_ = lean_uint64_of_nat(v___x_847_);
                    lean_dec(v___x_847_);
                    v___y_830_ = v___x_848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_831_ = lean_uint64_mix_hash(v___x_828_, v___y_830_);
                v___x_832_ = lean_uint64_of_nat(v_den_827_);
                v___x_833_ = lean_uint64_mix_hash(v___x_831_, v___x_832_);
                v___x_834_ = lean_uint64_mix_hash(v___x_833_, v___x_828_);
                v___x_835_ = lean_uint64_mix_hash(v___x_834_, v___x_828_);
                return v___x_835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instHashableRat_hash___boxed(mut v_x_849_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_850_: u64 = 0;
    let mut v_r_851_: *mut LeanObject = core::ptr::null_mut();
    v_res_850_ = l_instHashableRat_hash(v_x_849_);
    lean_dec_ref(v_x_849_);
    v_r_851_ = lean_box_uint64(v_res_850_);
    return v_r_851_;
}
pub unsafe fn _init_l_instInhabitedRat___closed__0() -> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = lean_unsigned_to_nat(1);
    v___x_855_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
        _init_l_instHashableRat_hash___closed__0,
    );
    v___x_856_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_856_, 0, v___x_855_);
    lean_ctor_set(v___x_856_, 1, v___x_854_);
    return v___x_856_;
}
pub unsafe fn _init_l_instInhabitedRat() -> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0_once),
        _init_l_instInhabitedRat___closed__0,
    );
    return v___x_857_;
}
pub unsafe fn l_instToStringRat___lam__0(mut v_a_859_: *mut LeanObject) -> *mut LeanObject {
    let mut v_num_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    v_num_860_ = lean_ctor_get(v_a_859_, 0);
    lean_inc(v_num_860_);
    v_den_861_ = lean_ctor_get(v_a_859_, 1);
    lean_inc(v_den_861_);
    lean_dec_ref(v_a_859_);
    v___x_862_ = lean_unsigned_to_nat(1);
    v___x_863_ = lean_nat_dec_eq(v_den_861_, v___x_862_);
    if v___x_863_ == 0 {
        let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
        v___x_864_ = l_Int_repr(v_num_860_);
        lean_dec(v_num_860_);
        v___x_865_ = l_instToStringRat___lam__0___closed__0;
        v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
        v___x_867_ = l_Nat_reprFast(v_den_861_);
        v___x_868_ = lean_string_append(v___x_866_, v___x_867_);
        lean_dec_ref(v___x_867_);
        return v___x_868_;
    } else {
        let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_den_861_);
        v___x_869_ = l_Int_repr(v_num_860_);
        lean_dec(v_num_860_);
        return v___x_869_;
    }
}
pub unsafe fn l_instReprRat___lam__0(
    mut v_a_874_: *mut LeanObject,
    mut v_x_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    v_num_876_ = lean_ctor_get(v_a_874_, 0);
    lean_inc(v_num_876_);
    v_den_877_ = lean_ctor_get(v_a_874_, 1);
    lean_inc(v_den_877_);
    lean_dec_ref(v_a_874_);
    v___x_878_ = lean_unsigned_to_nat(1);
    v___x_879_ = lean_nat_dec_eq(v_den_877_, v___x_878_);
    if v___x_879_ == 0 {
        let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
        v___x_880_ = l_instReprRat___lam__0___closed__0;
        v___x_881_ = l_Int_repr(v_num_876_);
        lean_dec(v_num_876_);
        v___x_882_ = lean_string_append(v___x_880_, v___x_881_);
        lean_dec_ref(v___x_881_);
        v___x_883_ = l_instReprRat___lam__0___closed__1;
        v___x_884_ = lean_string_append(v___x_882_, v___x_883_);
        v___x_885_ = l_Nat_reprFast(v_den_877_);
        v___x_886_ = lean_string_append(v___x_884_, v___x_885_);
        lean_dec_ref(v___x_885_);
        v___x_887_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_887_, 0, v___x_886_);
        return v___x_887_;
    } else {
        let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_890_: u8 = 0;
        lean_dec(v_den_877_);
        v___x_888_ = lean_unsigned_to_nat(0);
        v___x_889_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
            core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
            _init_l_instHashableRat_hash___closed__0,
        );
        v___x_890_ = lean_int_dec_lt(v_num_876_, v___x_889_);
        if v___x_890_ == 0 {
            let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
            v___x_891_ = l_Int_repr(v_num_876_);
            lean_dec(v_num_876_);
            v___x_892_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_892_, 0, v___x_891_);
            return v___x_892_;
        } else {
            let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
            v___x_893_ = l_Int_repr(v_num_876_);
            lean_dec(v_num_876_);
            v___x_894_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_894_, 0, v___x_893_);
            v___x_895_ = l_Repr_addAppParen(v___x_894_, v___x_888_);
            return v___x_895_;
        }
    }
}
pub unsafe fn l_instReprRat___lam__0___boxed(
    mut v_a_896_: *mut LeanObject,
    mut v_x_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_898_: *mut LeanObject = core::ptr::null_mut();
    v_res_898_ = l_instReprRat___lam__0(v_a_896_, v_x_897_);
    lean_dec(v_x_897_);
    return v_res_898_;
}
pub unsafe fn l_Rat_maybeNormalize___redArg(
    mut v_num_901_: *mut LeanObject,
    mut v_den_902_: *mut LeanObject,
    mut v_g_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    v___x_904_ = lean_unsigned_to_nat(1);
    v___x_905_ = lean_nat_dec_eq(v_g_903_, v___x_904_);
    if v___x_905_ == 0 {
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_g_903_);
        v___x_906_ = lean_nat_to_int(v_g_903_);
        v___x_907_ = lean_int_div_exact(v_num_901_, v___x_906_);
        lean_dec(v___x_906_);
        lean_dec(v_num_901_);
        v___x_908_ = lean_nat_div_exact(v_den_902_, v_g_903_);
        lean_dec(v_g_903_);
        lean_dec(v_den_902_);
        v___x_909_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_909_, 0, v___x_907_);
        lean_ctor_set(v___x_909_, 1, v___x_908_);
        return v___x_909_;
    } else {
        let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_g_903_);
        v___x_910_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_910_, 0, v_num_901_);
        lean_ctor_set(v___x_910_, 1, v_den_902_);
        return v___x_910_;
    }
}
pub unsafe fn l_Rat_maybeNormalize(
    mut v_num_911_: *mut LeanObject,
    mut v_den_912_: *mut LeanObject,
    mut v_g_913_: *mut LeanObject,
    mut v_dvd__num_914_: *mut LeanObject,
    mut v_dvd__den_915_: *mut LeanObject,
    mut v_den__nz_916_: *mut LeanObject,
    mut v_reduced_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    v___x_918_ = lean_unsigned_to_nat(1);
    v___x_919_ = lean_nat_dec_eq(v_g_913_, v___x_918_);
    if v___x_919_ == 0 {
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_g_913_);
        v___x_920_ = lean_nat_to_int(v_g_913_);
        v___x_921_ = lean_int_div_exact(v_num_911_, v___x_920_);
        lean_dec(v___x_920_);
        lean_dec(v_num_911_);
        v___x_922_ = lean_nat_div_exact(v_den_912_, v_g_913_);
        lean_dec(v_g_913_);
        lean_dec(v_den_912_);
        v___x_923_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_923_, 0, v___x_921_);
        lean_ctor_set(v___x_923_, 1, v___x_922_);
        return v___x_923_;
    } else {
        let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_g_913_);
        v___x_924_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_924_, 0, v_num_911_);
        lean_ctor_set(v___x_924_, 1, v_den_912_);
        return v___x_924_;
    }
}
pub unsafe fn _init_l_Rat_normalize___auto__1() -> *mut LeanObject {
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v___x_925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Rat_den__nz___autoParam___closed__26_once),
        _init_l_Rat_den__nz___autoParam___closed__26,
    );
    return v___x_925_;
}
pub unsafe fn l_Rat_normalize___redArg(
    mut v_num_926_: *mut LeanObject,
    mut v_den_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    v___x_928_ = lean_nat_abs(v_num_926_);
    v___x_929_ = lean_nat_gcd(v___x_928_, v_den_927_);
    lean_dec(v___x_928_);
    v___x_930_ = lean_unsigned_to_nat(1);
    v___x_931_ = lean_nat_dec_eq(v___x_929_, v___x_930_);
    if v___x_931_ == 0 {
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___x_929_);
        v___x_932_ = lean_nat_to_int(v___x_929_);
        v___x_933_ = lean_int_div_exact(v_num_926_, v___x_932_);
        lean_dec(v___x_932_);
        lean_dec(v_num_926_);
        v___x_934_ = lean_nat_div_exact(v_den_927_, v___x_929_);
        lean_dec(v___x_929_);
        lean_dec(v_den_927_);
        v___x_935_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_935_, 0, v___x_933_);
        lean_ctor_set(v___x_935_, 1, v___x_934_);
        return v___x_935_;
    } else {
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_929_);
        v___x_936_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_936_, 0, v_num_926_);
        lean_ctor_set(v___x_936_, 1, v_den_927_);
        return v___x_936_;
    }
}
pub unsafe fn l_Rat_normalize(
    mut v_num_937_: *mut LeanObject,
    mut v_den_938_: *mut LeanObject,
    mut v_den__nz_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    v___x_940_ = lean_nat_abs(v_num_937_);
    v___x_941_ = lean_nat_gcd(v___x_940_, v_den_938_);
    lean_dec(v___x_940_);
    v___x_942_ = lean_unsigned_to_nat(1);
    v___x_943_ = lean_nat_dec_eq(v___x_941_, v___x_942_);
    if v___x_943_ == 0 {
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___x_941_);
        v___x_944_ = lean_nat_to_int(v___x_941_);
        v___x_945_ = lean_int_div_exact(v_num_937_, v___x_944_);
        lean_dec(v___x_944_);
        lean_dec(v_num_937_);
        v___x_946_ = lean_nat_div_exact(v_den_938_, v___x_941_);
        lean_dec(v___x_941_);
        lean_dec(v_den_938_);
        v___x_947_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_947_, 0, v___x_945_);
        lean_ctor_set(v___x_947_, 1, v___x_946_);
        return v___x_947_;
    } else {
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_941_);
        v___x_948_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_948_, 0, v_num_937_);
        lean_ctor_set(v___x_948_, 1, v_den_938_);
        return v___x_948_;
    }
}
pub unsafe fn l_Nat_cast___at___00mkRat_spec__0(mut v_a_949_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_950_ = lean_nat_to_int(v_a_949_);
    return v___x_950_;
}
pub unsafe fn l_mkRat(
    mut v_num_951_: *mut LeanObject,
    mut v_den_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    v___x_953_ = lean_unsigned_to_nat(0);
    v___x_954_ = lean_nat_dec_eq(v_den_952_, v___x_953_);
    if v___x_954_ == 0 {
        let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_958_: u8 = 0;
        v___x_955_ = lean_nat_abs(v_num_951_);
        v___x_956_ = lean_nat_gcd(v___x_955_, v_den_952_);
        lean_dec(v___x_955_);
        v___x_957_ = lean_unsigned_to_nat(1);
        v___x_958_ = lean_nat_dec_eq(v___x_956_, v___x_957_);
        if v___x_958_ == 0 {
            let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v___x_956_);
            v___x_959_ = lean_nat_to_int(v___x_956_);
            v___x_960_ = lean_int_div_exact(v_num_951_, v___x_959_);
            lean_dec(v___x_959_);
            lean_dec(v_num_951_);
            v___x_961_ = lean_nat_div_exact(v_den_952_, v___x_956_);
            lean_dec(v___x_956_);
            lean_dec(v_den_952_);
            v___x_962_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_962_, 0, v___x_960_);
            lean_ctor_set(v___x_962_, 1, v___x_961_);
            return v___x_962_;
        } else {
            let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_956_);
            v___x_963_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_963_, 0, v_num_951_);
            lean_ctor_set(v___x_963_, 1, v_den_952_);
            return v___x_963_;
        }
    } else {
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_den_952_);
        lean_dec(v_num_951_);
        v___x_964_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0),
            core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0_once),
            _init_l_instInhabitedRat___closed__0,
        );
        return v___x_964_;
    }
}
pub unsafe fn l_Rat_ofInt(mut v_num_965_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_966_ = lean_unsigned_to_nat(1);
    v___x_967_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_967_, 0, v_num_965_);
    lean_ctor_set(v___x_967_, 1, v___x_966_);
    return v___x_967_;
}
pub unsafe fn l_Rat_instNatCast___lam__0(mut v_n_968_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_969_ = lean_nat_to_int(v_n_968_);
    v___x_970_ = l_Rat_ofInt(v___x_969_);
    return v___x_970_;
}
pub unsafe fn l_Rat_instOfNat(mut v_n_975_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Rat_instNatCast___lam__0(v_n_975_);
    return v___x_976_;
}
pub unsafe fn l_Rat_isInt(mut v_a_977_: *mut LeanObject) -> u8 {
    let mut v_den_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    v_den_978_ = lean_ctor_get(v_a_977_, 1);
    v___x_979_ = lean_unsigned_to_nat(1);
    v___x_980_ = lean_nat_dec_eq(v_den_978_, v___x_979_);
    return v___x_980_;
}
pub unsafe fn l_Rat_isInt___boxed(mut v_a_981_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_982_: u8 = 0;
    let mut v_r_983_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Rat_isInt(v_a_981_);
    lean_dec_ref(v_a_981_);
    v_r_983_ = lean_box((v_res_982_) as usize);
    return v_r_983_;
}
pub unsafe fn l_Rat_divInt(
    mut v_x_984_: *mut LeanObject,
    mut v_x_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_988_: u8 = 0;
    v_natZero_986_ = lean_unsigned_to_nat(0);
    v_intZero_987_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
        _init_l_instHashableRat_hash___closed__0,
    );
    v_isNeg_988_ = lean_int_dec_lt(v_x_985_, v_intZero_987_);
    if v_isNeg_988_ == 0 {
        let mut v_a_989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_990_: u8 = 0;
        v_a_989_ = lean_nat_abs(v_x_985_);
        v___x_990_ = lean_nat_dec_eq(v_a_989_, v_natZero_986_);
        if v___x_990_ == 0 {
            let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_994_: u8 = 0;
            v___x_991_ = lean_nat_abs(v_x_984_);
            v___x_992_ = lean_nat_gcd(v___x_991_, v_a_989_);
            lean_dec(v___x_991_);
            v___x_993_ = lean_unsigned_to_nat(1);
            v___x_994_ = lean_nat_dec_eq(v___x_992_, v___x_993_);
            if v___x_994_ == 0 {
                let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v___x_992_);
                v___x_995_ = lean_nat_to_int(v___x_992_);
                v___x_996_ = lean_int_div_exact(v_x_984_, v___x_995_);
                lean_dec(v___x_995_);
                lean_dec(v_x_984_);
                v___x_997_ = lean_nat_div_exact(v_a_989_, v___x_992_);
                lean_dec(v___x_992_);
                lean_dec(v_a_989_);
                v___x_998_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_998_, 0, v___x_996_);
                lean_ctor_set(v___x_998_, 1, v___x_997_);
                return v___x_998_;
            } else {
                let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_992_);
                v___x_999_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_999_, 0, v_x_984_);
                lean_ctor_set(v___x_999_, 1, v_a_989_);
                return v___x_999_;
            }
        } else {
            let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_989_);
            lean_dec(v_x_984_);
            v___x_1000_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0),
                core::ptr::addr_of_mut!(l_instInhabitedRat___closed__0_once),
                _init_l_instInhabitedRat___closed__0,
            );
            return v___x_1000_;
        }
    } else {
        let mut v_abs_1001_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1002_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_abs_1001_ = lean_nat_abs(v_x_985_);
        v_one_1002_ = lean_unsigned_to_nat(1);
        v_a_1003_ = lean_nat_sub(v_abs_1001_, v_one_1002_);
        lean_dec(v_abs_1001_);
        v___x_1004_ = lean_int_neg(v_x_984_);
        lean_dec(v_x_984_);
        v___x_1005_ = lean_nat_add(v_a_1003_, v_one_1002_);
        lean_dec(v_a_1003_);
        v___x_1006_ = lean_nat_abs(v___x_1004_);
        v___x_1007_ = lean_nat_gcd(v___x_1006_, v___x_1005_);
        lean_dec(v___x_1006_);
        v___x_1008_ = lean_nat_dec_eq(v___x_1007_, v_one_1002_);
        if v___x_1008_ == 0 {
            let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v___x_1007_);
            v___x_1009_ = lean_nat_to_int(v___x_1007_);
            v___x_1010_ = lean_int_div_exact(v___x_1004_, v___x_1009_);
            lean_dec(v___x_1009_);
            lean_dec(v___x_1004_);
            v___x_1011_ = lean_nat_div_exact(v___x_1005_, v___x_1007_);
            lean_dec(v___x_1007_);
            lean_dec(v___x_1005_);
            v___x_1012_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1012_, 0, v___x_1010_);
            lean_ctor_set(v___x_1012_, 1, v___x_1011_);
            return v___x_1012_;
        } else {
            let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1007_);
            v___x_1013_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1013_, 0, v___x_1004_);
            lean_ctor_set(v___x_1013_, 1, v___x_1005_);
            return v___x_1013_;
        }
    }
}
pub unsafe fn l_Rat_divInt___boxed(
    mut v_x_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1016_: *mut LeanObject = core::ptr::null_mut();
    v_res_1016_ = l_Rat_divInt(v_x_1014_, v_x_1015_);
    lean_dec(v_x_1015_);
    return v_res_1016_;
}
pub unsafe fn _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4()
-> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ =
        l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3;
    v___x_1052_ = l_String_toRawSubstring_x27(v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(
    mut v_x_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: u8 = 0;
    v___x_1071_ = l_Rat_term___x2f_x2e___00__closed__2;
    lean_inc(v_x_1068_);
    v___x_1072_ = l_Lean_Syntax_isOfKind(v_x_1068_, v___x_1071_);
    if v___x_1072_ == 0 {
        let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1068_);
        v___x_1073_ = lean_box(1);
        v___x_1074_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1074_, 0, v___x_1073_);
        lean_ctor_set(v___x_1074_, 1, v_a_1070_);
        return v___x_1074_;
    } else {
        let mut v_quotContext_1075_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1076_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: u8 = 0;
        let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1075_ = lean_ctor_get(v_a_1069_, 1);
        v_currMacroScope_1076_ = lean_ctor_get(v_a_1069_, 2);
        v_ref_1077_ = lean_ctor_get(v_a_1069_, 5);
        v___x_1078_ = lean_unsigned_to_nat(0);
        v___x_1079_ = l_Lean_Syntax_getArg(v_x_1068_, v___x_1078_);
        v___x_1080_ = lean_unsigned_to_nat(2);
        v___x_1081_ = l_Lean_Syntax_getArg(v_x_1068_, v___x_1080_);
        lean_dec(v_x_1068_);
        v___x_1082_ = 0;
        v___x_1083_ = l_Lean_SourceInfo_fromRef(v_ref_1077_, v___x_1082_);
        v___x_1084_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2;
        v___x_1085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4), core::ptr::addr_of_mut!(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once), _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4);
        v___x_1086_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6;
        lean_inc(v_currMacroScope_1076_);
        lean_inc(v_quotContext_1075_);
        v___x_1087_ =
            l_Lean_addMacroScope(v_quotContext_1075_, v___x_1086_, v_currMacroScope_1076_);
        v___x_1088_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10;
        lean_inc_n(v___x_1083_, 2);
        v___x_1089_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1089_, 0, v___x_1083_);
        lean_ctor_set(v___x_1089_, 1, v___x_1085_);
        lean_ctor_set(v___x_1089_, 2, v___x_1087_);
        lean_ctor_set(v___x_1089_, 3, v___x_1088_);
        v___x_1090_ = l_Rat_den__nz___autoParam___closed__9;
        v___x_1091_ = l_Lean_Syntax_node2(v___x_1083_, v___x_1090_, v___x_1079_, v___x_1081_);
        v___x_1092_ = l_Lean_Syntax_node2(v___x_1083_, v___x_1084_, v___x_1089_, v___x_1091_);
        v___x_1093_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1093_, 0, v___x_1092_);
        lean_ctor_set(v___x_1093_, 1, v_a_1070_);
        return v___x_1093_;
    }
}
pub unsafe fn l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___boxed(
    mut v_x_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
    mut v_a_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1097_: *mut LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(
        v_x_1094_, v_a_1095_, v_a_1096_,
    );
    lean_dec_ref(v_a_1095_);
    return v_res_1097_;
}
pub unsafe fn l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(
    mut v_x_1101_: *mut LeanObject,
    mut v_a_1102_: *mut LeanObject,
    mut v_a_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    v___x_1104_ =
        l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2;
    lean_inc(v_x_1101_);
    v___x_1105_ = l_Lean_Syntax_isOfKind(v_x_1101_, v___x_1104_);
    if v___x_1105_ == 0 {
        let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1101_);
        v___x_1106_ = lean_box(0);
        v___x_1107_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1107_, 0, v___x_1106_);
        lean_ctor_set(v___x_1107_, 1, v_a_1103_);
        return v___x_1107_;
    } else {
        let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1111_: u8 = 0;
        v___x_1108_ = lean_unsigned_to_nat(0);
        v___x_1109_ = l_Lean_Syntax_getArg(v_x_1101_, v___x_1108_);
        v___x_1110_ = l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1;
        lean_inc(v___x_1109_);
        v___x_1111_ = l_Lean_Syntax_isOfKind(v___x_1109_, v___x_1110_);
        if v___x_1111_ == 0 {
            let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1109_);
            lean_dec(v_x_1101_);
            v___x_1112_ = lean_box(0);
            v___x_1113_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1113_, 0, v___x_1112_);
            lean_ctor_set(v___x_1113_, 1, v_a_1103_);
            return v___x_1113_;
        } else {
            let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: u8 = 0;
            v___x_1114_ = lean_unsigned_to_nat(1);
            v___x_1115_ = l_Lean_Syntax_getArg(v_x_1101_, v___x_1114_);
            lean_dec(v_x_1101_);
            v___x_1116_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1115_);
            v___x_1117_ = l_Lean_Syntax_matchesNull(v___x_1115_, v___x_1116_);
            if v___x_1117_ == 0 {
                let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1115_);
                lean_dec(v___x_1109_);
                v___x_1118_ = lean_box(0);
                v___x_1119_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1119_, 0, v___x_1118_);
                lean_ctor_set(v___x_1119_, 1, v_a_1103_);
                return v___x_1119_;
            } else {
                let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1122_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1123_: u8 = 0;
                let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
                v___x_1120_ = l_Lean_Syntax_getArg(v___x_1115_, v___x_1108_);
                v___x_1121_ = l_Lean_Syntax_getArg(v___x_1115_, v___x_1114_);
                lean_dec(v___x_1115_);
                v_ref_1122_ = l_Lean_replaceRef(v___x_1109_, v_a_1102_);
                lean_dec(v___x_1109_);
                v___x_1123_ = 0;
                v___x_1124_ = l_Lean_SourceInfo_fromRef(v_ref_1122_, v___x_1123_);
                lean_dec(v_ref_1122_);
                v___x_1125_ = l_Rat_term___x2f_x2e___00__closed__2;
                v___x_1126_ = l_Rat_term___x2f_x2e___00__closed__5;
                lean_inc(v___x_1124_);
                v___x_1127_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1127_, 0, v___x_1124_);
                lean_ctor_set(v___x_1127_, 1, v___x_1126_);
                v___x_1128_ = l_Lean_Syntax_node3(
                    v___x_1124_,
                    v___x_1125_,
                    v___x_1120_,
                    v___x_1127_,
                    v___x_1121_,
                );
                v___x_1129_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1129_, 0, v___x_1128_);
                lean_ctor_set(v___x_1129_, 1, v_a_1103_);
                return v___x_1129_;
            }
        }
    }
}
pub unsafe fn l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___boxed(
    mut v_x_1130_: *mut LeanObject,
    mut v_a_1131_: *mut LeanObject,
    mut v_a_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1133_: *mut LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(
        v_x_1130_, v_a_1131_, v_a_1132_,
    );
    lean_dec(v_a_1131_);
    return v_res_1133_;
}
pub unsafe fn l_Nat_cast___at___00Rat_ofScientific_spec__0(
    mut v_a_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = lean_nat_to_int(v_a_1134_);
    v___x_1136_ = l_Rat_ofInt(v___x_1135_);
    return v___x_1136_;
}
pub unsafe fn l_Rat_ofScientific(
    mut v_m_1137_: *mut LeanObject,
    mut v_s_1138_: u8,
    mut v_e_1139_: *mut LeanObject,
) -> *mut LeanObject {
    if v_s_1138_ == 0 {
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
        v___x_1140_ = lean_unsigned_to_nat(10);
        v___x_1141_ = lean_nat_pow(v___x_1140_, v_e_1139_);
        v___x_1142_ = lean_nat_mul(v_m_1137_, v___x_1141_);
        lean_dec(v___x_1141_);
        lean_dec(v_m_1137_);
        v___x_1143_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_1142_);
        return v___x_1143_;
    } else {
        let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: u8 = 0;
        v___x_1144_ = lean_nat_to_int(v_m_1137_);
        v___x_1145_ = lean_unsigned_to_nat(10);
        v___x_1146_ = lean_nat_pow(v___x_1145_, v_e_1139_);
        v___x_1147_ = lean_nat_abs(v___x_1144_);
        v___x_1148_ = lean_nat_gcd(v___x_1147_, v___x_1146_);
        lean_dec(v___x_1147_);
        v___x_1149_ = lean_unsigned_to_nat(1);
        v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
        if v___x_1150_ == 0 {
            let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v___x_1148_);
            v___x_1151_ = lean_nat_to_int(v___x_1148_);
            v___x_1152_ = lean_int_div_exact(v___x_1144_, v___x_1151_);
            lean_dec(v___x_1151_);
            lean_dec(v___x_1144_);
            v___x_1153_ = lean_nat_div_exact(v___x_1146_, v___x_1148_);
            lean_dec(v___x_1148_);
            lean_dec(v___x_1146_);
            v___x_1154_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1154_, 0, v___x_1152_);
            lean_ctor_set(v___x_1154_, 1, v___x_1153_);
            return v___x_1154_;
        } else {
            let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1148_);
            v___x_1155_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1155_, 0, v___x_1144_);
            lean_ctor_set(v___x_1155_, 1, v___x_1146_);
            return v___x_1155_;
        }
    }
}
pub unsafe fn l_Rat_ofScientific___boxed(
    mut v_m_1156_: *mut LeanObject,
    mut v_s_1157_: *mut LeanObject,
    mut v_e_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1159_: u8 = 0;
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1159_ = (lean_unbox(v_s_1157_) as u8);
    v_res_1160_ = l_Rat_ofScientific(v_m_1156_, v_s_boxed_1159_, v_e_1158_);
    lean_dec(v_e_1158_);
    return v_res_1160_;
}
pub unsafe fn l_Rat_blt(mut v_a_1163_: *mut LeanObject, mut v_b_1164_: *mut LeanObject) -> u8 {
    let mut v_num_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1168_: u8 = 0;
    let mut v___y_1169_: u8 = 0;
    let mut v_num_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1179_: u8 = 0;
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v_num_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v_num_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: u8 = 0;
    let mut v_num_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1165_ = lean_ctor_get(v_a_1163_, 0);
                lean_inc(v_num_1165_);
                v_den_1166_ = lean_ctor_get(v_a_1163_, 1);
                lean_inc(v_den_1166_);
                lean_dec_ref(v_a_1163_);
                v___x_1177_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
                    _init_l_instHashableRat_hash___closed__0,
                );
                v___x_1186_ = lean_int_dec_lt(v_num_1165_, v___x_1177_);
                if v___x_1186_ == 0 {
                    v___y_1179_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v_num_1187_ = lean_ctor_get(v_b_1164_, 0);
                    v___x_1188_ = lean_int_dec_le(v___x_1177_, v_num_1187_);
                    v___y_1179_ = v___x_1188_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1169_ == 0 {
                    v_num_1170_ = lean_ctor_get(v_b_1164_, 0);
                    lean_inc(v_num_1170_);
                    v_den_1171_ = lean_ctor_get(v_b_1164_, 1);
                    lean_inc(v_den_1171_);
                    lean_dec_ref(v_b_1164_);
                    v___x_1172_ = lean_nat_to_int(v_den_1171_);
                    v___x_1173_ = lean_int_mul(v_num_1165_, v___x_1172_);
                    lean_dec(v___x_1172_);
                    lean_dec(v_num_1165_);
                    v___x_1174_ = lean_nat_to_int(v_den_1166_);
                    v___x_1175_ = lean_int_mul(v_num_1170_, v___x_1174_);
                    lean_dec(v___x_1174_);
                    lean_dec(v_num_1170_);
                    v___x_1176_ = lean_int_dec_lt(v___x_1173_, v___x_1175_);
                    lean_dec(v___x_1175_);
                    lean_dec(v___x_1173_);
                    return v___x_1176_;
                } else {
                    lean_dec(v_den_1166_);
                    lean_dec(v_num_1165_);
                    lean_dec_ref(v_b_1164_);
                    return v___y_1168_;
                }
            }
            2 => {
                if v___y_1179_ == 0 {
                    v___x_1180_ = lean_int_dec_eq(v_num_1165_, v___x_1177_);
                    if v___x_1180_ == 0 {
                        v___x_1181_ = lean_int_dec_lt(v___x_1177_, v_num_1165_);
                        if v___x_1181_ == 0 {
                            v___y_1168_ = v___y_1179_;
                            v___y_1169_ = v___x_1181_;
                            state = 1;
                            continue;
                        } else {
                            v_num_1182_ = lean_ctor_get(v_b_1164_, 0);
                            v___x_1183_ = lean_int_dec_le(v_num_1182_, v___x_1177_);
                            v___y_1168_ = v___y_1179_;
                            v___y_1169_ = v___x_1183_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_den_1166_);
                        lean_dec(v_num_1165_);
                        v_num_1184_ = lean_ctor_get(v_b_1164_, 0);
                        lean_inc(v_num_1184_);
                        lean_dec_ref(v_b_1164_);
                        v___x_1185_ = lean_int_dec_lt(v___x_1177_, v_num_1184_);
                        lean_dec(v_num_1184_);
                        return v___x_1185_;
                    }
                } else {
                    lean_dec(v_den_1166_);
                    lean_dec(v_num_1165_);
                    lean_dec_ref(v_b_1164_);
                    return v___y_1179_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_blt___boxed(
    mut v_a_1189_: *mut LeanObject,
    mut v_b_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1191_: u8 = 0;
    let mut v_r_1192_: *mut LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Rat_blt(v_a_1189_, v_b_1190_);
    v_r_1192_ = lean_box((v_res_1191_) as usize);
    return v_r_1192_;
}
pub unsafe fn _init_l_Rat_instLT() -> *mut LeanObject {
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1193_ = lean_box(0);
    return v___x_1193_;
}
pub unsafe fn l_Rat_instDecidableLt(
    mut v_a_1194_: *mut LeanObject,
    mut v_b_1195_: *mut LeanObject,
) -> u8 {
    let mut v___x_1196_: u8 = 0;
    v___x_1196_ = l_Rat_blt(v_a_1194_, v_b_1195_);
    return v___x_1196_;
}
pub unsafe fn l_Rat_instDecidableLt___boxed(
    mut v_a_1197_: *mut LeanObject,
    mut v_b_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1199_: u8 = 0;
    let mut v_r_1200_: *mut LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Rat_instDecidableLt(v_a_1197_, v_b_1198_);
    v_r_1200_ = lean_box((v_res_1199_) as usize);
    return v_r_1200_;
}
pub unsafe fn _init_l_Rat_instLE() -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = lean_box(0);
    return v___x_1201_;
}
pub unsafe fn l_Rat_instDecidableLe(
    mut v_a_1202_: *mut LeanObject,
    mut v_b_1203_: *mut LeanObject,
) -> u8 {
    let mut v___x_1204_: u8 = 0;
    v___x_1204_ = l_Rat_blt(v_b_1203_, v_a_1202_);
    if v___x_1204_ == 0 {
        let mut v___x_1205_: u8 = 0;
        v___x_1205_ = 1;
        return v___x_1205_;
    } else {
        let mut v___x_1206_: u8 = 0;
        v___x_1206_ = 0;
        return v___x_1206_;
    }
}
pub unsafe fn l_Rat_instDecidableLe___boxed(
    mut v_a_1207_: *mut LeanObject,
    mut v_b_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1209_: u8 = 0;
    let mut v_r_1210_: *mut LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Rat_instDecidableLe(v_a_1207_, v_b_1208_);
    v_r_1210_ = lean_box((v_res_1209_) as usize);
    return v_r_1210_;
}
pub unsafe fn l_Rat_instMin___lam__0(
    mut v_x_1211_: *mut LeanObject,
    mut v_y_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1213_: u8 = 0;
    lean_inc_ref(v_y_1212_);
    lean_inc_ref(v_x_1211_);
    v___x_1213_ = l_Rat_instDecidableLe(v_x_1211_, v_y_1212_);
    if v___x_1213_ == 0 {
        lean_dec_ref(v_x_1211_);
        return v_y_1212_;
    } else {
        lean_dec_ref(v_y_1212_);
        return v_x_1211_;
    }
}
pub unsafe fn l_Rat_instMax___lam__0(
    mut v_x_1216_: *mut LeanObject,
    mut v_y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1218_: u8 = 0;
    lean_inc_ref(v_y_1217_);
    lean_inc_ref(v_x_1216_);
    v___x_1218_ = l_Rat_instDecidableLe(v_x_1216_, v_y_1217_);
    if v___x_1218_ == 0 {
        lean_dec_ref(v_y_1217_);
        return v_x_1216_;
    } else {
        lean_dec_ref(v_x_1216_);
        return v_y_1217_;
    }
}
pub unsafe fn l_Rat_mul(
    mut v_a_1221_: *mut LeanObject,
    mut v_b_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g1_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g2_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1223_ = lean_ctor_get(v_a_1221_, 0);
                v_den_1224_ = lean_ctor_get(v_a_1221_, 1);
                v_num_1225_ = lean_ctor_get(v_b_1222_, 0);
                v_den_1226_ = lean_ctor_get(v_b_1222_, 1);
                v_isSharedCheck_1245_ = (!lean_is_exclusive(v_b_1222_)) as u8;
                if v_isSharedCheck_1245_ == 0 {
                    v___x_1228_ = v_b_1222_;
                    v_isShared_1229_ = v_isSharedCheck_1245_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_den_1226_);
                    lean_inc(v_num_1225_);
                    lean_dec(v_b_1222_);
                    v___x_1228_ = lean_box(0);
                    v_isShared_1229_ = v_isSharedCheck_1245_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1230_ = lean_nat_abs(v_num_1223_);
                v_g1_1231_ = lean_nat_gcd(v___x_1230_, v_den_1226_);
                lean_dec(v___x_1230_);
                v___x_1232_ = lean_nat_abs(v_num_1225_);
                v_g2_1233_ = lean_nat_gcd(v___x_1232_, v_den_1224_);
                lean_dec(v___x_1232_);
                lean_inc(v_g1_1231_);
                v___x_1234_ = lean_nat_to_int(v_g1_1231_);
                v___x_1235_ = lean_int_div_exact(v_num_1223_, v___x_1234_);
                lean_dec(v___x_1234_);
                lean_inc(v_g2_1233_);
                v___x_1236_ = lean_nat_to_int(v_g2_1233_);
                v___x_1237_ = lean_int_div_exact(v_num_1225_, v___x_1236_);
                lean_dec(v___x_1236_);
                lean_dec(v_num_1225_);
                v___x_1238_ = lean_int_mul(v___x_1235_, v___x_1237_);
                lean_dec(v___x_1237_);
                lean_dec(v___x_1235_);
                v___x_1239_ = lean_nat_div_exact(v_den_1224_, v_g2_1233_);
                lean_dec(v_g2_1233_);
                v___x_1240_ = lean_nat_div_exact(v_den_1226_, v_g1_1231_);
                lean_dec(v_g1_1231_);
                lean_dec(v_den_1226_);
                v___x_1241_ = lean_nat_mul(v___x_1239_, v___x_1240_);
                lean_dec(v___x_1240_);
                lean_dec(v___x_1239_);
                if v_isShared_1229_ == 0 {
                    lean_ctor_set(v___x_1228_, 1, v___x_1241_);
                    lean_ctor_set(v___x_1228_, 0, v___x_1238_);
                    v___x_1243_ = v___x_1228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1241_);
                    v___x_1243_ = v_reuseFailAlloc_1244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_mul___boxed(
    mut v_a_1246_: *mut LeanObject,
    mut v_b_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Rat_mul(v_a_1246_, v_b_1247_);
    lean_dec_ref(v_a_1246_);
    return v_res_1248_;
}
pub unsafe fn l_Rat_inv(mut v_a_1251_: *mut LeanObject) -> *mut LeanObject {
    let mut v_num_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: u8 = 0;
    let mut v___x_1256_: u8 = 0;
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_unused_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1252_ = lean_ctor_get(v_a_1251_, 0);
                v_den_1253_ = lean_ctor_get(v_a_1251_, 1);
                v___x_1254_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
                    core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
                    _init_l_instHashableRat_hash___closed__0,
                );
                v___x_1255_ = lean_int_dec_lt(v_num_1252_, v___x_1254_);
                if v___x_1255_ == 0 {
                    v___x_1256_ = lean_int_dec_lt(v___x_1254_, v_num_1252_);
                    if v___x_1256_ == 0 {
                        return v_a_1251_;
                    } else {
                        lean_inc(v_den_1253_);
                        lean_inc(v_num_1252_);
                        v_isSharedCheck_1265_ = (!lean_is_exclusive(v_a_1251_)) as u8;
                        if v_isSharedCheck_1265_ == 0 {
                            v_unused_1266_ = lean_ctor_get(v_a_1251_, 1);
                            lean_dec(v_unused_1266_);
                            v_unused_1267_ = lean_ctor_get(v_a_1251_, 0);
                            lean_dec(v_unused_1267_);
                            v___x_1258_ = v_a_1251_;
                            v_isShared_1259_ = v_isSharedCheck_1265_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_1251_);
                            v___x_1258_ = lean_box(0);
                            v_isShared_1259_ = v_isSharedCheck_1265_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_den_1253_);
                    lean_inc(v_num_1252_);
                    v_isSharedCheck_1277_ = (!lean_is_exclusive(v_a_1251_)) as u8;
                    if v_isSharedCheck_1277_ == 0 {
                        v_unused_1278_ = lean_ctor_get(v_a_1251_, 1);
                        lean_dec(v_unused_1278_);
                        v_unused_1279_ = lean_ctor_get(v_a_1251_, 0);
                        lean_dec(v_unused_1279_);
                        v___x_1269_ = v_a_1251_;
                        v_isShared_1270_ = v_isSharedCheck_1277_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_1251_);
                        v___x_1269_ = lean_box(0);
                        v_isShared_1270_ = v_isSharedCheck_1277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1260_ = lean_nat_to_int(v_den_1253_);
                v___x_1261_ = lean_nat_abs(v_num_1252_);
                lean_dec(v_num_1252_);
                if v_isShared_1259_ == 0 {
                    lean_ctor_set(v___x_1258_, 1, v___x_1261_);
                    lean_ctor_set(v___x_1258_, 0, v___x_1260_);
                    v___x_1263_ = v___x_1258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1260_);
                    lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
                    v___x_1263_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1263_;
            }
            3 => {
                v___x_1271_ = lean_nat_to_int(v_den_1253_);
                v___x_1272_ = lean_int_neg(v___x_1271_);
                lean_dec(v___x_1271_);
                v___x_1273_ = lean_nat_abs(v_num_1252_);
                lean_dec(v_num_1252_);
                if v_isShared_1270_ == 0 {
                    lean_ctor_set(v___x_1269_, 1, v___x_1273_);
                    lean_ctor_set(v___x_1269_, 0, v___x_1272_);
                    v___x_1275_ = v___x_1269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
                    v___x_1275_ = v_reuseFailAlloc_1276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_pow(
    mut v_q_1282_: *mut LeanObject,
    mut v_n_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1284_ = lean_ctor_get(v_q_1282_, 0);
                v_den_1285_ = lean_ctor_get(v_q_1282_, 1);
                v_isSharedCheck_1294_ = (!lean_is_exclusive(v_q_1282_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1287_ = v_q_1282_;
                    v_isShared_1288_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_den_1285_);
                    lean_inc(v_num_1284_);
                    lean_dec(v_q_1282_);
                    v___x_1287_ = lean_box(0);
                    v_isShared_1288_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1289_ = l_Int_pow(v_num_1284_, v_n_1283_);
                lean_dec(v_num_1284_);
                v___x_1290_ = lean_nat_pow(v_den_1285_, v_n_1283_);
                lean_dec(v_den_1285_);
                if v_isShared_1288_ == 0 {
                    lean_ctor_set(v___x_1287_, 1, v___x_1290_);
                    lean_ctor_set(v___x_1287_, 0, v___x_1289_);
                    v___x_1292_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1289_);
                    lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1290_);
                    v___x_1292_ = v_reuseFailAlloc_1293_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_pow___boxed(
    mut v_q_1295_: *mut LeanObject,
    mut v_n_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_Rat_pow(v_q_1295_, v_n_1296_);
    lean_dec(v_n_1296_);
    return v_res_1297_;
}
pub unsafe fn l_Rat_zpow(
    mut v_q_1300_: *mut LeanObject,
    mut v_i_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1303_: u8 = 0;
    v_intZero_1302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0),
        core::ptr::addr_of_mut!(l_instHashableRat_hash___closed__0_once),
        _init_l_instHashableRat_hash___closed__0,
    );
    v_isNeg_1303_ = lean_int_dec_lt(v_i_1301_, v_intZero_1302_);
    if v_isNeg_1303_ == 0 {
        let mut v_a_1304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
        v_a_1304_ = lean_nat_abs(v_i_1301_);
        v___x_1305_ = l_Rat_pow(v_q_1300_, v_a_1304_);
        lean_dec(v_a_1304_);
        return v___x_1305_;
    } else {
        let mut v_abs_1306_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1307_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
        v_abs_1306_ = lean_nat_abs(v_i_1301_);
        v_one_1307_ = lean_unsigned_to_nat(1);
        v_a_1308_ = lean_nat_sub(v_abs_1306_, v_one_1307_);
        lean_dec(v_abs_1306_);
        v___x_1309_ = lean_nat_add(v_a_1308_, v_one_1307_);
        lean_dec(v_a_1308_);
        v___x_1310_ = l_Rat_pow(v_q_1300_, v___x_1309_);
        lean_dec(v___x_1309_);
        v___x_1311_ = l_Rat_inv(v___x_1310_);
        return v___x_1311_;
    }
}
pub unsafe fn l_Rat_zpow___boxed(
    mut v_q_1312_: *mut LeanObject,
    mut v_i_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Rat_zpow(v_q_1312_, v_i_1313_);
    lean_dec(v_i_1313_);
    return v_res_1314_;
}
pub unsafe fn l_Rat_div(
    mut v_x1_1317_: *mut LeanObject,
    mut v_x2_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v___x_1319_ = l_Rat_inv(v_x2_1318_);
    v___x_1320_ = l_Rat_mul(v_x1_1317_, v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn l_Rat_div___boxed(
    mut v_x1_1321_: *mut LeanObject,
    mut v_x2_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1323_: *mut LeanObject = core::ptr::null_mut();
    v_res_1323_ = l_Rat_div(v_x1_1321_, v_x2_1322_);
    lean_dec_ref(v_x1_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Rat_add(
    mut v_a_1326_: *mut LeanObject,
    mut v_b_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g1_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1328_ = lean_ctor_get(v_a_1326_, 0);
                lean_inc(v_num_1328_);
                v_den_1329_ = lean_ctor_get(v_a_1326_, 1);
                lean_inc(v_den_1329_);
                lean_dec_ref(v_a_1326_);
                v_num_1330_ = lean_ctor_get(v_b_1327_, 0);
                v_den_1331_ = lean_ctor_get(v_b_1327_, 1);
                v_isSharedCheck_1367_ = (!lean_is_exclusive(v_b_1327_)) as u8;
                if v_isSharedCheck_1367_ == 0 {
                    v___x_1333_ = v_b_1327_;
                    v_isShared_1334_ = v_isSharedCheck_1367_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_den_1331_);
                    lean_inc(v_num_1330_);
                    lean_dec(v_b_1327_);
                    v___x_1333_ = lean_box(0);
                    v_isShared_1334_ = v_isSharedCheck_1367_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1335_ = lean_nat_gcd(v_den_1329_, v_den_1331_);
                v___x_1336_ = lean_unsigned_to_nat(1);
                v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
                if v___x_1337_ == 0 {
                    v___x_1338_ = lean_nat_div(v_den_1329_, v___x_1335_);
                    lean_dec(v_den_1329_);
                    v_den_1339_ = lean_nat_mul(v___x_1338_, v_den_1331_);
                    v___x_1340_ = lean_nat_div(v_den_1331_, v___x_1335_);
                    lean_dec(v_den_1331_);
                    v___x_1341_ = lean_nat_to_int(v___x_1340_);
                    v___x_1342_ = lean_int_mul(v_num_1328_, v___x_1341_);
                    lean_dec(v___x_1341_);
                    lean_dec(v_num_1328_);
                    v___x_1343_ = lean_nat_to_int(v___x_1338_);
                    v___x_1344_ = lean_int_mul(v_num_1330_, v___x_1343_);
                    lean_dec(v___x_1343_);
                    lean_dec(v_num_1330_);
                    v_num_1345_ = lean_int_add(v___x_1342_, v___x_1344_);
                    lean_dec(v___x_1344_);
                    lean_dec(v___x_1342_);
                    v___x_1346_ = lean_nat_abs(v_num_1345_);
                    v_g1_1347_ = lean_nat_gcd(v___x_1346_, v___x_1335_);
                    lean_dec(v___x_1335_);
                    lean_dec(v___x_1346_);
                    v___x_1348_ = lean_nat_dec_eq(v_g1_1347_, v___x_1336_);
                    if v___x_1348_ == 0 {
                        lean_inc(v_g1_1347_);
                        v___x_1349_ = lean_nat_to_int(v_g1_1347_);
                        v___x_1350_ = lean_int_div_exact(v_num_1345_, v___x_1349_);
                        lean_dec(v___x_1349_);
                        lean_dec(v_num_1345_);
                        v___x_1351_ = lean_nat_div_exact(v_den_1339_, v_g1_1347_);
                        lean_dec(v_g1_1347_);
                        lean_dec(v_den_1339_);
                        if v_isShared_1334_ == 0 {
                            lean_ctor_set(v___x_1333_, 1, v___x_1351_);
                            lean_ctor_set(v___x_1333_, 0, v___x_1350_);
                            v___x_1353_ = v___x_1333_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1350_);
                            lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1351_);
                            v___x_1353_ = v_reuseFailAlloc_1354_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_g1_1347_);
                        if v_isShared_1334_ == 0 {
                            lean_ctor_set(v___x_1333_, 1, v_den_1339_);
                            lean_ctor_set(v___x_1333_, 0, v_num_1345_);
                            v___x_1356_ = v___x_1333_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_num_1345_);
                            lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_den_1339_);
                            v___x_1356_ = v_reuseFailAlloc_1357_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1335_);
                    lean_inc(v_den_1331_);
                    v___x_1358_ = lean_nat_to_int(v_den_1331_);
                    v___x_1359_ = lean_int_mul(v_num_1328_, v___x_1358_);
                    lean_dec(v___x_1358_);
                    lean_dec(v_num_1328_);
                    lean_inc(v_den_1329_);
                    v___x_1360_ = lean_nat_to_int(v_den_1329_);
                    v___x_1361_ = lean_int_mul(v_num_1330_, v___x_1360_);
                    lean_dec(v___x_1360_);
                    lean_dec(v_num_1330_);
                    v___x_1362_ = lean_int_add(v___x_1359_, v___x_1361_);
                    lean_dec(v___x_1361_);
                    lean_dec(v___x_1359_);
                    v___x_1363_ = lean_nat_mul(v_den_1329_, v_den_1331_);
                    lean_dec(v_den_1331_);
                    lean_dec(v_den_1329_);
                    if v_isShared_1334_ == 0 {
                        lean_ctor_set(v___x_1333_, 1, v___x_1363_);
                        lean_ctor_set(v___x_1333_, 0, v___x_1362_);
                        v___x_1365_ = v___x_1333_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1362_);
                        lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
                        v___x_1365_ = v_reuseFailAlloc_1366_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1353_;
            }
            3 => {
                return v___x_1356_;
            }
            4 => {
                return v___x_1365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_neg(mut v_a_1370_: *mut LeanObject) -> *mut LeanObject {
    let mut v_num_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1375_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1371_ = lean_ctor_get(v_a_1370_, 0);
                v_den_1372_ = lean_ctor_get(v_a_1370_, 1);
                v_isSharedCheck_1380_ = (!lean_is_exclusive(v_a_1370_)) as u8;
                if v_isSharedCheck_1380_ == 0 {
                    v___x_1374_ = v_a_1370_;
                    v_isShared_1375_ = v_isSharedCheck_1380_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_den_1372_);
                    lean_inc(v_num_1371_);
                    lean_dec(v_a_1370_);
                    v___x_1374_ = lean_box(0);
                    v_isShared_1375_ = v_isSharedCheck_1380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1376_ = lean_int_neg(v_num_1371_);
                lean_dec(v_num_1371_);
                if v_isShared_1375_ == 0 {
                    lean_ctor_set(v___x_1374_, 0, v___x_1376_);
                    v___x_1378_ = v___x_1374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
                    lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_den_1372_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_sub(
    mut v_a_1383_: *mut LeanObject,
    mut v_b_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_num_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g1_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_num_1385_ = lean_ctor_get(v_a_1383_, 0);
                lean_inc(v_num_1385_);
                v_den_1386_ = lean_ctor_get(v_a_1383_, 1);
                lean_inc(v_den_1386_);
                lean_dec_ref(v_a_1383_);
                v_num_1387_ = lean_ctor_get(v_b_1384_, 0);
                v_den_1388_ = lean_ctor_get(v_b_1384_, 1);
                v_isSharedCheck_1424_ = (!lean_is_exclusive(v_b_1384_)) as u8;
                if v_isSharedCheck_1424_ == 0 {
                    v___x_1390_ = v_b_1384_;
                    v_isShared_1391_ = v_isSharedCheck_1424_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_den_1388_);
                    lean_inc(v_num_1387_);
                    lean_dec(v_b_1384_);
                    v___x_1390_ = lean_box(0);
                    v_isShared_1391_ = v_isSharedCheck_1424_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1392_ = lean_nat_gcd(v_den_1386_, v_den_1388_);
                v___x_1393_ = lean_unsigned_to_nat(1);
                v___x_1394_ = lean_nat_dec_eq(v___x_1392_, v___x_1393_);
                if v___x_1394_ == 0 {
                    v___x_1395_ = lean_nat_div(v_den_1386_, v___x_1392_);
                    lean_dec(v_den_1386_);
                    v_den_1396_ = lean_nat_mul(v___x_1395_, v_den_1388_);
                    v___x_1397_ = lean_nat_div(v_den_1388_, v___x_1392_);
                    lean_dec(v_den_1388_);
                    v___x_1398_ = lean_nat_to_int(v___x_1397_);
                    v___x_1399_ = lean_int_mul(v_num_1385_, v___x_1398_);
                    lean_dec(v___x_1398_);
                    lean_dec(v_num_1385_);
                    v___x_1400_ = lean_nat_to_int(v___x_1395_);
                    v___x_1401_ = lean_int_mul(v_num_1387_, v___x_1400_);
                    lean_dec(v___x_1400_);
                    lean_dec(v_num_1387_);
                    v_num_1402_ = lean_int_sub(v___x_1399_, v___x_1401_);
                    lean_dec(v___x_1401_);
                    lean_dec(v___x_1399_);
                    v___x_1403_ = lean_nat_abs(v_num_1402_);
                    v_g1_1404_ = lean_nat_gcd(v___x_1403_, v___x_1392_);
                    lean_dec(v___x_1392_);
                    lean_dec(v___x_1403_);
                    v___x_1405_ = lean_nat_dec_eq(v_g1_1404_, v___x_1393_);
                    if v___x_1405_ == 0 {
                        lean_inc(v_g1_1404_);
                        v___x_1406_ = lean_nat_to_int(v_g1_1404_);
                        v___x_1407_ = lean_int_div_exact(v_num_1402_, v___x_1406_);
                        lean_dec(v___x_1406_);
                        lean_dec(v_num_1402_);
                        v___x_1408_ = lean_nat_div_exact(v_den_1396_, v_g1_1404_);
                        lean_dec(v_g1_1404_);
                        lean_dec(v_den_1396_);
                        if v_isShared_1391_ == 0 {
                            lean_ctor_set(v___x_1390_, 1, v___x_1408_);
                            lean_ctor_set(v___x_1390_, 0, v___x_1407_);
                            v___x_1410_ = v___x_1390_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
                            lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
                            v___x_1410_ = v_reuseFailAlloc_1411_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_g1_1404_);
                        if v_isShared_1391_ == 0 {
                            lean_ctor_set(v___x_1390_, 1, v_den_1396_);
                            lean_ctor_set(v___x_1390_, 0, v_num_1402_);
                            v___x_1413_ = v___x_1390_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_num_1402_);
                            lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_den_1396_);
                            v___x_1413_ = v_reuseFailAlloc_1414_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1392_);
                    lean_inc(v_den_1388_);
                    v___x_1415_ = lean_nat_to_int(v_den_1388_);
                    v___x_1416_ = lean_int_mul(v_num_1385_, v___x_1415_);
                    lean_dec(v___x_1415_);
                    lean_dec(v_num_1385_);
                    lean_inc(v_den_1386_);
                    v___x_1417_ = lean_nat_to_int(v_den_1386_);
                    v___x_1418_ = lean_int_mul(v_num_1387_, v___x_1417_);
                    lean_dec(v___x_1417_);
                    lean_dec(v_num_1387_);
                    v___x_1419_ = lean_int_sub(v___x_1416_, v___x_1418_);
                    lean_dec(v___x_1418_);
                    lean_dec(v___x_1416_);
                    v___x_1420_ = lean_nat_mul(v_den_1386_, v_den_1388_);
                    lean_dec(v_den_1388_);
                    lean_dec(v_den_1386_);
                    if v_isShared_1391_ == 0 {
                        lean_ctor_set(v___x_1390_, 1, v___x_1420_);
                        lean_ctor_set(v___x_1390_, 0, v___x_1419_);
                        v___x_1422_ = v___x_1390_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1419_);
                        lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1420_);
                        v___x_1422_ = v_reuseFailAlloc_1423_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1410_;
            }
            3 => {
                return v___x_1413_;
            }
            4 => {
                return v___x_1422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Rat_floor(mut v_a_1427_: *mut LeanObject) -> *mut LeanObject {
    let mut v_num_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: u8 = 0;
    v_num_1428_ = lean_ctor_get(v_a_1427_, 0);
    lean_inc(v_num_1428_);
    v_den_1429_ = lean_ctor_get(v_a_1427_, 1);
    lean_inc(v_den_1429_);
    lean_dec_ref(v_a_1427_);
    v___x_1430_ = lean_unsigned_to_nat(1);
    v___x_1431_ = lean_nat_dec_eq(v_den_1429_, v___x_1430_);
    if v___x_1431_ == 0 {
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
        v___x_1432_ = lean_nat_to_int(v_den_1429_);
        v___x_1433_ = lean_int_ediv(v_num_1428_, v___x_1432_);
        lean_dec(v___x_1432_);
        lean_dec(v_num_1428_);
        return v___x_1433_;
    } else {
        lean_dec(v_den_1429_);
        return v_num_1428_;
    }
}
pub unsafe fn _init_l_Rat_ceil___closed__0() -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = lean_unsigned_to_nat(1);
    v___x_1435_ = lean_nat_to_int(v___x_1434_);
    return v___x_1435_;
}
pub unsafe fn l_Rat_ceil(mut v_a_1436_: *mut LeanObject) -> *mut LeanObject {
    let mut v_num_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u8 = 0;
    v_num_1437_ = lean_ctor_get(v_a_1436_, 0);
    lean_inc(v_num_1437_);
    v_den_1438_ = lean_ctor_get(v_a_1436_, 1);
    lean_inc(v_den_1438_);
    lean_dec_ref(v_a_1436_);
    v___x_1439_ = lean_unsigned_to_nat(1);
    v___x_1440_ = lean_nat_dec_eq(v_den_1438_, v___x_1439_);
    if v___x_1440_ == 0 {
        let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
        v___x_1441_ = lean_nat_to_int(v_den_1438_);
        v___x_1442_ = lean_int_ediv(v_num_1437_, v___x_1441_);
        lean_dec(v___x_1441_);
        lean_dec(v_num_1437_);
        v___x_1443_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Rat_ceil___closed__0),
            core::ptr::addr_of_mut!(l_Rat_ceil___closed__0_once),
            _init_l_Rat_ceil___closed__0,
        );
        v___x_1444_ = lean_int_add(v___x_1442_, v___x_1443_);
        lean_dec(v___x_1442_);
        return v___x_1444_;
    } else {
        lean_dec(v_den_1438_);
        return v_num_1437_;
    }
}
pub unsafe fn _init_l_Rat_abs___closed__0() -> *mut LeanObject {
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    v___x_1445_ = lean_unsigned_to_nat(0);
    v___x_1446_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_1445_);
    return v___x_1446_;
}
pub unsafe fn l_Rat_abs(mut v_a_1447_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    v___x_1448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Rat_abs___closed__0),
        core::ptr::addr_of_mut!(l_Rat_abs___closed__0_once),
        _init_l_Rat_abs___closed__0,
    );
    lean_inc_ref(v_a_1447_);
    v___x_1449_ = l_Rat_instDecidableLe(v___x_1448_, v_a_1447_);
    if v___x_1449_ == 0 {
        let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
        v___x_1450_ = l_Rat_neg(v_a_1447_);
        return v___x_1450_;
    } else {
        return v_a_1447_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Rat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Coprime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_instInhabitedRat = _init_l_instInhabitedRat();
    lean_mark_persistent(l_instInhabitedRat);
    l_Rat_instLT = _init_l_Rat_instLT();
    lean_mark_persistent(l_Rat_instLT);
    l_Rat_instLE = _init_l_Rat_instLE();
    lean_mark_persistent(l_Rat_instLE);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Rat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Rat_den__nz___autoParam = _init_l_Rat_den__nz___autoParam();
    lean_mark_persistent(l_Rat_den__nz___autoParam);
    l_Rat_reduced___autoParam = _init_l_Rat_reduced___autoParam();
    lean_mark_persistent(l_Rat_reduced___autoParam);
    l_Rat_normalize___auto__1 = _init_l_Rat_normalize___auto__1();
    lean_mark_persistent(l_Rat_normalize___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Rat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Coprime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Rat_Basic(builtin);
}
