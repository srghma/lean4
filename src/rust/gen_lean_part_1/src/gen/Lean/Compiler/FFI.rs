// Lean compiler output
// Module: Lean.Compiler.FFI
// Imports: Init.System.FilePath Init.Data.String.Search
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_get_internal_linker_flags, lean_get_leanc_extra_flags, lean_get_leanc_internal_flags,
    lean_get_linker_flags, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_append, lean_string_get_byte_fast,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint8_dec_eq, lean_uint32_dec_eq, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_pos_x21, l_String_Slice_slice_x21};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posGE___redArg;
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, l_System_FilePath_join,
    runtime_initialize_Init_System_FilePath,
};
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getCFlags_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getCFlags_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_FFI_getCFlags_x27: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_FFI_getCFlags___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [45, 73, 0],
    };
static mut l_Lean_Compiler_FFI_getCFlags___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_FFI_getCFlags___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_FFI_getCFlags___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [105, 110, 99, 108, 117, 100, 101, 0],
    };
static mut l_Lean_Compiler_FFI_getCFlags___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_FFI_getCFlags___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_FFI_getCFlags___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getCFlags___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 79, 79, 84, 0]};
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3: u8 = 0;
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalCFlags___closed__2: usize = 0;
pub static l_Lean_Compiler_FFI_getLinkerFlags___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [45, 76, 0],
    };
static mut l_Lean_Compiler_FFI_getLinkerFlags___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_FFI_getLinkerFlags___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_FFI_getLinkerFlags___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [108, 105, 98, 0],
    };
static mut l_Lean_Compiler_FFI_getLinkerFlags___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_FFI_getLinkerFlags___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_FFI_getLinkerFlags___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lean_Compiler_FFI_getLinkerFlags___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_FFI_getLinkerFlags___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getLinkerFlags___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2: usize = 0;
pub unsafe fn l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(
    mut v_a_00___x40___internal___hyg_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = lean_get_leanc_extra_flags(v_a_00___x40___internal___hyg_360_);
    return v_res_361_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(
    mut v_s_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
    return v___x_365_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(
    mut v_s_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v_s_366_);
    leanh::lean_dec_ref(v_s_366_);
    return v_res_367_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(
    mut v_s_368_: *mut leanh::LeanObject,
    mut v___x_369_: *mut leanh::LeanObject,
    mut v___x_370_: *mut leanh::LeanObject,
    mut v_a_371_: *mut leanh::LeanObject,
    mut v_b_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: u8 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_389_: u8 = 0;
    let mut v_startInclusive_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: u32 = 0;
    let mut v___x_395_: u32 = 0;
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_371_) == 0 {
                    v_currPos_385_ = leanh::lean_ctor_get(v_a_371_, 0);
                    v_searcher_386_ = leanh::lean_ctor_get(v_a_371_, 1);
                    v_isSharedCheck_412_ = (!leanh::lean_is_exclusive(v_a_371_)) as u8;
                    if v_isSharedCheck_412_ == 0 {
                        v___x_388_ = v_a_371_;
                        v_isShared_389_ = v_isSharedCheck_412_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_386_);
                        leanh::lean_inc(v_currPos_385_);
                        leanh::lean_dec(v_a_371_);
                        v___x_388_ = leanh::lean_box(0);
                        v_isShared_389_ = v_isSharedCheck_412_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_370_);
                    leanh::lean_dec_ref(v_s_368_);
                    return v_b_372_;
                }
            }
            1 => {
                v___x_377_ = lean_nat_sub(v_endExclusive_376_, v_startInclusive_375_);
                v___x_378_ = leanh::lean_unsigned_to_nat(0);
                v___x_379_ = lean_nat_dec_eq(v___x_377_, v___x_378_);
                leanh::lean_dec(v___x_377_);
                if v___x_379_ == 0 {
                    leanh::lean_inc_ref(v_s_368_);
                    v___x_380_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_380_, 0, v_s_368_);
                    leanh::lean_ctor_set(v___x_380_, 1, v_startInclusive_375_);
                    leanh::lean_ctor_set(v___x_380_, 2, v_endExclusive_376_);
                    v___x_381_ = l_String_Slice_toString(v___x_380_);
                    leanh::lean_dec_ref_known(v___x_380_, 3);
                    v___x_382_ = lean_array_push(v_b_372_, v___x_381_);
                    v_a_371_ = v_it_374_;
                    v_b_372_ = v___x_382_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_endExclusive_376_);
                    leanh::lean_dec(v_startInclusive_375_);
                    v_a_371_ = v_it_374_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_startInclusive_390_ = leanh::lean_ctor_get(v___x_369_, 1);
                v_endExclusive_391_ = leanh::lean_ctor_get(v___x_369_, 2);
                v___x_392_ = lean_nat_sub(v_endExclusive_391_, v_startInclusive_390_);
                v___x_393_ = lean_nat_dec_eq(v_searcher_386_, v___x_392_);
                leanh::lean_dec(v___x_392_);
                if v___x_393_ == 0 {
                    v___x_394_ = 32;
                    v___x_395_ = lean_string_utf8_get_fast(v_s_368_, v_searcher_386_);
                    v___x_396_ = lean_uint32_dec_eq(v___x_395_, v___x_394_);
                    if v___x_396_ == 0 {
                        v___x_397_ = lean_string_utf8_next_fast(v_s_368_, v_searcher_386_);
                        leanh::lean_dec(v_searcher_386_);
                        if v_isShared_389_ == 0 {
                            leanh::lean_ctor_set(v___x_388_, 1, v___x_397_);
                            v___x_399_ = v___x_388_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_401_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v_currPos_385_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_397_);
                            v___x_399_ = v_reuseFailAlloc_401_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_402_ = lean_string_utf8_next_fast(v_s_368_, v_searcher_386_);
                        v___x_403_ = lean_nat_sub(v___x_402_, v_searcher_386_);
                        v___x_404_ = lean_nat_add(v_searcher_386_, v___x_403_);
                        leanh::lean_dec(v___x_403_);
                        v_slice_405_ = l_String_Slice_subslice_x21(
                            v___x_369_,
                            v_currPos_385_,
                            v_searcher_386_,
                        );
                        leanh::lean_inc(v___x_404_);
                        if v_isShared_389_ == 0 {
                            leanh::lean_ctor_set(v___x_388_, 1, v___x_404_);
                            leanh::lean_ctor_set(v___x_388_, 0, v___x_404_);
                            v_nextIt_407_ = v___x_388_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_410_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
                            v_nextIt_407_ = v_reuseFailAlloc_410_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_388_);
                    leanh::lean_dec(v_searcher_386_);
                    v___x_411_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_370_);
                    v_it_374_ = v___x_411_;
                    v_startInclusive_375_ = v_currPos_385_;
                    v_endExclusive_376_ = v___x_370_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_371_ = v___x_399_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_408_ = leanh::lean_ctor_get(v_slice_405_, 0);
                leanh::lean_inc(v_startInclusive_408_);
                v_endExclusive_409_ = leanh::lean_ctor_get(v_slice_405_, 1);
                leanh::lean_inc(v_endExclusive_409_);
                leanh::lean_dec_ref(v_slice_405_);
                v_it_374_ = v_nextIt_407_;
                v_startInclusive_375_ = v_startInclusive_408_;
                v_endExclusive_376_ = v_endExclusive_409_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg___boxed(
    mut v_s_413_: *mut leanh::LeanObject,
    mut v___x_414_: *mut leanh::LeanObject,
    mut v___x_415_: *mut leanh::LeanObject,
    mut v_a_416_: *mut leanh::LeanObject,
    mut v_b_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_418_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_413_, v___x_414_, v___x_415_, v_a_416_, v_b_417_);
    leanh::lean_dec_ref(v___x_414_);
    return v_res_418_;
}
pub unsafe fn l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(
    mut v_s_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = leanh::lean_unsigned_to_nat(0);
    v___x_423_ = lean_string_utf8_byte_size(v_s_421_);
    leanh::lean_inc_ref(v_s_421_);
    v___x_424_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_424_, 0, v_s_421_);
    leanh::lean_ctor_set(v___x_424_, 1, v___x_422_);
    leanh::lean_ctor_set(v___x_424_, 2, v___x_423_);
    v___x_425_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(v___x_424_);
    v___x_426_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0;
    v___x_427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_421_, v___x_424_, v___x_423_, v___x_425_, v___x_426_);
    leanh::lean_dec_ref_known(v___x_424_, 3);
    return v___x_427_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(
    mut v_s_428_: *mut leanh::LeanObject,
    mut v___x_429_: *mut leanh::LeanObject,
    mut v___x_430_: *mut leanh::LeanObject,
    mut v_inst_431_: *mut leanh::LeanObject,
    mut v_R_432_: *mut leanh::LeanObject,
    mut v_a_433_: *mut leanh::LeanObject,
    mut v_b_434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___redArg(v_s_428_, v___x_429_, v___x_430_, v_a_433_, v_b_434_);
    return v___x_435_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1___boxed(
    mut v_s_436_: *mut leanh::LeanObject,
    mut v___x_437_: *mut leanh::LeanObject,
    mut v___x_438_: *mut leanh::LeanObject,
    mut v_inst_439_: *mut leanh::LeanObject,
    mut v_R_440_: *mut leanh::LeanObject,
    mut v_a_441_: *mut leanh::LeanObject,
    mut v_b_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__1(v_s_436_, v___x_437_, v___x_438_, v_inst_439_, v_R_440_, v_a_441_, v_b_442_);
    leanh::lean_dec_ref(v___x_437_);
    return v_res_443_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = leanh::lean_box(0);
    v___x_445_ = lean_get_leanc_extra_flags(v___x_444_);
    return v___x_445_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags_x27___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags_x27___closed__0_once),
        _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0,
    );
    v___x_447_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_446_);
    return v___x_447_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getCFlags_x27() -> *mut leanh::LeanObject {
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags_x27___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags_x27___closed__1_once),
        _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1,
    );
    return v___x_448_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getCFlags___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_451_ = l_Lean_Compiler_FFI_getCFlags___closed__0;
    v___x_452_ = leanh::lean_unsigned_to_nat(2);
    v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
    v___x_454_ = lean_array_push(v___x_453_, v___x_451_);
    return v___x_454_;
}
pub unsafe fn l_Lean_Compiler_FFI_getCFlags(
    mut v_leanSysroot_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Compiler_FFI_getCFlags___closed__1;
    v___x_457_ = l_System_FilePath_join(v_leanSysroot_455_, v___x_456_);
    v___x_458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getCFlags___closed__2_once),
        _init_l_Lean_Compiler_FFI_getCFlags___closed__2,
    );
    v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
    v___x_460_ = l_Lean_Compiler_FFI_getCFlags_x27;
    v___x_461_ = l_Array_append___redArg(v___x_459_, v___x_460_);
    return v___x_461_;
}
pub unsafe fn l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(
    mut v_a_00___x40___internal___hyg_463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = lean_get_leanc_internal_flags(v_a_00___x40___internal___hyg_463_);
    return v_res_464_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(
    mut v_s_465_: *mut leanh::LeanObject,
    mut v_replacement_466_: *mut leanh::LeanObject,
    mut v_a_467_: *mut leanh::LeanObject,
    mut v_b_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v_startInclusive_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_pos_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v_str_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v_needle_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v_str_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u8 = 0;
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_535_: u8 = 0;
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_537_: u8 = 0;
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    let mut v_oldBasePos_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBasePos_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_467_) {
                0 => {
                    v_pos_487_ = leanh::lean_ctor_get(v_a_467_, 0);
                    v_isSharedCheck_499_ = (!leanh::lean_is_exclusive(v_a_467_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v___x_489_ = v_a_467_;
                        v_isShared_490_ = v_isSharedCheck_499_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_487_);
                        leanh::lean_dec(v_a_467_);
                        v___x_489_ = leanh::lean_box(0);
                        v_isShared_490_ = v_isSharedCheck_499_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_pos_500_ = leanh::lean_ctor_get(v_a_467_, 0);
                    v_isSharedCheck_512_ = (!leanh::lean_is_exclusive(v_a_467_)) as u8;
                    if v_isSharedCheck_512_ == 0 {
                        v___x_502_ = v_a_467_;
                        v_isShared_503_ = v_isSharedCheck_512_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_500_);
                        leanh::lean_dec(v_a_467_);
                        v___x_502_ = leanh::lean_box(0);
                        v_isShared_503_ = v_isSharedCheck_512_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_needle_513_ = leanh::lean_ctor_get(v_a_467_, 0);
                    v_table_514_ = leanh::lean_ctor_get(v_a_467_, 1);
                    v_stackPos_515_ = leanh::lean_ctor_get(v_a_467_, 2);
                    v_needlePos_516_ = leanh::lean_ctor_get(v_a_467_, 3);
                    v_isSharedCheck_575_ = (!leanh::lean_is_exclusive(v_a_467_)) as u8;
                    if v_isSharedCheck_575_ == 0 {
                        v___x_518_ = v_a_467_;
                        v_isShared_519_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_needlePos_516_);
                        leanh::lean_inc(v_stackPos_515_);
                        leanh::lean_inc(v_table_514_);
                        leanh::lean_inc(v_needle_513_);
                        leanh::lean_dec(v_a_467_);
                        v___x_518_ = leanh::lean_box(0);
                        v_isShared_519_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_s_465_);
                    return v_b_468_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_s_465_);
                v___x_473_ = l_String_Slice_slice_x21(v_s_465_, v_startPos_471_, v_endPos_472_);
                leanh::lean_dec(v_endPos_472_);
                leanh::lean_dec(v_startPos_471_);
                v_str_474_ = leanh::lean_ctor_get(v___x_473_, 0);
                leanh::lean_inc_ref(v_str_474_);
                v_startInclusive_475_ = leanh::lean_ctor_get(v___x_473_, 1);
                leanh::lean_inc(v_startInclusive_475_);
                v_endExclusive_476_ = leanh::lean_ctor_get(v___x_473_, 2);
                leanh::lean_inc(v_endExclusive_476_);
                leanh::lean_dec_ref(v___x_473_);
                v___x_477_ = lean_string_utf8_extract(
                    v_str_474_,
                    v_startInclusive_475_,
                    v_endExclusive_476_,
                );
                leanh::lean_dec(v_endExclusive_476_);
                leanh::lean_dec(v_startInclusive_475_);
                leanh::lean_dec_ref(v_str_474_);
                v___x_478_ = lean_string_append(v_b_468_, v___x_477_);
                leanh::lean_dec_ref(v___x_477_);
                v_a_467_ = v_it_470_;
                v_b_468_ = v___x_478_;
                state = 0;
                continue;
            }
            2 => {
                v___x_482_ = leanh::lean_unsigned_to_nat(0);
                v___x_483_ = lean_string_utf8_byte_size(v_replacement_466_);
                v___x_484_ = lean_string_utf8_extract(v_replacement_466_, v___x_482_, v___x_483_);
                v___x_485_ = lean_string_append(v_b_468_, v___x_484_);
                leanh::lean_dec_ref(v___x_484_);
                v_a_467_ = v_it_481_;
                v_b_468_ = v___x_485_;
                state = 0;
                continue;
            }
            3 => {
                v_startInclusive_491_ = leanh::lean_ctor_get(v_s_465_, 1);
                v_endExclusive_492_ = leanh::lean_ctor_get(v_s_465_, 2);
                v___x_493_ = lean_nat_sub(v_endExclusive_492_, v_startInclusive_491_);
                v___x_494_ = lean_nat_dec_eq(v_pos_487_, v___x_493_);
                leanh::lean_dec(v___x_493_);
                if v___x_494_ == 0 {
                    if v_isShared_490_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_489_, 1);
                        v___x_496_ = v___x_489_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_497_, 0, v_pos_487_);
                        v___x_496_ = v_reuseFailAlloc_497_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_489_);
                    leanh::lean_dec(v_pos_487_);
                    v___x_498_ = leanh::lean_box(3);
                    v_it_481_ = v___x_498_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_it_481_ = v___x_496_;
                state = 2;
                continue;
            }
            5 => {
                v_str_504_ = leanh::lean_ctor_get(v_s_465_, 0);
                v_startInclusive_505_ = leanh::lean_ctor_get(v_s_465_, 1);
                v___x_506_ = lean_nat_add(v_startInclusive_505_, v_pos_500_);
                v___x_507_ = lean_string_utf8_next_fast(v_str_504_, v___x_506_);
                leanh::lean_dec(v___x_506_);
                v___x_508_ = lean_nat_sub(v___x_507_, v_startInclusive_505_);
                leanh::lean_inc(v___x_508_);
                if v_isShared_503_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_502_, 0);
                    leanh::lean_ctor_set(v___x_502_, 0, v___x_508_);
                    v___x_510_ = v___x_502_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
                    v___x_510_ = v_reuseFailAlloc_511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_it_470_ = v___x_510_;
                v_startPos_471_ = v_pos_500_;
                v_endPos_472_ = v___x_508_;
                state = 1;
                continue;
            }
            7 => {
                v_str_520_ = leanh::lean_ctor_get(v_needle_513_, 0);
                v_startInclusive_521_ = leanh::lean_ctor_get(v_needle_513_, 1);
                v_endExclusive_522_ = leanh::lean_ctor_get(v_needle_513_, 2);
                v_str_523_ = leanh::lean_ctor_get(v_s_465_, 0);
                v_startInclusive_524_ = leanh::lean_ctor_get(v_s_465_, 1);
                v_endExclusive_525_ = leanh::lean_ctor_get(v_s_465_, 2);
                v_basePos_526_ = lean_nat_sub(v_stackPos_515_, v_needlePos_516_);
                v___x_527_ = lean_nat_sub(v_endExclusive_522_, v_startInclusive_521_);
                v___x_528_ = lean_nat_add(v_basePos_526_, v___x_527_);
                v___x_529_ = lean_nat_sub(v_endExclusive_525_, v_startInclusive_524_);
                v___x_530_ = lean_nat_dec_le(v___x_528_, v___x_529_);
                leanh::lean_dec(v___x_528_);
                if v___x_530_ == 0 {
                    leanh::lean_dec(v___x_527_);
                    leanh::lean_del_object(v___x_518_);
                    leanh::lean_dec(v_needlePos_516_);
                    leanh::lean_dec(v_stackPos_515_);
                    leanh::lean_dec_ref(v_table_514_);
                    leanh::lean_dec_ref(v_needle_513_);
                    v___x_531_ = lean_nat_dec_lt(v_basePos_526_, v___x_529_);
                    if v___x_531_ == 0 {
                        leanh::lean_dec(v___x_529_);
                        leanh::lean_dec(v_basePos_526_);
                        leanh::lean_dec_ref(v_s_465_);
                        return v_b_468_;
                    } else {
                        v___x_532_ = l_String_Slice_pos_x21(v_s_465_, v_basePos_526_);
                        leanh::lean_dec(v_basePos_526_);
                        v___x_533_ = leanh::lean_box(3);
                        v_it_470_ = v___x_533_;
                        v_startPos_471_ = v___x_532_;
                        v_endPos_472_ = v___x_529_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_529_);
                    v___x_534_ = lean_nat_add(v_startInclusive_524_, v_stackPos_515_);
                    v_stackByte_535_ = lean_string_get_byte_fast(v_str_523_, v___x_534_);
                    v___x_536_ = lean_nat_add(v_startInclusive_521_, v_needlePos_516_);
                    v_patByte_537_ = lean_string_get_byte_fast(v_str_520_, v___x_536_);
                    v___x_538_ = lean_uint8_dec_eq(v_stackByte_535_, v_patByte_537_);
                    if v___x_538_ == 0 {
                        leanh::lean_dec(v___x_527_);
                        v___x_539_ = leanh::lean_unsigned_to_nat(0);
                        v___x_540_ = lean_nat_dec_eq(v_needlePos_516_, v___x_539_);
                        if v___x_540_ == 0 {
                            v___x_541_ = leanh::lean_unsigned_to_nat(1);
                            v___x_542_ = lean_nat_sub(v_needlePos_516_, v___x_541_);
                            leanh::lean_dec(v_needlePos_516_);
                            v_newNeedlePos_543_ =
                                lean_array_fget_borrowed(v_table_514_, v___x_542_);
                            leanh::lean_dec(v___x_542_);
                            v___x_544_ = lean_nat_dec_eq(v_newNeedlePos_543_, v___x_539_);
                            if v___x_544_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_543_);
                                v_oldBasePos_545_ =
                                    l_String_Slice_pos_x21(v_s_465_, v_basePos_526_);
                                leanh::lean_dec(v_basePos_526_);
                                v___x_546_ = lean_nat_sub(v_stackPos_515_, v_newNeedlePos_543_);
                                v_newBasePos_547_ = l_String_Slice_pos_x21(v_s_465_, v___x_546_);
                                leanh::lean_dec(v___x_546_);
                                if v_isShared_519_ == 0 {
                                    leanh::lean_ctor_set(v___x_518_, 3, v_newNeedlePos_543_);
                                    v___x_549_ = v___x_518_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_550_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_550_,
                                        0,
                                        v_needle_513_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_550_,
                                        1,
                                        v_table_514_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_550_,
                                        2,
                                        v_stackPos_515_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_550_,
                                        3,
                                        v_newNeedlePos_543_,
                                    );
                                    v___x_549_ = v_reuseFailAlloc_550_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_basePos_551_ = l_String_Slice_pos_x21(v_s_465_, v_basePos_526_);
                                leanh::lean_dec(v_basePos_526_);
                                v_nextStackPos_552_ =
                                    l_String_Slice_posGE___redArg(v_s_465_, v_stackPos_515_);
                                leanh::lean_inc(v_nextStackPos_552_);
                                if v_isShared_519_ == 0 {
                                    leanh::lean_ctor_set(v___x_518_, 3, v___x_539_);
                                    leanh::lean_ctor_set(v___x_518_, 2, v_nextStackPos_552_);
                                    v___x_554_ = v___x_518_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_555_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_555_,
                                        0,
                                        v_needle_513_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_555_,
                                        1,
                                        v_table_514_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_555_,
                                        2,
                                        v_nextStackPos_552_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_555_,
                                        3,
                                        v___x_539_,
                                    );
                                    v___x_554_ = v_reuseFailAlloc_555_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_basePos_526_);
                            leanh::lean_dec(v_needlePos_516_);
                            v_basePos_556_ = l_String_Slice_pos_x21(v_s_465_, v_stackPos_515_);
                            v___x_557_ = leanh::lean_unsigned_to_nat(1);
                            v___x_558_ = lean_nat_add(v_stackPos_515_, v___x_557_);
                            leanh::lean_dec(v_stackPos_515_);
                            v_nextStackPos_559_ =
                                l_String_Slice_posGE___redArg(v_s_465_, v___x_558_);
                            leanh::lean_inc(v_nextStackPos_559_);
                            if v_isShared_519_ == 0 {
                                leanh::lean_ctor_set(v___x_518_, 3, v___x_539_);
                                leanh::lean_ctor_set(v___x_518_, 2, v_nextStackPos_559_);
                                v___x_561_ = v___x_518_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_562_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_562_,
                                    0,
                                    v_needle_513_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_562_, 1, v_table_514_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_562_,
                                    2,
                                    v_nextStackPos_559_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_562_, 3, v___x_539_);
                                v___x_561_ = v_reuseFailAlloc_562_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_basePos_526_);
                        v___x_563_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_564_ = lean_nat_add(v_stackPos_515_, v___x_563_);
                        leanh::lean_dec(v_stackPos_515_);
                        v_nextNeedlePos_565_ = lean_nat_add(v_needlePos_516_, v___x_563_);
                        leanh::lean_dec(v_needlePos_516_);
                        v___x_566_ = lean_nat_dec_eq(v_nextNeedlePos_565_, v___x_527_);
                        leanh::lean_dec(v___x_527_);
                        if v___x_566_ == 0 {
                            if v_isShared_519_ == 0 {
                                leanh::lean_ctor_set(v___x_518_, 3, v_nextNeedlePos_565_);
                                leanh::lean_ctor_set(v___x_518_, 2, v_nextStackPos_564_);
                                v___x_568_ = v___x_518_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_570_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_570_,
                                    0,
                                    v_needle_513_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_570_, 1, v_table_514_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_570_,
                                    2,
                                    v_nextStackPos_564_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_570_,
                                    3,
                                    v_nextNeedlePos_565_,
                                );
                                v___x_568_ = v_reuseFailAlloc_570_;
                                state = 11;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_nextNeedlePos_565_);
                            v___x_571_ = leanh::lean_unsigned_to_nat(0);
                            if v_isShared_519_ == 0 {
                                leanh::lean_ctor_set(v___x_518_, 3, v___x_571_);
                                leanh::lean_ctor_set(v___x_518_, 2, v_nextStackPos_564_);
                                v___x_573_ = v___x_518_;
                                state = 12;
                                continue;
                            } else {
                                v_reuseFailAlloc_574_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_574_,
                                    0,
                                    v_needle_513_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_574_, 1, v_table_514_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_574_,
                                    2,
                                    v_nextStackPos_564_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_574_, 3, v___x_571_);
                                v___x_573_ = v_reuseFailAlloc_574_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                v_it_470_ = v___x_549_;
                v_startPos_471_ = v_oldBasePos_545_;
                v_endPos_472_ = v_newBasePos_547_;
                state = 1;
                continue;
            }
            9 => {
                v_it_470_ = v___x_554_;
                v_startPos_471_ = v_basePos_551_;
                v_endPos_472_ = v_nextStackPos_552_;
                state = 1;
                continue;
            }
            10 => {
                v_it_470_ = v___x_561_;
                v_startPos_471_ = v_basePos_556_;
                v_endPos_472_ = v_nextStackPos_559_;
                state = 1;
                continue;
            }
            11 => {
                v_a_467_ = v___x_568_;
                state = 0;
                continue;
            }
            12 => {
                v_it_481_ = v___x_573_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg___boxed(
    mut v_s_576_: *mut leanh::LeanObject,
    mut v_replacement_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
    mut v_b_579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_576_, v_replacement_577_, v_a_578_, v_b_579_);
    leanh::lean_dec_ref(v_replacement_577_);
    return v_res_580_;
}
pub unsafe fn _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0;
    v___x_584_ = lean_string_utf8_byte_size(v___x_583_);
    return v___x_584_;
}
pub unsafe fn _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3()
-> u8 {
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    v___x_585_ = leanh::lean_unsigned_to_nat(0);
    v___x_586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
    v___x_587_ = lean_nat_dec_eq(v___x_586_, v___x_585_);
    return v___x_587_;
}
pub unsafe fn _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__2);
    v___x_589_ = leanh::lean_unsigned_to_nat(0);
    v___x_590_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__0;
    v___x_591_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_591_, 0, v___x_590_);
    leanh::lean_ctor_set(v___x_591_, 1, v___x_589_);
    leanh::lean_ctor_set(v___x_591_, 2, v___x_588_);
    return v___x_591_;
}
pub unsafe fn _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
    v___x_593_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_592_);
    return v___x_593_;
}
pub unsafe fn _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = leanh::lean_unsigned_to_nat(0);
    v___x_595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__5);
    v___x_596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__4);
    v___x_597_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_597_, 0, v___x_596_);
    leanh::lean_ctor_set(v___x_597_, 1, v___x_595_);
    leanh::lean_ctor_set(v___x_597_, 2, v___x_594_);
    leanh::lean_ctor_set(v___x_597_, 3, v___x_594_);
    return v___x_597_;
}
pub unsafe fn l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(
    mut v_s_600_: *mut leanh::LeanObject,
    mut v_replacement_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    v___x_602_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__1;
    v___x_603_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__3);
    if v___x_603_ == 0 {
        let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6_once), _init_l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__6);
        v___x_605_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_600_, v_replacement_601_, v___x_604_, v___x_602_);
        return v___x_605_;
    } else {
        let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_606_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___closed__7;
        v___x_607_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_600_, v_replacement_601_, v___x_606_, v___x_602_);
        return v___x_607_;
    }
}
pub unsafe fn l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg___boxed(
    mut v_s_608_: *mut leanh::LeanObject,
    mut v_replacement_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_610_ =
        l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(
            v_s_608_,
            v_replacement_609_,
        );
    leanh::lean_dec_ref(v_replacement_609_);
    return v_res_610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(
    mut v_leanSysroot_611_: *mut leanh::LeanObject,
    mut v_sz_612_: usize,
    mut v_i_613_: usize,
    mut v_bs_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_615_: u8 = 0;
    let mut v_v_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: usize = 0;
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_615_ = lean_usize_dec_lt(v_i_613_, v_sz_612_);
                if v___x_615_ == 0 {
                    return v_bs_614_;
                } else {
                    v_v_616_ = lean_array_uget(v_bs_614_, v_i_613_);
                    v___x_617_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_618_ = lean_array_uset(v_bs_614_, v_i_613_, v___x_617_);
                    v___x_619_ = lean_string_utf8_byte_size(v_v_616_);
                    v___x_620_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_620_, 0, v_v_616_);
                    leanh::lean_ctor_set(v___x_620_, 1, v___x_617_);
                    leanh::lean_ctor_set(v___x_620_, 2, v___x_619_);
                    v___x_621_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_620_, v_leanSysroot_611_);
                    v___x_622_ = 1usize;
                    v___x_623_ = lean_usize_add(v_i_613_, v___x_622_);
                    v___x_624_ = lean_array_uset(v_bs_x27_618_, v_i_613_, v___x_621_);
                    v_i_613_ = v___x_623_;
                    v_bs_614_ = v___x_624_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1___boxed(
    mut v_leanSysroot_626_: *mut leanh::LeanObject,
    mut v_sz_627_: *mut leanh::LeanObject,
    mut v_i_628_: *mut leanh::LeanObject,
    mut v_bs_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_630_: usize = 0;
    let mut v_i_boxed_631_: usize = 0;
    let mut v_res_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_630_ = leanh::lean_unbox_usize(v_sz_627_);
    leanh::lean_dec(v_sz_627_);
    v_i_boxed_631_ = leanh::lean_unbox_usize(v_i_628_);
    leanh::lean_dec(v_i_628_);
    v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_626_, v_sz_boxed_630_, v_i_boxed_631_, v_bs_629_);
    leanh::lean_dec_ref(v_leanSysroot_626_);
    return v_res_632_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = leanh::lean_box(0);
    v___x_634_ = lean_get_leanc_internal_flags(v___x_633_);
    return v___x_634_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__0_once),
        _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0,
    );
    v___x_636_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_635_);
    return v___x_636_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2() -> usize {
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_638_: usize = 0;
    v___x_637_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once),
        _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1,
    );
    v_sz_638_ = lean_array_size(v___x_637_);
    return v_sz_638_;
}
pub unsafe fn l_Lean_Compiler_FFI_getInternalCFlags(
    mut v_leanSysroot_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_641_: usize = 0;
    let mut v___x_642_: usize = 0;
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__1_once),
        _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1,
    );
    v_sz_641_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalCFlags___closed__2_once),
        _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2,
    );
    v___x_642_ = 0usize;
    v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_639_, v_sz_641_, v___x_642_, v___x_640_);
    return v___x_643_;
}
pub unsafe fn l_Lean_Compiler_FFI_getInternalCFlags___boxed(
    mut v_leanSysroot_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_645_ = l_Lean_Compiler_FFI_getInternalCFlags(v_leanSysroot_644_);
    leanh::lean_dec_ref(v_leanSysroot_644_);
    return v_res_645_;
}
pub unsafe fn l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(
    mut v_s_646_: *mut leanh::LeanObject,
    mut v_pattern_647_: *mut leanh::LeanObject,
    mut v_replacement_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ =
        l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(
            v_s_646_,
            v_replacement_648_,
        );
    return v___x_649_;
}
pub unsafe fn l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(
    mut v_s_650_: *mut leanh::LeanObject,
    mut v_pattern_651_: *mut leanh::LeanObject,
    mut v_replacement_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0(
        v_s_650_,
        v_pattern_651_,
        v_replacement_652_,
    );
    leanh::lean_dec_ref(v_replacement_652_);
    leanh::lean_dec_ref(v_pattern_651_);
    return v_res_653_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(
    mut v_s_654_: *mut leanh::LeanObject,
    mut v_replacement_655_: *mut leanh::LeanObject,
    mut v_inst_656_: *mut leanh::LeanObject,
    mut v_R_657_: *mut leanh::LeanObject,
    mut v_a_658_: *mut leanh::LeanObject,
    mut v_b_659_: *mut leanh::LeanObject,
    mut v_c_660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___redArg(v_s_654_, v_replacement_655_, v_a_658_, v_b_659_);
    return v___x_661_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0___boxed(
    mut v_s_662_: *mut leanh::LeanObject,
    mut v_replacement_663_: *mut leanh::LeanObject,
    mut v_inst_664_: *mut leanh::LeanObject,
    mut v_R_665_: *mut leanh::LeanObject,
    mut v_a_666_: *mut leanh::LeanObject,
    mut v_b_667_: *mut leanh::LeanObject,
    mut v_c_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0_spec__0(v_s_662_, v_replacement_663_, v_inst_664_, v_R_665_, v_a_666_, v_b_667_, v_c_668_);
    leanh::lean_dec_ref(v_replacement_663_);
    return v_res_669_;
}
pub unsafe fn l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(
    mut v_linkStatic_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_linkStatic_boxed_672_: u8 = 0;
    let mut v_res_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_linkStatic_boxed_672_ = (leanh::lean_unbox(v_linkStatic_671_) as u8);
    v_res_673_ = lean_get_linker_flags(v_linkStatic_boxed_672_);
    return v_res_673_;
}
pub unsafe fn l_Lean_Compiler_FFI_getLinkerFlags_x27(
    mut v_linkStatic_674_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = lean_get_linker_flags(v_linkStatic_674_);
    v___x_676_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(
    mut v_linkStatic_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_linkStatic_boxed_678_: u8 = 0;
    let mut v_res_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_linkStatic_boxed_678_ = (leanh::lean_unbox(v_linkStatic_677_) as u8);
    v_res_679_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_boxed_678_);
    return v_res_679_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_Compiler_FFI_getLinkerFlags___closed__0;
    v___x_684_ = leanh::lean_unsigned_to_nat(2);
    v___x_685_ = lean_mk_empty_array_with_capacity(v___x_684_);
    v___x_686_ = lean_array_push(v___x_685_, v___x_683_);
    return v___x_686_;
}
pub unsafe fn l_Lean_Compiler_FFI_getLinkerFlags(
    mut v_leanSysroot_687_: *mut leanh::LeanObject,
    mut v_linkStatic_688_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
    v___x_690_ = l_System_FilePath_join(v_leanSysroot_687_, v___x_689_);
    v___x_691_ = l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
    v___x_692_ = l_System_FilePath_join(v___x_690_, v___x_691_);
    v___x_693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getLinkerFlags___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getLinkerFlags___closed__3_once),
        _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3,
    );
    v___x_694_ = lean_array_push(v___x_693_, v___x_692_);
    v___x_695_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v_linkStatic_688_);
    v___x_696_ = l_Array_append___redArg(v___x_694_, v___x_695_);
    leanh::lean_dec_ref(v___x_695_);
    return v___x_696_;
}
pub unsafe fn l_Lean_Compiler_FFI_getLinkerFlags___boxed(
    mut v_leanSysroot_697_: *mut leanh::LeanObject,
    mut v_linkStatic_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_linkStatic_boxed_699_: u8 = 0;
    let mut v_res_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_linkStatic_boxed_699_ = (leanh::lean_unbox(v_linkStatic_698_) as u8);
    v_res_700_ = l_Lean_Compiler_FFI_getLinkerFlags(v_leanSysroot_697_, v_linkStatic_boxed_699_);
    return v_res_700_;
}
pub unsafe fn l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(
    mut v_a_00___x40___internal___hyg_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = lean_get_internal_linker_flags(v_a_00___x40___internal___hyg_702_);
    return v_res_703_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = leanh::lean_box(0);
    v___x_705_ = lean_get_internal_linker_flags(v___x_704_);
    return v___x_705_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0_once),
        _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0,
    );
    v___x_707_ = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(v___x_706_);
    return v___x_707_;
}
pub unsafe fn _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2() -> usize {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_709_: usize = 0;
    v___x_708_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once),
        _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1,
    );
    v_sz_709_ = lean_array_size(v___x_708_);
    return v_sz_709_;
}
pub unsafe fn l_Lean_Compiler_FFI_getInternalLinkerFlags(
    mut v_leanSysroot_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_712_: usize = 0;
    let mut v___x_713_: usize = 0;
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1_once),
        _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1,
    );
    v_sz_712_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2_once),
        _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2,
    );
    v___x_713_ = 0usize;
    v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_FFI_getInternalCFlags_spec__1(v_leanSysroot_710_, v_sz_712_, v___x_713_, v___x_711_);
    return v___x_714_;
}
pub unsafe fn l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(
    mut v_leanSysroot_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_leanSysroot_715_);
    leanh::lean_dec_ref(v_leanSysroot_715_);
    return v_res_716_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_FFI(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_FFI_getCFlags_x27 = _init_l_Lean_Compiler_FFI_getCFlags_x27();
    leanh::lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_FFI(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_FFI(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_FFI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_FFI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_FFI(builtin);
}