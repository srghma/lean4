// Lean compiler output
// Module: Lean.Server.FileWorker.ExampleHover
// Imports: Lean.Elab.Do
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_append, lean_string_memcmp,
    lean_string_push, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Lean::Elab::Do::{initialize_Lean_Elab_Do, runtime_initialize_Lean_Elab_Do};
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [45, 45, 32, 0]};
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [96, 96, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 117, 116, 112, 117, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(
    mut v_upperBound_400_: *mut crate::leanh::LeanObject,
    mut v_line_401_: *mut crate::leanh::LeanObject,
    mut v_a_402_: *mut crate::leanh::LeanObject,
    mut v_b_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: u8 = 0;
    let mut v_snd_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_408_: u8 = 0;
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: u32 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: u32 = 0;
    let mut v___x_419_: u8 = 0;
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_426_: u8 = 0;
    let mut v_unused_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_404_ = lean_nat_dec_lt(v_a_402_, v_upperBound_400_);
                if v___x_404_ == 0 {
                    crate::leanh::lean_dec(v_a_402_);
                    crate::leanh::lean_dec_ref(v_line_401_);
                    return v_b_403_;
                } else {
                    v_snd_405_ = crate::leanh::lean_ctor_get(v_b_403_, 1);
                    v_isSharedCheck_426_ = (!crate::leanh::lean_is_exclusive(v_b_403_)) as u8;
                    if v_isSharedCheck_426_ == 0 {
                        v_unused_427_ = crate::leanh::lean_ctor_get(v_b_403_, 0);
                        crate::leanh::lean_dec(v_unused_427_);
                        v___x_407_ = v_b_403_;
                        v_isShared_408_ = v_isSharedCheck_426_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_405_);
                        crate::leanh::lean_dec(v_b_403_);
                        v___x_407_ = crate::leanh::lean_box(0);
                        v_isShared_408_ = v_isSharedCheck_426_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_414_ = lean_string_utf8_byte_size(v_line_401_);
                v___x_415_ = lean_nat_dec_eq(v_snd_405_, v___x_414_);
                if v___x_415_ == 0 {
                    if v___x_404_ == 0 {
                        crate::leanh::lean_dec(v_a_402_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_407_);
                        v___x_416_ = 32;
                        v___x_417_ = crate::leanh::lean_box(0);
                        v___x_418_ = lean_string_utf8_get_fast(v_line_401_, v_snd_405_);
                        v___x_419_ = lean_uint32_dec_eq(v___x_418_, v___x_416_);
                        if v___x_419_ == 0 {
                            crate::leanh::lean_dec(v_a_402_);
                            crate::leanh::lean_dec_ref(v_line_401_);
                            v___x_420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_420_, 0, v___x_417_);
                            crate::leanh::lean_ctor_set(v___x_420_, 1, v_snd_405_);
                            return v___x_420_;
                        } else {
                            v___x_421_ = lean_string_utf8_next_fast(v_line_401_, v_snd_405_);
                            crate::leanh::lean_dec(v_snd_405_);
                            v___x_422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_417_);
                            crate::leanh::lean_ctor_set(v___x_422_, 1, v___x_421_);
                            v___x_423_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_424_ = lean_nat_add(v_a_402_, v___x_423_);
                            crate::leanh::lean_dec(v_a_402_);
                            v_a_402_ = v___x_424_;
                            v_b_403_ = v___x_422_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_402_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_410_, 0, v_line_401_);
                if v_isShared_408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_407_, 0, v___x_410_);
                    v___x_412_ = v___x_407_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_413_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_413_, 1, v_snd_405_);
                    v___x_412_ = v_reuseFailAlloc_413_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg___boxed(
    mut v_upperBound_428_: *mut crate::leanh::LeanObject,
    mut v_line_429_: *mut crate::leanh::LeanObject,
    mut v_a_430_: *mut crate::leanh::LeanObject,
    mut v_b_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_432_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_428_, v_line_429_, v_a_430_, v_b_431_);
    crate::leanh::lean_dec(v_upperBound_428_);
    return v_res_432_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(
    mut v_x_433_: *mut crate::leanh::LeanObject,
    mut v_x_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_436_: u8 = 0;
    let mut v___x_437_: u32 = 0;
    let mut v_one_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_435_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_436_ = lean_nat_dec_eq(v_x_433_, v_zero_435_);
                if v_isZero_436_ == 1 {
                    crate::leanh::lean_dec(v_x_433_);
                    return v_x_434_;
                } else {
                    v___x_437_ = 32;
                    v_one_438_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_439_ = lean_nat_sub(v_x_433_, v_one_438_);
                    crate::leanh::lean_dec(v_x_433_);
                    v___x_440_ = lean_string_push(v_x_434_, v___x_437_);
                    v_x_433_ = v_n_439_;
                    v_x_434_ = v___x_440_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(
    mut v_s_442_: *mut crate::leanh::LeanObject,
    mut v_pos_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: u32 = 0;
    let mut v___x_452_: u32 = 0;
    let mut v___x_453_: u8 = 0;
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_444_ = crate::leanh::lean_ctor_get(v_s_442_, 0);
                v_startInclusive_445_ = crate::leanh::lean_ctor_get(v_s_442_, 1);
                v_endExclusive_446_ = crate::leanh::lean_ctor_get(v_s_442_, 2);
                v___x_447_ = lean_nat_add(v_startInclusive_445_, v_pos_443_);
                v___x_448_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_449_ = lean_nat_sub(v_endExclusive_446_, v___x_447_);
                v___x_450_ = lean_nat_dec_eq(v___x_448_, v___x_449_);
                crate::leanh::lean_dec(v___x_449_);
                if v___x_450_ == 0 {
                    v___x_451_ = 32;
                    v___x_452_ = lean_string_utf8_get_fast(v_str_444_, v___x_447_);
                    v___x_453_ = lean_uint32_dec_eq(v___x_452_, v___x_451_);
                    if v___x_453_ == 0 {
                        crate::leanh::lean_dec(v___x_447_);
                        return v_pos_443_;
                    } else {
                        v___x_454_ = lean_string_utf8_next_fast(v_str_444_, v___x_447_);
                        v___x_455_ = lean_nat_sub(v___x_454_, v___x_447_);
                        crate::leanh::lean_dec(v___x_447_);
                        v___x_456_ = lean_nat_add(v_pos_443_, v___x_455_);
                        crate::leanh::lean_dec(v___x_455_);
                        v___x_457_ = lean_nat_dec_lt(v_pos_443_, v___x_456_);
                        if v___x_457_ == 0 {
                            crate::leanh::lean_dec(v___x_456_);
                            return v_pos_443_;
                        } else {
                            crate::leanh::lean_dec(v_pos_443_);
                            v_pos_443_ = v___x_456_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_447_);
                    return v_pos_443_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1___boxed(
    mut v_s_459_: *mut crate::leanh::LeanObject,
    mut v_pos_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v_s_459_, v_pos_460_);
    crate::leanh::lean_dec_ref(v_s_459_);
    return v_res_461_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(
    mut v_indent_467_: *mut crate::leanh::LeanObject,
    mut v_line_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_iter_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__0;
    crate::leanh::lean_inc(v_indent_467_);
    v___x_470_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__0(v_indent_467_, v___x_469_);
    v_iter_471_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_472_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__1;
    crate::leanh::lean_inc_ref(v_line_468_);
    v___x_473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_indent_467_, v_line_468_, v_iter_471_, v___x_472_);
    crate::leanh::lean_dec(v_indent_467_);
    v_fst_474_ = crate::leanh::lean_ctor_get(v___x_473_, 0);
    crate::leanh::lean_inc(v_fst_474_);
    if crate::leanh::lean_obj_tag(v_fst_474_) == 0 {
        let mut v_snd_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: u8 = 0;
        v_snd_475_ = crate::leanh::lean_ctor_get(v___x_473_, 1);
        crate::leanh::lean_inc_n(v_snd_475_, 2);
        crate::leanh::lean_dec_ref(v___x_473_);
        v___x_476_ = lean_string_utf8_byte_size(v_line_468_);
        crate::leanh::lean_inc_ref(v_line_468_);
        v___x_477_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_477_, 0, v_line_468_);
        crate::leanh::lean_ctor_set(v___x_477_, 1, v_snd_475_);
        crate::leanh::lean_ctor_set(v___x_477_, 2, v___x_476_);
        v___x_478_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__1(v___x_477_, v_iter_471_);
        crate::leanh::lean_dec_ref_known(v___x_477_, 3);
        v___x_479_ = lean_nat_sub(v___x_476_, v_snd_475_);
        v___x_480_ = lean_nat_dec_eq(v___x_478_, v___x_479_);
        crate::leanh::lean_dec(v___x_479_);
        crate::leanh::lean_dec(v___x_478_);
        if v___x_480_ == 0 {
            let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_481_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt___closed__2;
            v_s_482_ = lean_string_append(v___x_470_, v___x_481_);
            v___x_483_ = lean_string_utf8_extract(v_line_468_, v_snd_475_, v___x_476_);
            crate::leanh::lean_dec(v_snd_475_);
            crate::leanh::lean_dec_ref(v_line_468_);
            v___x_484_ = lean_string_append(v_s_482_, v___x_483_);
            crate::leanh::lean_dec_ref(v___x_483_);
            return v___x_484_;
        } else {
            crate::leanh::lean_dec(v_snd_475_);
            crate::leanh::lean_dec_ref(v___x_470_);
            return v_line_468_;
        }
    } else {
        let mut v_val_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_473_);
        crate::leanh::lean_dec_ref(v___x_470_);
        crate::leanh::lean_dec_ref(v_line_468_);
        v_val_485_ = crate::leanh::lean_ctor_get(v_fst_474_, 0);
        crate::leanh::lean_inc(v_val_485_);
        crate::leanh::lean_dec_ref_known(v_fst_474_, 1);
        return v_val_485_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(
    mut v_upperBound_486_: *mut crate::leanh::LeanObject,
    mut v_line_487_: *mut crate::leanh::LeanObject,
    mut v_inst_488_: *mut crate::leanh::LeanObject,
    mut v_R_489_: *mut crate::leanh::LeanObject,
    mut v_a_490_: *mut crate::leanh::LeanObject,
    mut v_b_491_: *mut crate::leanh::LeanObject,
    mut v_c_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___redArg(v_upperBound_486_, v_line_487_, v_a_490_, v_b_491_);
    return v___x_493_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2___boxed(
    mut v_upperBound_494_: *mut crate::leanh::LeanObject,
    mut v_line_495_: *mut crate::leanh::LeanObject,
    mut v_inst_496_: *mut crate::leanh::LeanObject,
    mut v_R_497_: *mut crate::leanh::LeanObject,
    mut v_a_498_: *mut crate::leanh::LeanObject,
    mut v_b_499_: *mut crate::leanh::LeanObject,
    mut v_c_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_501_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt_spec__2(v_upperBound_494_, v_line_495_, v_inst_496_, v_R_497_, v_a_498_, v_b_499_, v_c_500_);
    crate::leanh::lean_dec(v_upperBound_494_);
    return v_res_501_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(
    mut v_s_502_: *mut crate::leanh::LeanObject,
    mut v_a_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_508_: u8 = 0;
    let mut v_fst_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: u32 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u32 = 0;
    let mut v___x_519_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut v_isSharedCheck_543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_504_ = crate::leanh::lean_ctor_get(v_a_503_, 1);
                v_fst_505_ = crate::leanh::lean_ctor_get(v_a_503_, 0);
                v_isSharedCheck_543_ = (!crate::leanh::lean_is_exclusive(v_a_503_)) as u8;
                if v_isSharedCheck_543_ == 0 {
                    v___x_507_ = v_a_503_;
                    v_isShared_508_ = v_isSharedCheck_543_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_504_);
                    crate::leanh::lean_inc(v_fst_505_);
                    crate::leanh::lean_dec(v_a_503_);
                    v___x_507_ = crate::leanh::lean_box(0);
                    v_isShared_508_ = v_isSharedCheck_543_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_509_ = crate::leanh::lean_ctor_get(v_snd_504_, 0);
                v_snd_510_ = crate::leanh::lean_ctor_get(v_snd_504_, 1);
                v_isSharedCheck_542_ = (!crate::leanh::lean_is_exclusive(v_snd_504_)) as u8;
                if v_isSharedCheck_542_ == 0 {
                    v___x_512_ = v_snd_504_;
                    v_isShared_513_ = v_isSharedCheck_542_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_510_);
                    crate::leanh::lean_inc(v_fst_509_);
                    crate::leanh::lean_dec(v_snd_504_);
                    v___x_512_ = crate::leanh::lean_box(0);
                    v_isShared_513_ = v_isSharedCheck_542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_514_ = lean_string_utf8_byte_size(v_s_502_);
                v___x_515_ = lean_nat_dec_eq(v_snd_510_, v___x_514_);
                if v___x_515_ == 0 {
                    v___x_516_ = lean_string_utf8_get_fast(v_s_502_, v_snd_510_);
                    v___x_517_ = lean_string_utf8_next_fast(v_s_502_, v_snd_510_);
                    crate::leanh::lean_dec(v_snd_510_);
                    v___x_518_ = 10;
                    v___x_519_ = lean_uint32_dec_eq(v___x_516_, v___x_518_);
                    if v___x_519_ == 0 {
                        if v_isShared_513_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_512_, 1, v___x_517_);
                            v___x_521_ = v___x_512_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_526_, 0, v_fst_509_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_517_);
                            v___x_521_ = v_reuseFailAlloc_526_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_527_ = lean_string_utf8_extract(v_s_502_, v_fst_509_, v___x_517_);
                        crate::leanh::lean_dec(v_fst_509_);
                        v___x_528_ = lean_array_push(v_fst_505_, v___x_527_);
                        if v_isShared_513_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_512_, 1, v___x_517_);
                            crate::leanh::lean_ctor_set(v___x_512_, 0, v___x_517_);
                            v___x_530_ = v___x_512_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_517_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_517_);
                            v___x_530_ = v_reuseFailAlloc_535_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_513_ == 0 {
                        v___x_537_ = v___x_512_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_541_, 0, v_fst_509_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_541_, 1, v_snd_510_);
                        v___x_537_ = v_reuseFailAlloc_541_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_507_, 1, v___x_521_);
                    v___x_523_ = v___x_507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v_fst_505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_521_);
                    v___x_523_ = v_reuseFailAlloc_525_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_503_ = v___x_523_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_507_, 1, v___x_530_);
                    crate::leanh::lean_ctor_set(v___x_507_, 0, v___x_528_);
                    v___x_532_ = v___x_507_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_530_);
                    v___x_532_ = v_reuseFailAlloc_534_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_503_ = v___x_532_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_507_, 1, v___x_537_);
                    v___x_539_ = v___x_507_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
                    v___x_539_ = v_reuseFailAlloc_540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg___boxed(
    mut v_s_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_544_, v_a_545_);
    crate::leanh::lean_dec_ref(v_s_544_);
    return v_res_546_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(
    mut v_s_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    v___x_555_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___closed__2;
    v___x_556_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_554_, v___x_555_);
    v_snd_557_ = crate::leanh::lean_ctor_get(v___x_556_, 1);
    crate::leanh::lean_inc(v_snd_557_);
    v_fst_558_ = crate::leanh::lean_ctor_get(v___x_556_, 0);
    crate::leanh::lean_inc(v_fst_558_);
    crate::leanh::lean_dec_ref(v___x_556_);
    v_fst_559_ = crate::leanh::lean_ctor_get(v_snd_557_, 0);
    crate::leanh::lean_inc(v_fst_559_);
    v_snd_560_ = crate::leanh::lean_ctor_get(v_snd_557_, 1);
    crate::leanh::lean_inc(v_snd_560_);
    crate::leanh::lean_dec(v_snd_557_);
    v___x_561_ = lean_nat_dec_eq(v_snd_560_, v_fst_559_);
    if v___x_561_ == 0 {
        let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_562_ = lean_string_utf8_extract(v_s_554_, v_fst_559_, v_snd_560_);
        crate::leanh::lean_dec(v_snd_560_);
        crate::leanh::lean_dec(v_fst_559_);
        v___x_563_ = lean_array_push(v_fst_558_, v___x_562_);
        return v___x_563_;
    } else {
        crate::leanh::lean_dec(v_snd_560_);
        crate::leanh::lean_dec(v_fst_559_);
        return v_fst_558_;
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines___boxed(
    mut v_s_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ =
        l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(
            v_s_564_,
        );
    crate::leanh::lean_dec_ref(v_s_564_);
    return v_res_565_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(
    mut v_s_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_a_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___redArg(v_s_566_, v_a_568_);
    return v___x_569_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0___boxed(
    mut v_s_570_: *mut crate::leanh::LeanObject,
    mut v_inst_571_: *mut crate::leanh::LeanObject,
    mut v_a_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_573_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines_spec__0(v_s_570_, v_inst_571_, v_a_572_);
    crate::leanh::lean_dec_ref(v_s_570_);
    return v_res_573_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx(
    mut v_x_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_574_) {
        0 => {
            let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_575_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_575_;
        }
        1 => {
            let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_576_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_576_;
        }
        _ => {
            let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_577_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_577_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx___boxed(
    mut v_x_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorIdx(v_x_578_);
    crate::leanh::lean_dec(v_x_578_);
    return v_res_579_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(
    mut v_t_580_: *mut crate::leanh::LeanObject,
    mut v_k_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_580_) {
        0 => {
            return v_k_581_;
        }
        1 => {
            let mut v_ticks_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ticks_582_ = crate::leanh::lean_ctor_get(v_t_580_, 0);
            crate::leanh::lean_inc(v_ticks_582_);
            crate::leanh::lean_dec_ref_known(v_t_580_, 1);
            v___x_583_ = crate::leanh::lean_apply_1(v_k_581_, v_ticks_582_);
            return v___x_583_;
        }
        _ => {
            let mut v_indent_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ticks_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_indent_584_ = crate::leanh::lean_ctor_get(v_t_580_, 0);
            crate::leanh::lean_inc(v_indent_584_);
            v_ticks_585_ = crate::leanh::lean_ctor_get(v_t_580_, 1);
            crate::leanh::lean_inc(v_ticks_585_);
            crate::leanh::lean_dec_ref_known(v_t_580_, 2);
            v___x_586_ = crate::leanh::lean_apply_2(v_k_581_, v_indent_584_, v_ticks_585_);
            return v___x_586_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(
    mut v_motive_587_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_588_: *mut crate::leanh::LeanObject,
    mut v_t_589_: *mut crate::leanh::LeanObject,
    mut v_h_590_: *mut crate::leanh::LeanObject,
    mut v_k_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_589_, v_k_591_);
    return v___x_592_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___boxed(
    mut v_motive_593_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_594_: *mut crate::leanh::LeanObject,
    mut v_t_595_: *mut crate::leanh::LeanObject,
    mut v_h_596_: *mut crate::leanh::LeanObject,
    mut v_k_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim(v_motive_593_, v_ctorIdx_594_, v_t_595_, v_h_596_, v_k_597_);
    crate::leanh::lean_dec(v_ctorIdx_594_);
    return v_res_598_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim___redArg(
    mut v_t_599_: *mut crate::leanh::LeanObject,
    mut v_normal_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_599_, v_normal_600_);
    return v___x_601_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_normal_elim(
    mut v_motive_602_: *mut crate::leanh::LeanObject,
    mut v_t_603_: *mut crate::leanh::LeanObject,
    mut v_h_604_: *mut crate::leanh::LeanObject,
    mut v_normal_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_603_, v_normal_605_);
    return v___x_606_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim___redArg(
    mut v_t_607_: *mut crate::leanh::LeanObject,
    mut v_nonOutput_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_607_, v_nonOutput_608_);
    return v___x_609_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_nonOutput_elim(
    mut v_motive_610_: *mut crate::leanh::LeanObject,
    mut v_t_611_: *mut crate::leanh::LeanObject,
    mut v_h_612_: *mut crate::leanh::LeanObject,
    mut v_nonOutput_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_611_, v_nonOutput_613_);
    return v___x_614_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim___redArg(
    mut v_t_615_: *mut crate::leanh::LeanObject,
    mut v_output_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_617_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_615_, v_output_616_);
    return v___x_617_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_output_elim(
    mut v_motive_618_: *mut crate::leanh::LeanObject,
    mut v_t_619_: *mut crate::leanh::LeanObject,
    mut v_h_620_: *mut crate::leanh::LeanObject,
    mut v_output_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_RWState_ctorElim___redArg(v_t_619_, v_output_621_);
    return v___x_622_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(
    mut v_s_623_: *mut crate::leanh::LeanObject,
    mut v_pos_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: u32 = 0;
    let mut v___x_633_: u32 = 0;
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_625_ = crate::leanh::lean_ctor_get(v_s_623_, 0);
                v_startInclusive_626_ = crate::leanh::lean_ctor_get(v_s_623_, 1);
                v_endExclusive_627_ = crate::leanh::lean_ctor_get(v_s_623_, 2);
                v___x_628_ = lean_nat_add(v_startInclusive_626_, v_pos_624_);
                v___x_629_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_630_ = lean_nat_sub(v_endExclusive_627_, v___x_628_);
                v___x_631_ = lean_nat_dec_eq(v___x_629_, v___x_630_);
                crate::leanh::lean_dec(v___x_630_);
                if v___x_631_ == 0 {
                    v___x_632_ = lean_string_utf8_get_fast(v_str_625_, v___x_628_);
                    v___x_633_ = 96;
                    v___x_634_ = lean_uint32_dec_eq(v___x_632_, v___x_633_);
                    if v___x_634_ == 0 {
                        crate::leanh::lean_dec(v___x_628_);
                        return v_pos_624_;
                    } else {
                        v___x_635_ = lean_string_utf8_next_fast(v_str_625_, v___x_628_);
                        v___x_636_ = lean_nat_sub(v___x_635_, v___x_628_);
                        crate::leanh::lean_dec(v___x_628_);
                        v___x_637_ = lean_nat_add(v_pos_624_, v___x_636_);
                        crate::leanh::lean_dec(v___x_636_);
                        v___x_638_ = lean_nat_dec_lt(v_pos_624_, v___x_637_);
                        if v___x_638_ == 0 {
                            crate::leanh::lean_dec(v___x_637_);
                            return v_pos_624_;
                        } else {
                            crate::leanh::lean_dec(v_pos_624_);
                            v_pos_624_ = v___x_637_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_628_);
                    return v_pos_624_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2___boxed(
    mut v_s_640_: *mut crate::leanh::LeanObject,
    mut v_pos_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ =
        l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(
            v_s_640_, v_pos_641_,
        );
    crate::leanh::lean_dec_ref(v_s_640_);
    return v_res_642_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(
    mut v_s_643_: *mut crate::leanh::LeanObject,
    mut v_pos_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___y_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: u32 = 0;
    let mut v___y_662_: u8 = 0;
    let mut v___x_663_: u32 = 0;
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: u32 = 0;
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: u32 = 0;
    let mut v___x_668_: u8 = 0;
    let mut v___x_669_: u32 = 0;
    let mut v___x_670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_645_ = crate::leanh::lean_ctor_get(v_s_643_, 0);
                v_startInclusive_646_ = crate::leanh::lean_ctor_get(v_s_643_, 1);
                v_endExclusive_647_ = crate::leanh::lean_ctor_get(v_s_643_, 2);
                v___x_648_ = lean_nat_add(v_startInclusive_646_, v_pos_644_);
                v___x_657_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_658_ = lean_nat_sub(v_endExclusive_647_, v___x_648_);
                v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
                crate::leanh::lean_dec(v___x_658_);
                if v___x_659_ == 0 {
                    v___x_660_ = lean_string_utf8_get_fast(v_str_645_, v___x_648_);
                    v___x_667_ = 32;
                    v___x_668_ = lean_uint32_dec_eq(v___x_660_, v___x_667_);
                    if v___x_668_ == 0 {
                        v___x_669_ = 9;
                        v___x_670_ = lean_uint32_dec_eq(v___x_660_, v___x_669_);
                        v___y_662_ = v___x_670_;
                        state = 3;
                        continue;
                    } else {
                        v___y_662_ = v___x_668_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_648_);
                    return v_pos_644_;
                }
            }
            1 => {
                v___x_650_ = lean_string_utf8_next_fast(v_str_645_, v___x_648_);
                v___x_651_ = lean_nat_sub(v___x_650_, v___x_648_);
                crate::leanh::lean_dec(v___x_648_);
                v___x_652_ = lean_nat_add(v_pos_644_, v___x_651_);
                crate::leanh::lean_dec(v___x_651_);
                v___x_653_ = lean_nat_dec_lt(v_pos_644_, v___x_652_);
                if v___x_653_ == 0 {
                    crate::leanh::lean_dec(v___x_652_);
                    return v_pos_644_;
                } else {
                    crate::leanh::lean_dec(v_pos_644_);
                    v_pos_644_ = v___x_652_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_656_ == 0 {
                    crate::leanh::lean_dec(v___x_648_);
                    return v_pos_644_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_662_ == 0 {
                    v___x_663_ = 13;
                    v___x_664_ = lean_uint32_dec_eq(v___x_660_, v___x_663_);
                    if v___x_664_ == 0 {
                        v___x_665_ = 10;
                        v___x_666_ = lean_uint32_dec_eq(v___x_660_, v___x_665_);
                        v___y_656_ = v___x_666_;
                        state = 2;
                        continue;
                    } else {
                        v___y_656_ = v___x_664_;
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
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0___boxed(
    mut v_s_671_: *mut crate::leanh::LeanObject,
    mut v_pos_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ =
        l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(
            v_s_671_, v_pos_672_,
        );
    crate::leanh::lean_dec_ref(v_s_671_);
    return v_res_673_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(
    mut v_s_674_: *mut crate::leanh::LeanObject,
    mut v_pos_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: u32 = 0;
    let mut v___x_684_: u32 = 0;
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_676_ = crate::leanh::lean_ctor_get(v_s_674_, 0);
                v_startInclusive_677_ = crate::leanh::lean_ctor_get(v_s_674_, 1);
                v_endExclusive_678_ = crate::leanh::lean_ctor_get(v_s_674_, 2);
                v___x_679_ = lean_nat_add(v_startInclusive_677_, v_pos_675_);
                v___x_680_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_681_ = lean_nat_sub(v_endExclusive_678_, v___x_679_);
                v___x_682_ = lean_nat_dec_eq(v___x_680_, v___x_681_);
                crate::leanh::lean_dec(v___x_681_);
                if v___x_682_ == 0 {
                    v___x_683_ = lean_string_utf8_get_fast(v_str_676_, v___x_679_);
                    v___x_684_ = 32;
                    v___x_685_ = lean_uint32_dec_eq(v___x_683_, v___x_684_);
                    if v___x_685_ == 0 {
                        crate::leanh::lean_dec(v___x_679_);
                        return v_pos_675_;
                    } else {
                        v___x_686_ = lean_string_utf8_next_fast(v_str_676_, v___x_679_);
                        v___x_687_ = lean_nat_sub(v___x_686_, v___x_679_);
                        crate::leanh::lean_dec(v___x_679_);
                        v___x_688_ = lean_nat_add(v_pos_675_, v___x_687_);
                        crate::leanh::lean_dec(v___x_687_);
                        v___x_689_ = lean_nat_dec_lt(v_pos_675_, v___x_688_);
                        if v___x_689_ == 0 {
                            crate::leanh::lean_dec(v___x_688_);
                            return v_pos_675_;
                        } else {
                            crate::leanh::lean_dec(v_pos_675_);
                            v_pos_675_ = v___x_688_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_679_);
                    return v_pos_675_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1___boxed(
    mut v_s_691_: *mut crate::leanh::LeanObject,
    mut v_pos_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_693_ =
        l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(
            v_s_691_, v_pos_692_,
        );
    crate::leanh::lean_dec_ref(v_s_691_);
    return v_res_693_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0;
    v___x_696_ = lean_string_utf8_byte_size(v___x_695_);
    return v___x_696_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__2;
    v___x_699_ = lean_string_utf8_byte_size(v___x_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(
    mut v_as_700_: *mut crate::leanh::LeanObject,
    mut v_sz_701_: usize,
    mut v_i_702_: usize,
    mut v_b_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: usize = 0;
    let mut v___x_707_: usize = 0;
    let mut v___x_709_: u8 = 0;
    let mut v_fst_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_714_: u8 = 0;
    let mut v_a_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inOutput_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inOutput_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: u8 = 0;
    let mut v_inOutput_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v___x_759_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ticks_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut v_indent_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ticks_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_771_: u8 = 0;
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_776_: u8 = 0;
    let mut v_unused_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_709_ = lean_usize_dec_lt(v_i_702_, v_sz_701_);
                if v___x_709_ == 0 {
                    return v_b_703_;
                } else {
                    v_fst_710_ = crate::leanh::lean_ctor_get(v_b_703_, 0);
                    v_snd_711_ = crate::leanh::lean_ctor_get(v_b_703_, 1);
                    v_isSharedCheck_779_ = (!crate::leanh::lean_is_exclusive(v_b_703_)) as u8;
                    if v_isSharedCheck_779_ == 0 {
                        v___x_713_ = v_b_703_;
                        v_isShared_714_ = v_isSharedCheck_779_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_711_);
                        crate::leanh::lean_inc(v_fst_710_);
                        crate::leanh::lean_dec(v_b_703_);
                        v___x_713_ = crate::leanh::lean_box(0);
                        v_isShared_714_ = v_isSharedCheck_779_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_706_ = 1usize;
                v___x_707_ = lean_usize_add(v_i_702_, v___x_706_);
                v_i_702_ = v___x_707_;
                v_b_703_ = v_a_705_;
                state = 0;
                continue;
            }
            2 => {
                v_a_715_ = lean_array_uget_borrowed(v_as_700_, v_i_702_);
                v___x_735_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_736_ = lean_string_utf8_byte_size(v_a_715_);
                crate::leanh::lean_inc(v_a_715_);
                v___x_737_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_737_, 0, v_a_715_);
                crate::leanh::lean_ctor_set(v___x_737_, 1, v___x_735_);
                crate::leanh::lean_ctor_set(v___x_737_, 2, v___x_736_);
                v___x_738_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__0(v___x_737_, v___x_735_);
                v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__0;
                v___x_740_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__1);
                v___x_741_ = lean_nat_sub(v___x_736_, v___x_738_);
                v___x_742_ = lean_nat_dec_le(v___x_740_, v___x_741_);
                crate::leanh::lean_dec(v___x_741_);
                if v___x_742_ == 0 {
                    crate::leanh::lean_dec(v___x_738_);
                    crate::leanh::lean_dec_ref_known(v___x_737_, 3);
                    state = 3;
                    continue;
                } else {
                    v___x_743_ = lean_string_memcmp(
                        v_a_715_, v___x_739_, v___x_738_, v___x_735_, v___x_740_,
                    );
                    if v___x_743_ == 0 {
                        crate::leanh::lean_dec(v___x_738_);
                        crate::leanh::lean_dec_ref_known(v___x_737_, 3);
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_713_);
                        v_inOutput_744_ = crate::leanh::lean_box(0);
                        v___x_745_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_737_, v___x_735_);
                        crate::leanh::lean_dec_ref_known(v___x_737_, 3);
                        crate::leanh::lean_inc(v___x_738_);
                        crate::leanh::lean_inc(v_a_715_);
                        v___x_746_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_746_, 0, v_a_715_);
                        crate::leanh::lean_ctor_set(v___x_746_, 1, v___x_738_);
                        crate::leanh::lean_ctor_set(v___x_746_, 2, v___x_736_);
                        v___x_747_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__2(v___x_746_, v___x_735_);
                        crate::leanh::lean_dec_ref_known(v___x_746_, 3);
                        v___x_748_ = lean_nat_add(v___x_738_, v___x_747_);
                        crate::leanh::lean_dec(v___x_747_);
                        v___x_749_ = lean_nat_sub(v___x_748_, v___x_738_);
                        crate::leanh::lean_dec(v___x_738_);
                        match crate::leanh::lean_obj_tag(v_snd_711_) {
                            0 => {
                                crate::leanh::lean_inc(v___x_748_);
                                crate::leanh::lean_inc(v_a_715_);
                                v___x_752_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_752_, 0, v_a_715_);
                                crate::leanh::lean_ctor_set(v___x_752_, 1, v___x_748_);
                                crate::leanh::lean_ctor_set(v___x_752_, 2, v___x_736_);
                                v___x_753_ = l_String_Slice_Pos_skipWhile___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__1(v___x_752_, v___x_735_);
                                crate::leanh::lean_dec_ref_known(v___x_752_, 3);
                                v___x_754_ = lean_nat_add(v___x_748_, v___x_753_);
                                crate::leanh::lean_dec(v___x_753_);
                                crate::leanh::lean_dec(v___x_748_);
                                v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__2;
                                v___x_756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___closed__3);
                                v___x_757_ = lean_nat_sub(v___x_736_, v___x_754_);
                                v___x_758_ = lean_nat_dec_le(v___x_756_, v___x_757_);
                                crate::leanh::lean_dec(v___x_757_);
                                if v___x_758_ == 0 {
                                    crate::leanh::lean_dec(v___x_754_);
                                    crate::leanh::lean_dec(v___x_745_);
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_759_ = lean_string_memcmp(
                                        v_a_715_, v___x_755_, v___x_754_, v___x_735_, v___x_756_,
                                    );
                                    crate::leanh::lean_dec(v___x_754_);
                                    if v___x_759_ == 0 {
                                        crate::leanh::lean_dec(v___x_745_);
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_760_ =
                                            crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_760_, 0, v___x_745_);
                                        crate::leanh::lean_ctor_set(v___x_760_, 1, v___x_749_);
                                        v_inOutput_728_ = v___x_760_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                            1 => {
                                crate::leanh::lean_dec(v___x_748_);
                                crate::leanh::lean_dec(v___x_745_);
                                v_ticks_761_ = crate::leanh::lean_ctor_get(v_snd_711_, 0);
                                v___x_762_ = lean_nat_dec_eq(v_ticks_761_, v___x_749_);
                                crate::leanh::lean_dec(v___x_749_);
                                if v___x_762_ == 0 {
                                    v_inOutput_732_ = v_snd_711_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_snd_711_, 1);
                                    v_inOutput_732_ = v_inOutput_744_;
                                    state = 7;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec(v___x_748_);
                                crate::leanh::lean_dec(v___x_745_);
                                v_indent_763_ = crate::leanh::lean_ctor_get(v_snd_711_, 0);
                                v_ticks_764_ = crate::leanh::lean_ctor_get(v_snd_711_, 1);
                                v___x_765_ = lean_nat_dec_eq(v_ticks_764_, v___x_749_);
                                crate::leanh::lean_dec(v___x_749_);
                                if v___x_765_ == 0 {
                                    crate::leanh::lean_inc(v_a_715_);
                                    crate::leanh::lean_inc(v_indent_763_);
                                    v___x_766_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_763_, v_a_715_);
                                    v___x_767_ = lean_string_append(v_fst_710_, v___x_766_);
                                    crate::leanh::lean_dec_ref(v___x_766_);
                                    v___x_768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_767_);
                                    crate::leanh::lean_ctor_set(v___x_768_, 1, v_snd_711_);
                                    v_a_705_ = v___x_768_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_isSharedCheck_776_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_711_)) as u8;
                                    if v_isSharedCheck_776_ == 0 {
                                        v_unused_777_ = crate::leanh::lean_ctor_get(v_snd_711_, 1);
                                        crate::leanh::lean_dec(v_unused_777_);
                                        v_unused_778_ = crate::leanh::lean_ctor_get(v_snd_711_, 0);
                                        crate::leanh::lean_dec(v_unused_778_);
                                        v___x_770_ = v_snd_711_;
                                        v_isShared_771_ = v_isSharedCheck_776_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_snd_711_);
                                        v___x_770_ = crate::leanh::lean_box(0);
                                        v_isShared_771_ = v_isSharedCheck_776_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_snd_711_) == 2 {
                    v_indent_717_ = crate::leanh::lean_ctor_get(v_snd_711_, 0);
                    crate::leanh::lean_inc(v_a_715_);
                    crate::leanh::lean_inc(v_indent_717_);
                    v___x_718_ = l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_addCommentAt(v_indent_717_, v_a_715_);
                    v___x_719_ = lean_string_append(v_fst_710_, v___x_718_);
                    crate::leanh::lean_dec_ref(v___x_718_);
                    if v_isShared_714_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_719_);
                        v___x_721_ = v___x_713_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_722_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_722_, 1, v_snd_711_);
                        v___x_721_ = v_reuseFailAlloc_722_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_723_ = lean_string_append(v_fst_710_, v_a_715_);
                    if v_isShared_714_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_723_);
                        v___x_725_ = v___x_713_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 1, v_snd_711_);
                        v___x_725_ = v_reuseFailAlloc_726_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_a_705_ = v___x_721_;
                state = 1;
                continue;
            }
            5 => {
                v_a_705_ = v___x_725_;
                state = 1;
                continue;
            }
            6 => {
                v___x_729_ = lean_string_append(v_fst_710_, v_a_715_);
                v___x_730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
                crate::leanh::lean_ctor_set(v___x_730_, 1, v_inOutput_728_);
                v_a_705_ = v___x_730_;
                state = 1;
                continue;
            }
            7 => {
                v___x_733_ = lean_string_append(v_fst_710_, v_a_715_);
                v___x_734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_734_, 0, v___x_733_);
                crate::leanh::lean_ctor_set(v___x_734_, 1, v_inOutput_732_);
                v_a_705_ = v___x_734_;
                state = 1;
                continue;
            }
            8 => {
                v___x_751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_751_, 0, v___x_749_);
                v_inOutput_728_ = v___x_751_;
                state = 6;
                continue;
            }
            9 => {
                v___x_772_ = lean_string_append(v_fst_710_, v_a_715_);
                if v_isShared_771_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_770_, 0);
                    crate::leanh::lean_ctor_set(v___x_770_, 1, v_inOutput_744_);
                    crate::leanh::lean_ctor_set(v___x_770_, 0, v___x_772_);
                    v___x_774_ = v___x_770_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_775_, 1, v_inOutput_744_);
                    v___x_774_ = v_reuseFailAlloc_775_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_705_ = v___x_774_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3___boxed(
    mut v_as_780_: *mut crate::leanh::LeanObject,
    mut v_sz_781_: *mut crate::leanh::LeanObject,
    mut v_i_782_: *mut crate::leanh::LeanObject,
    mut v_b_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_784_: usize = 0;
    let mut v_i_boxed_785_: usize = 0;
    let mut v_res_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_784_ = crate::leanh::lean_unbox_usize(v_sz_781_);
    crate::leanh::lean_dec(v_sz_781_);
    v_i_boxed_785_ = crate::leanh::lean_unbox_usize(v_i_782_);
    crate::leanh::lean_dec(v_i_782_);
    v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_as_780_, v_sz_boxed_784_, v_i_boxed_785_, v_b_783_);
    crate::leanh::lean_dec_ref(v_as_780_);
    return v_res_786_;
}
pub unsafe fn l_Lean_Server_FileWorker_Hover_rewriteExamples(
    mut v_docstring_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lines_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_793_: usize = 0;
    let mut v___x_794_: usize = 0;
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lines_791_ =
        l___private_Lean_Server_FileWorker_ExampleHover_0__Lean_Server_FileWorker_Hover_lines(
            v_docstring_790_,
        );
    v___x_792_ = l_Lean_Server_FileWorker_Hover_rewriteExamples___closed__0;
    v_sz_793_ = lean_array_size(v_lines_791_);
    v___x_794_ = 0usize;
    v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_Hover_rewriteExamples_spec__3(v_lines_791_, v_sz_793_, v___x_794_, v___x_792_);
    crate::leanh::lean_dec_ref(v_lines_791_);
    v_fst_796_ = crate::leanh::lean_ctor_get(v___x_795_, 0);
    crate::leanh::lean_inc(v_fst_796_);
    crate::leanh::lean_dec_ref(v___x_795_);
    return v_fst_796_;
}
pub unsafe fn l_Lean_Server_FileWorker_Hover_rewriteExamples___boxed(
    mut v_docstring_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Lean_Server_FileWorker_Hover_rewriteExamples(v_docstring_797_);
    crate::leanh::lean_dec_ref(v_docstring_797_);
    return v_res_798_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_ExampleHover(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_ExampleHover(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_FileWorker_ExampleHover(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_ExampleHover(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_ExampleHover(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_ExampleHover(builtin);
}
