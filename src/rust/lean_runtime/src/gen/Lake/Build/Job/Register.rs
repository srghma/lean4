// Lean compiler output
// Module: Lake.Build.Job.Register
// Imports: Lake.Build.Fetch
use crate::r#gen::Init::Data::Array::Basic::l_Array_shrink___redArg;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Prelude::{l_Array_extract___redArg, l_ByteArray_empty};
use crate::r#gen::Init::System::IO::l_IO_FS_Stream_ofBuffer;
use crate::r#gen::Init::System::ST::l_ST_Prim_Ref_modifyUnsafe___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Build::Fetch::{
    initialize_Lake_Build_Fetch, runtime_initialize_Lake_Build_Fetch,
};
use crate::r#gen::Lake::Build::Job::Basic::{
    l_Lake_Job_toOpaque___redArg, l_Lake_JobResult_prependLog___redArg,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_validate_utf8;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_from_utf8_unchecked,
    lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::IO::{lean_get_set_stderr, lean_get_set_stdout};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lake_JobState_renew___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_JobState_renew___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_JobState_renew___closed__0_value) as *mut LeanObject;
pub static l_Lake_Job_renew___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Job_renew___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Job_renew___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Job_renew___redArg___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00Lake_ensureJob_spec__0___closed__0_value: LeanStringObject<1> =
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
static mut l_panic___at___00Lake_ensureJob_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lake_ensureJob_spec__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_ensureJob___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ensureJob___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_ensureJob___redArg___closed__1_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lake_ensureJob___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lake_ensureJob___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ensureJob___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_ensureJob___redArg___closed__3_value: LeanStringObject<16> = LeanStringObject {
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
        115, 116, 100, 111, 117, 116, 47, 115, 116, 100, 101, 114, 114, 58, 10, 0,
    ],
};
static mut l_Lake_ensureJob___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_ensureJob___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97, 115,
        105, 99, 0,
    ],
};
static mut l_Lake_ensureJob___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_ensureJob___redArg___closed__5_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0,
    ],
};
static mut l_Lake_ensureJob___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_ensureJob___redArg___closed__6_value: LeanStringObject<21> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110, 103,
        0,
    ],
};
static mut l_Lake_ensureJob___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lake_ensureJob___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ensureJob___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lake_JobState_renew(mut v_s_572_: *mut LeanObject) -> *mut LeanObject {
    let mut v_trace_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v_caption_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_578_: u64 = 0;
    let mut v_mtime_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_593_: u8 = 0;
    let mut v_unused_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_595_: u8 = 0;
    let mut v_unused_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_597_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trace_573_ = lean_ctor_get(v_s_572_, 1);
                v_isSharedCheck_595_ = (!lean_is_exclusive(v_s_572_)) as u8;
                if v_isSharedCheck_595_ == 0 {
                    v_unused_596_ = lean_ctor_get(v_s_572_, 2);
                    lean_dec(v_unused_596_);
                    v_unused_597_ = lean_ctor_get(v_s_572_, 0);
                    lean_dec(v_unused_597_);
                    v___x_575_ = v_s_572_;
                    v_isShared_576_ = v_isSharedCheck_595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_trace_573_);
                    lean_dec(v_s_572_);
                    v___x_575_ = lean_box(0);
                    v_isShared_576_ = v_isSharedCheck_595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_caption_577_ = lean_ctor_get(v_trace_573_, 0);
                v_hash_578_ = lean_ctor_get_uint64(
                    v_trace_573_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_579_ = lean_ctor_get(v_trace_573_, 2);
                v_isSharedCheck_593_ = (!lean_is_exclusive(v_trace_573_)) as u8;
                if v_isSharedCheck_593_ == 0 {
                    v_unused_594_ = lean_ctor_get(v_trace_573_, 1);
                    lean_dec(v_unused_594_);
                    v___x_581_ = v_trace_573_;
                    v_isShared_582_ = v_isSharedCheck_593_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_mtime_579_);
                    lean_inc(v_caption_577_);
                    lean_dec(v_trace_573_);
                    v___x_581_ = lean_box(0);
                    v_isShared_582_ = v_isSharedCheck_593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_583_ = lean_unsigned_to_nat(0);
                v___x_584_ = l_Lake_JobState_renew___closed__0;
                v___x_585_ = 0;
                v___x_586_ = 0;
                if v_isShared_582_ == 0 {
                    lean_ctor_set(v___x_581_, 1, v___x_584_);
                    v___x_588_ = v___x_581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_592_, 0, v_caption_577_);
                    lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_584_);
                    lean_ctor_set(v_reuseFailAlloc_592_, 2, v_mtime_579_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_592_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_hash_578_,
                    );
                    v___x_588_ = v_reuseFailAlloc_592_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_576_ == 0 {
                    lean_ctor_set(v___x_575_, 2, v___x_583_);
                    lean_ctor_set(v___x_575_, 1, v___x_588_);
                    lean_ctor_set(v___x_575_, 0, v___x_584_);
                    v___x_590_ = v___x_575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_584_);
                    lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
                    lean_ctor_set(v_reuseFailAlloc_591_, 2, v___x_583_);
                    v___x_590_ = v_reuseFailAlloc_591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_590_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_585_,
                );
                lean_ctor_set_uint8(
                    v___x_590_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_586_,
                );
                return v___x_590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_renew___redArg___lam__0(mut v_x_598_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trace_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v_caption_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_609_: u64 = 0;
    let mut v_mtime_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_unused_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_629_: u8 = 0;
    let mut v_unused_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_unused_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v_trace_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v_caption_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_643_: u64 = 0;
    let mut v_mtime_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_unused_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_unused_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_unused_667_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_598_) == 0 {
                    v_a_599_ = lean_ctor_get(v_x_598_, 1);
                    lean_inc(v_a_599_);
                    v_trace_600_ = lean_ctor_get(v_a_599_, 1);
                    v_isSharedCheck_631_ = (!lean_is_exclusive(v_a_599_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v_unused_632_ = lean_ctor_get(v_a_599_, 2);
                        lean_dec(v_unused_632_);
                        v_unused_633_ = lean_ctor_get(v_a_599_, 0);
                        lean_dec(v_unused_633_);
                        v___x_602_ = v_a_599_;
                        v_isShared_603_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_trace_600_);
                        lean_dec(v_a_599_);
                        v___x_602_ = lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_634_ = lean_ctor_get(v_x_598_, 1);
                    v_isSharedCheck_666_ = (!lean_is_exclusive(v_x_598_)) as u8;
                    if v_isSharedCheck_666_ == 0 {
                        v_unused_667_ = lean_ctor_get(v_x_598_, 0);
                        lean_dec(v_unused_667_);
                        v___x_636_ = v_x_598_;
                        v_isShared_637_ = v_isSharedCheck_666_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_634_);
                        lean_dec(v_x_598_);
                        v___x_636_ = lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_666_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_a_604_ = lean_ctor_get(v_x_598_, 0);
                v_isSharedCheck_629_ = (!lean_is_exclusive(v_x_598_)) as u8;
                if v_isSharedCheck_629_ == 0 {
                    v_unused_630_ = lean_ctor_get(v_x_598_, 1);
                    lean_dec(v_unused_630_);
                    v___x_606_ = v_x_598_;
                    v_isShared_607_ = v_isSharedCheck_629_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_604_);
                    lean_dec(v_x_598_);
                    v___x_606_ = lean_box(0);
                    v_isShared_607_ = v_isSharedCheck_629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_caption_608_ = lean_ctor_get(v_trace_600_, 0);
                v_hash_609_ = lean_ctor_get_uint64(
                    v_trace_600_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_610_ = lean_ctor_get(v_trace_600_, 2);
                v_isSharedCheck_627_ = (!lean_is_exclusive(v_trace_600_)) as u8;
                if v_isSharedCheck_627_ == 0 {
                    v_unused_628_ = lean_ctor_get(v_trace_600_, 1);
                    lean_dec(v_unused_628_);
                    v___x_612_ = v_trace_600_;
                    v_isShared_613_ = v_isSharedCheck_627_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_mtime_610_);
                    lean_inc(v_caption_608_);
                    lean_dec(v_trace_600_);
                    v___x_612_ = lean_box(0);
                    v_isShared_613_ = v_isSharedCheck_627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_614_ = lean_unsigned_to_nat(0);
                v___x_615_ = l_Lake_JobState_renew___closed__0;
                v___x_616_ = 0;
                v___x_617_ = 0;
                if v_isShared_613_ == 0 {
                    lean_ctor_set(v___x_612_, 1, v___x_615_);
                    v___x_619_ = v___x_612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_626_, 0, v_caption_608_);
                    lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_615_);
                    lean_ctor_set(v_reuseFailAlloc_626_, 2, v_mtime_610_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_626_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_hash_609_,
                    );
                    v___x_619_ = v_reuseFailAlloc_626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_603_ == 0 {
                    lean_ctor_set(v___x_602_, 2, v___x_614_);
                    lean_ctor_set(v___x_602_, 1, v___x_619_);
                    lean_ctor_set(v___x_602_, 0, v___x_615_);
                    v___x_621_ = v___x_602_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_615_);
                    lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_619_);
                    lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_614_);
                    v___x_621_ = v_reuseFailAlloc_625_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_621_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_616_,
                );
                lean_ctor_set_uint8(
                    v___x_621_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_617_,
                );
                if v_isShared_607_ == 0 {
                    lean_ctor_set(v___x_606_, 1, v___x_621_);
                    v___x_623_ = v___x_606_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_604_);
                    lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
                    v___x_623_ = v_reuseFailAlloc_624_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_623_;
            }
            7 => {
                v_trace_638_ = lean_ctor_get(v_a_634_, 1);
                v_isSharedCheck_663_ = (!lean_is_exclusive(v_a_634_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v_unused_664_ = lean_ctor_get(v_a_634_, 2);
                    lean_dec(v_unused_664_);
                    v_unused_665_ = lean_ctor_get(v_a_634_, 0);
                    lean_dec(v_unused_665_);
                    v___x_640_ = v_a_634_;
                    v_isShared_641_ = v_isSharedCheck_663_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_trace_638_);
                    lean_dec(v_a_634_);
                    v___x_640_ = lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_663_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_caption_642_ = lean_ctor_get(v_trace_638_, 0);
                v_hash_643_ = lean_ctor_get_uint64(
                    v_trace_638_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_mtime_644_ = lean_ctor_get(v_trace_638_, 2);
                v_isSharedCheck_661_ = (!lean_is_exclusive(v_trace_638_)) as u8;
                if v_isSharedCheck_661_ == 0 {
                    v_unused_662_ = lean_ctor_get(v_trace_638_, 1);
                    lean_dec(v_unused_662_);
                    v___x_646_ = v_trace_638_;
                    v_isShared_647_ = v_isSharedCheck_661_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_mtime_644_);
                    lean_inc(v_caption_642_);
                    lean_dec(v_trace_638_);
                    v___x_646_ = lean_box(0);
                    v_isShared_647_ = v_isSharedCheck_661_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_648_ = lean_unsigned_to_nat(0);
                v___x_649_ = l_Lake_JobState_renew___closed__0;
                v___x_650_ = 0;
                v___x_651_ = 0;
                if v_isShared_647_ == 0 {
                    lean_ctor_set(v___x_646_, 1, v___x_649_);
                    v___x_653_ = v___x_646_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_660_, 0, v_caption_642_);
                    lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_649_);
                    lean_ctor_set(v_reuseFailAlloc_660_, 2, v_mtime_644_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_660_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_hash_643_,
                    );
                    v___x_653_ = v_reuseFailAlloc_660_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_641_ == 0 {
                    lean_ctor_set(v___x_640_, 2, v___x_648_);
                    lean_ctor_set(v___x_640_, 1, v___x_653_);
                    lean_ctor_set(v___x_640_, 0, v___x_649_);
                    v___x_655_ = v___x_640_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_649_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_653_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 2, v___x_648_);
                    v___x_655_ = v_reuseFailAlloc_659_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_ctor_set_uint8(
                    v___x_655_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_650_,
                );
                lean_ctor_set_uint8(
                    v___x_655_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_651_,
                );
                if v_isShared_637_ == 0 {
                    lean_ctor_set(v___x_636_, 1, v___x_655_);
                    lean_ctor_set(v___x_636_, 0, v___x_648_);
                    v___x_657_ = v___x_636_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_648_);
                    lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
                    v___x_657_ = v_reuseFailAlloc_658_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_renew___redArg(mut v_self_669_: *mut LeanObject) -> *mut LeanObject {
    let mut v_task_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optional_673_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___f_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_670_ = lean_ctor_get(v_self_669_, 0);
                v_kind_671_ = lean_ctor_get(v_self_669_, 1);
                v_caption_672_ = lean_ctor_get(v_self_669_, 2);
                v_optional_673_ = lean_ctor_get_uint8(
                    v_self_669_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_684_ = (!lean_is_exclusive(v_self_669_)) as u8;
                if v_isSharedCheck_684_ == 0 {
                    v___x_675_ = v_self_669_;
                    v_isShared_676_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_caption_672_);
                    lean_inc(v_kind_671_);
                    lean_inc(v_task_670_);
                    lean_dec(v_self_669_);
                    v___x_675_ = lean_box(0);
                    v_isShared_676_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_677_ = l_Lake_Job_renew___redArg___closed__0;
                v___x_678_ = lean_unsigned_to_nat(0);
                v___x_679_ = 1;
                v___x_680_ = lean_task_map(v___f_677_, v_task_670_, v___x_678_, v___x_679_);
                if v_isShared_676_ == 0 {
                    lean_ctor_set(v___x_675_, 0, v___x_680_);
                    v___x_682_ = v___x_675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
                    lean_ctor_set(v_reuseFailAlloc_683_, 1, v_kind_671_);
                    lean_ctor_set(v_reuseFailAlloc_683_, 2, v_caption_672_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_683_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_optional_673_,
                    );
                    v___x_682_ = v_reuseFailAlloc_683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_renew(
    mut v_00_u03b1_685_: *mut LeanObject,
    mut v_self_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lake_Job_renew___redArg(v_self_686_);
    return v___x_687_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__0(
    mut v_job_688_: *mut LeanObject,
    mut v_x_689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = l_Lake_Job_toOpaque___redArg(v_job_688_);
    v___x_691_ = lean_array_push(v_x_689_, v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__1(
    mut v_job_692_: *mut LeanObject,
    mut v_toPure_693_: *mut LeanObject,
    mut v_____r_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lake_Job_renew___redArg(v_job_692_);
    v___x_696_ = lean_apply_2(v_toPure_693_, lean_box(0), v___x_695_);
    return v___x_696_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__2(
    mut v___f_697_: *mut LeanObject,
    mut v_inst_698_: *mut LeanObject,
    mut v_toBind_699_: *mut LeanObject,
    mut v___f_700_: *mut LeanObject,
    mut v_____do__lift_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_registeredJobs_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v_registeredJobs_702_ = lean_ctor_get(v_____do__lift_701_, 3);
    lean_inc(v_registeredJobs_702_);
    lean_dec_ref(v_____do__lift_701_);
    v___x_703_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyUnsafe___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_703_, 0, lean_box(0));
    lean_closure_set(v___x_703_, 1, lean_box(0));
    lean_closure_set(v___x_703_, 2, v_registeredJobs_702_);
    lean_closure_set(v___x_703_, 3, v___f_697_);
    v___x_704_ = lean_apply_2(v_inst_698_, lean_box(0), v___x_703_);
    v___x_705_ = lean_apply_4(
        v_toBind_699_,
        lean_box(0),
        lean_box(0),
        v___x_704_,
        v___f_700_,
    );
    return v___x_705_;
}
pub unsafe fn l_Lake_registerJob___redArg(
    mut v_inst_706_: *mut LeanObject,
    mut v_inst_707_: *mut LeanObject,
    mut v_inst_708_: *mut LeanObject,
    mut v_caption_709_: *mut LeanObject,
    mut v_job_710_: *mut LeanObject,
    mut v_optional_711_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_717_: u8 = 0;
    let mut v_toBind_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_unused_728_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_712_ = lean_ctor_get(v_inst_706_, 0);
                lean_inc_ref(v_toApplicative_712_);
                v_task_713_ = lean_ctor_get(v_job_710_, 0);
                v_kind_714_ = lean_ctor_get(v_job_710_, 1);
                v_isSharedCheck_727_ = (!lean_is_exclusive(v_job_710_)) as u8;
                if v_isSharedCheck_727_ == 0 {
                    v_unused_728_ = lean_ctor_get(v_job_710_, 2);
                    lean_dec(v_unused_728_);
                    v___x_716_ = v_job_710_;
                    v_isShared_717_ = v_isSharedCheck_727_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_kind_714_);
                    lean_inc(v_task_713_);
                    lean_dec(v_job_710_);
                    v___x_716_ = lean_box(0);
                    v_isShared_717_ = v_isSharedCheck_727_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_718_ = lean_ctor_get(v_inst_706_, 1);
                lean_inc(v_toBind_718_);
                lean_dec_ref(v_inst_706_);
                v_toPure_719_ = lean_ctor_get(v_toApplicative_712_, 1);
                lean_inc(v_toPure_719_);
                lean_dec_ref(v_toApplicative_712_);
                if v_isShared_717_ == 0 {
                    lean_ctor_set(v___x_716_, 2, v_caption_709_);
                    v_job_721_ = v___x_716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_726_, 0, v_task_713_);
                    lean_ctor_set(v_reuseFailAlloc_726_, 1, v_kind_714_);
                    lean_ctor_set(v_reuseFailAlloc_726_, 2, v_caption_709_);
                    v_job_721_ = v_reuseFailAlloc_726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v_job_721_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_optional_711_,
                );
                lean_inc_ref(v_job_721_);
                v___f_722_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_722_, 0, v_job_721_);
                v___f_723_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_723_, 0, v_job_721_);
                lean_closure_set(v___f_723_, 1, v_toPure_719_);
                lean_inc(v_toBind_718_);
                v___f_724_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_724_, 0, v___f_722_);
                lean_closure_set(v___f_724_, 1, v_inst_707_);
                lean_closure_set(v___f_724_, 2, v_toBind_718_);
                lean_closure_set(v___f_724_, 3, v___f_723_);
                v___x_725_ = lean_apply_4(
                    v_toBind_718_,
                    lean_box(0),
                    lean_box(0),
                    v_inst_708_,
                    v___f_724_,
                );
                return v___x_725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerJob___redArg___boxed(
    mut v_inst_729_: *mut LeanObject,
    mut v_inst_730_: *mut LeanObject,
    mut v_inst_731_: *mut LeanObject,
    mut v_caption_732_: *mut LeanObject,
    mut v_job_733_: *mut LeanObject,
    mut v_optional_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optional_boxed_735_: u8 = 0;
    let mut v_res_736_: *mut LeanObject = core::ptr::null_mut();
    v_optional_boxed_735_ = (lean_unbox(v_optional_734_) as u8);
    v_res_736_ = l_Lake_registerJob___redArg(
        v_inst_729_,
        v_inst_730_,
        v_inst_731_,
        v_caption_732_,
        v_job_733_,
        v_optional_boxed_735_,
    );
    return v_res_736_;
}
pub unsafe fn l_Lake_registerJob(
    mut v_m_737_: *mut LeanObject,
    mut v_00_u03b1_738_: *mut LeanObject,
    mut v_inst_739_: *mut LeanObject,
    mut v_inst_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
    mut v_caption_742_: *mut LeanObject,
    mut v_job_743_: *mut LeanObject,
    mut v_optional_744_: u8,
) -> *mut LeanObject {
    let mut v_toApplicative_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_750_: u8 = 0;
    let mut v_toBind_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_760_: u8 = 0;
    let mut v_unused_761_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_745_ = lean_ctor_get(v_inst_739_, 0);
                lean_inc_ref(v_toApplicative_745_);
                v_task_746_ = lean_ctor_get(v_job_743_, 0);
                v_kind_747_ = lean_ctor_get(v_job_743_, 1);
                v_isSharedCheck_760_ = (!lean_is_exclusive(v_job_743_)) as u8;
                if v_isSharedCheck_760_ == 0 {
                    v_unused_761_ = lean_ctor_get(v_job_743_, 2);
                    lean_dec(v_unused_761_);
                    v___x_749_ = v_job_743_;
                    v_isShared_750_ = v_isSharedCheck_760_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_kind_747_);
                    lean_inc(v_task_746_);
                    lean_dec(v_job_743_);
                    v___x_749_ = lean_box(0);
                    v_isShared_750_ = v_isSharedCheck_760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_751_ = lean_ctor_get(v_inst_739_, 1);
                lean_inc(v_toBind_751_);
                lean_dec_ref(v_inst_739_);
                v_toPure_752_ = lean_ctor_get(v_toApplicative_745_, 1);
                lean_inc(v_toPure_752_);
                lean_dec_ref(v_toApplicative_745_);
                if v_isShared_750_ == 0 {
                    lean_ctor_set(v___x_749_, 2, v_caption_742_);
                    v_job_754_ = v___x_749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_759_, 0, v_task_746_);
                    lean_ctor_set(v_reuseFailAlloc_759_, 1, v_kind_747_);
                    lean_ctor_set(v_reuseFailAlloc_759_, 2, v_caption_742_);
                    v_job_754_ = v_reuseFailAlloc_759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v_job_754_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_optional_744_,
                );
                lean_inc_ref(v_job_754_);
                v___f_755_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_755_, 0, v_job_754_);
                v___f_756_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_756_, 0, v_job_754_);
                lean_closure_set(v___f_756_, 1, v_toPure_752_);
                lean_inc(v_toBind_751_);
                v___f_757_ = lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_757_, 0, v___f_755_);
                lean_closure_set(v___f_757_, 1, v_inst_740_);
                lean_closure_set(v___f_757_, 2, v_toBind_751_);
                lean_closure_set(v___f_757_, 3, v___f_756_);
                v___x_758_ = lean_apply_4(
                    v_toBind_751_,
                    lean_box(0),
                    lean_box(0),
                    v_inst_741_,
                    v___f_757_,
                );
                return v___x_758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerJob___boxed(
    mut v_m_762_: *mut LeanObject,
    mut v_00_u03b1_763_: *mut LeanObject,
    mut v_inst_764_: *mut LeanObject,
    mut v_inst_765_: *mut LeanObject,
    mut v_inst_766_: *mut LeanObject,
    mut v_caption_767_: *mut LeanObject,
    mut v_job_768_: *mut LeanObject,
    mut v_optional_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optional_boxed_770_: u8 = 0;
    let mut v_res_771_: *mut LeanObject = core::ptr::null_mut();
    v_optional_boxed_770_ = (lean_unbox(v_optional_769_) as u8);
    v_res_771_ = l_Lake_registerJob(
        v_m_762_,
        v_00_u03b1_763_,
        v_inst_764_,
        v_inst_765_,
        v_inst_766_,
        v_caption_767_,
        v_job_768_,
        v_optional_boxed_770_,
    );
    return v_res_771_;
}
pub unsafe fn l_panic___at___00Lake_ensureJob_spec__0(
    mut v_msg_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = l_panic___at___00Lake_ensureJob_spec__0___closed__0;
    v___x_775_ = lean_panic_fn_borrowed(v___x_774_, v_msg_773_);
    return v___x_775_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__0(
    mut v_val_776_: *mut LeanObject,
    mut v_val_777_: *mut LeanObject,
    mut v_a_x3f_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    v___x_781_ = lean_get_set_stdout(v_val_776_);
    lean_dec_ref(v___x_781_);
    v___x_782_ = lean_get_set_stderr(v_val_777_);
    lean_dec_ref(v___x_782_);
    v___x_783_ = lean_box(0);
    v___x_784_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_784_, 0, v___x_783_);
    lean_ctor_set(v___x_784_, 1, v___y_779_);
    return v___x_784_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__0___boxed(
    mut v_val_785_: *mut LeanObject,
    mut v_val_786_: *mut LeanObject,
    mut v_a_x3f_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ =
        l_Lake_ensureJob___redArg___lam__0(v_val_785_, v_val_786_, v_a_x3f_787_, v___y_788_);
    lean_dec(v_a_x3f_787_);
    return v_res_790_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__1(
    mut v___x_791_: *mut LeanObject,
    mut v_x_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lake_JobResult_prependLog___redArg(v___x_791_, v_x_792_);
    return v___x_793_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__2(
    mut v_a_794_: *mut LeanObject,
    mut v_____r_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
    mut v___y_797_: *mut LeanObject,
    mut v___y_798_: *mut LeanObject,
    mut v___y_799_: *mut LeanObject,
    mut v___y_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_803_, 0, v_a_794_);
    lean_ctor_set(v___x_803_, 1, v___y_801_);
    return v___x_803_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__2___boxed(
    mut v_a_804_: *mut LeanObject,
    mut v_____r_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lake_ensureJob___redArg___lam__2(
        v_a_804_,
        v_____r_805_,
        v___y_806_,
        v___y_807_,
        v___y_808_,
        v___y_809_,
        v___y_810_,
        v___y_811_,
    );
    lean_dec_ref(v___y_810_);
    lean_dec(v___y_809_);
    lean_dec(v___y_808_);
    lean_dec(v___y_807_);
    lean_dec_ref(v___y_806_);
    return v_res_813_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___x_814_ = lean_unsigned_to_nat(0);
    v___x_815_ = l_ByteArray_empty;
    v___x_816_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_816_, 0, v___x_815_);
    lean_ctor_set(v___x_816_, 1, v___x_814_);
    return v___x_816_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Lake_ensureJob___redArg___closed__1;
    v___x_819_ = l_Lake_BuildTrace_nil(v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = l_Lake_ensureJob___redArg___closed__6;
    v___x_825_ = lean_unsigned_to_nat(46);
    v___x_826_ = lean_unsigned_to_nat(193);
    v___x_827_ = l_Lake_ensureJob___redArg___closed__5;
    v___x_828_ = l_Lake_ensureJob___redArg___closed__4;
    v___x_829_ =
        l_mkPanicMessageWithDecl(v___x_828_, v___x_827_, v___x_826_, v___x_825_, v___x_824_);
    return v___x_829_;
}
pub unsafe fn l_Lake_ensureJob___redArg(
    mut v_inst_830_: *mut LeanObject,
    mut v_x_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_iniPos_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v_task_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optional_872_: u8 = 0;
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_unused_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v_unused_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_839_ = lean_unsigned_to_nat(0);
                v___x_840_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__0_once),
                    _init_l_Lake_ensureJob___redArg___closed__0,
                );
                v___x_841_ = lean_st_mk_ref(v___x_840_);
                lean_inc(v___x_841_);
                v___x_842_ = l_IO_FS_Stream_ofBuffer(v___x_841_);
                lean_inc_ref(v___x_842_);
                v___x_843_ = lean_get_set_stdout(v___x_842_);
                v___x_844_ = lean_get_set_stderr(v___x_842_);
                lean_inc_ref(v_a_837_);
                lean_inc_ref(v_a_836_);
                lean_inc(v_a_835_);
                lean_inc(v_a_834_);
                lean_inc(v_a_833_);
                lean_inc_ref(v_a_832_);
                v___x_845_ = lean_apply_7(
                    v_x_831_,
                    v_a_832_,
                    v_a_833_,
                    v_a_834_,
                    v_a_835_,
                    v_a_836_,
                    v_a_837_,
                    lean_box(0),
                );
                v_iniPos_846_ = lean_array_get_size(v_a_837_);
                lean_dec_ref(v_a_837_);
                if lean_obj_tag(v___x_845_) == 0 {
                    v_a_892_ = lean_ctor_get(v___x_845_, 0);
                    lean_inc_n(v_a_892_, 2);
                    v_a_893_ = lean_ctor_get(v___x_845_, 1);
                    lean_inc(v_a_893_);
                    lean_dec_ref_known(v___x_845_, 2);
                    v___x_894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_894_, 0, v_a_892_);
                    v___x_895_ = l_Lake_ensureJob___redArg___lam__0(
                        v___x_843_, v___x_844_, v___x_894_, v_a_893_,
                    );
                    lean_dec_ref_known(v___x_894_, 1);
                    v_a_896_ = lean_ctor_get(v___x_895_, 1);
                    lean_inc(v_a_896_);
                    lean_dec_ref(v___x_895_);
                    v___x_897_ = lean_st_ref_get(v___x_841_);
                    lean_dec(v___x_841_);
                    v_data_898_ = lean_ctor_get(v___x_897_, 0);
                    lean_inc_ref(v_data_898_);
                    lean_dec(v___x_897_);
                    v___x_915_ = lean_string_validate_utf8(v_data_898_);
                    if v___x_915_ == 0 {
                        lean_dec_ref(v_data_898_);
                        v___x_916_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__7_once),
                            _init_l_Lake_ensureJob___redArg___closed__7,
                        );
                        v___x_917_ = l_panic___at___00Lake_ensureJob_spec__0(v___x_916_);
                        v___y_900_ = v___x_917_;
                        state = 7;
                        continue;
                    } else {
                        v___x_918_ = lean_string_from_utf8_unchecked(v_data_898_);
                        v___y_900_ = v___x_918_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_841_);
                    lean_dec_ref(v_a_832_);
                    v_a_919_ = lean_ctor_get(v___x_845_, 1);
                    lean_inc(v_a_919_);
                    lean_dec_ref_known(v___x_845_, 2);
                    v___x_920_ = lean_box(0);
                    v___x_921_ = l_Lake_ensureJob___redArg___lam__0(
                        v___x_843_, v___x_844_, v___x_920_, v_a_919_,
                    );
                    v_a_922_ = lean_ctor_get(v___x_921_, 1);
                    lean_inc(v_a_922_);
                    lean_dec_ref(v___x_921_);
                    v_a_848_ = v_a_922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_a_848_);
                v___x_849_ = l_Array_shrink___redArg(v_a_848_, v_iniPos_846_);
                v___x_850_ = lean_array_get_size(v_a_848_);
                v___x_851_ = l_Array_extract___redArg(v_a_848_, v_iniPos_846_, v___x_850_);
                lean_dec_ref(v_a_848_);
                v___x_852_ = l_panic___at___00Lake_ensureJob_spec__0___closed__0;
                v___x_853_ = 0;
                v___x_854_ = 0;
                v___x_855_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__2_once),
                    _init_l_Lake_ensureJob___redArg___closed__2,
                );
                v___x_856_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_856_, 0, v___x_851_);
                lean_ctor_set(v___x_856_, 1, v___x_855_);
                lean_ctor_set(v___x_856_, 2, v___x_839_);
                lean_ctor_set_uint8(
                    v___x_856_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_853_,
                );
                lean_ctor_set_uint8(
                    v___x_856_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_854_,
                );
                v___x_857_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_857_, 0, v___x_839_);
                lean_ctor_set(v___x_857_, 1, v___x_856_);
                v___x_858_ = lean_task_pure(v___x_857_);
                v___x_859_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_859_, 0, v___x_858_);
                lean_ctor_set(v___x_859_, 1, v_inst_830_);
                lean_ctor_set(v___x_859_, 2, v___x_852_);
                lean_ctor_set_uint8(
                    v___x_859_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_854_,
                );
                v___x_860_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_860_, 0, v___x_859_);
                lean_ctor_set(v___x_860_, 1, v___x_849_);
                return v___x_860_;
            }
            2 => {
                if lean_obj_tag(v___y_862_) == 0 {
                    v_a_863_ = lean_ctor_get(v___y_862_, 0);
                    lean_inc(v_a_863_);
                    v_a_864_ = lean_ctor_get(v___y_862_, 1);
                    v___x_865_ = lean_array_get_size(v_a_864_);
                    v___x_866_ = lean_nat_dec_lt(v_iniPos_846_, v___x_865_);
                    if v___x_866_ == 0 {
                        lean_dec(v_a_863_);
                        lean_dec(v_inst_830_);
                        return v___y_862_;
                    } else {
                        lean_inc(v_a_864_);
                        v_isSharedCheck_888_ = (!lean_is_exclusive(v___y_862_)) as u8;
                        if v_isSharedCheck_888_ == 0 {
                            v_unused_889_ = lean_ctor_get(v___y_862_, 1);
                            lean_dec(v_unused_889_);
                            v_unused_890_ = lean_ctor_get(v___y_862_, 0);
                            lean_dec(v_unused_890_);
                            v___x_868_ = v___y_862_;
                            v_isShared_869_ = v_isSharedCheck_888_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___y_862_);
                            v___x_868_ = lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_888_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_891_ = lean_ctor_get(v___y_862_, 1);
                    lean_inc(v_a_891_);
                    lean_dec_ref_known(v___y_862_, 2);
                    v_a_848_ = v_a_891_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_task_870_ = lean_ctor_get(v_a_863_, 0);
                v_caption_871_ = lean_ctor_get(v_a_863_, 2);
                v_optional_872_ = lean_ctor_get_uint8(
                    v_a_863_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_886_ = (!lean_is_exclusive(v_a_863_)) as u8;
                if v_isSharedCheck_886_ == 0 {
                    v_unused_887_ = lean_ctor_get(v_a_863_, 1);
                    lean_dec(v_unused_887_);
                    v___x_874_ = v_a_863_;
                    v_isShared_875_ = v_isSharedCheck_886_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_caption_871_);
                    lean_inc(v_task_870_);
                    lean_dec(v_a_863_);
                    v___x_874_ = lean_box(0);
                    v_isShared_875_ = v_isSharedCheck_886_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_864_);
                v___x_876_ = l_Array_shrink___redArg(v_a_864_, v_iniPos_846_);
                v___x_877_ = l_Array_extract___redArg(v_a_864_, v_iniPos_846_, v___x_865_);
                lean_dec(v_a_864_);
                v___f_878_ = lean_alloc_closure(
                    l_Lake_ensureJob___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_878_, 0, v___x_877_);
                v___x_879_ = lean_task_map(v___f_878_, v_task_870_, v___x_839_, v___x_866_);
                if v_isShared_875_ == 0 {
                    lean_ctor_set(v___x_874_, 1, v_inst_830_);
                    lean_ctor_set(v___x_874_, 0, v___x_879_);
                    v___x_881_ = v___x_874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_879_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 1, v_inst_830_);
                    lean_ctor_set(v_reuseFailAlloc_885_, 2, v_caption_871_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_885_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_optional_872_,
                    );
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_869_ == 0 {
                    lean_ctor_set(v___x_868_, 1, v___x_876_);
                    lean_ctor_set(v___x_868_, 0, v___x_881_);
                    v___x_883_ = v___x_868_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
                    lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_876_);
                    v___x_883_ = v_reuseFailAlloc_884_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_883_;
            }
            7 => {
                v___x_901_ = lean_string_utf8_byte_size(v___y_900_);
                v___x_902_ = lean_nat_dec_eq(v___x_901_, v___x_839_);
                if v___x_902_ == 0 {
                    v___x_903_ = l_Lake_ensureJob___redArg___closed__3;
                    v___x_904_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_904_, 0, v___y_900_);
                    lean_ctor_set(v___x_904_, 1, v___x_839_);
                    lean_ctor_set(v___x_904_, 2, v___x_901_);
                    v___x_905_ = l_String_Slice_trimAscii(v___x_904_);
                    v___x_906_ = l_String_Slice_toString(v___x_905_);
                    lean_dec_ref(v___x_905_);
                    v___x_907_ = lean_string_append(v___x_903_, v___x_906_);
                    lean_dec_ref(v___x_906_);
                    v___x_908_ = 1;
                    v___x_909_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_909_, 0, v___x_907_);
                    lean_ctor_set_uint8(
                        v___x_909_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_908_,
                    );
                    v___x_910_ = lean_box(0);
                    v___x_911_ = lean_array_push(v_a_896_, v___x_909_);
                    v___x_912_ = l_Lake_ensureJob___redArg___lam__2(
                        v_a_892_, v___x_910_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_,
                        v___x_911_,
                    );
                    lean_dec_ref(v_a_832_);
                    v___y_862_ = v___x_912_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___y_900_);
                    v___x_913_ = lean_box(0);
                    v___x_914_ = l_Lake_ensureJob___redArg___lam__2(
                        v_a_892_, v___x_913_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_,
                        v_a_896_,
                    );
                    lean_dec_ref(v_a_832_);
                    v___y_862_ = v___x_914_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ensureJob___redArg___boxed(
    mut v_inst_923_: *mut LeanObject,
    mut v_x_924_: *mut LeanObject,
    mut v_a_925_: *mut LeanObject,
    mut v_a_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_a_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_932_: *mut LeanObject = core::ptr::null_mut();
    v_res_932_ = l_Lake_ensureJob___redArg(
        v_inst_923_,
        v_x_924_,
        v_a_925_,
        v_a_926_,
        v_a_927_,
        v_a_928_,
        v_a_929_,
        v_a_930_,
    );
    lean_dec_ref(v_a_929_);
    lean_dec(v_a_928_);
    lean_dec(v_a_927_);
    lean_dec(v_a_926_);
    return v_res_932_;
}
pub unsafe fn l_Lake_ensureJob(
    mut v_00_u03b1_933_: *mut LeanObject,
    mut v_inst_934_: *mut LeanObject,
    mut v_x_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
    mut v_a_938_: *mut LeanObject,
    mut v_a_939_: *mut LeanObject,
    mut v_a_940_: *mut LeanObject,
    mut v_a_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Lake_ensureJob___redArg(
        v_inst_934_,
        v_x_935_,
        v_a_936_,
        v_a_937_,
        v_a_938_,
        v_a_939_,
        v_a_940_,
        v_a_941_,
    );
    return v___x_943_;
}
pub unsafe fn l_Lake_ensureJob___boxed(
    mut v_00_u03b1_944_: *mut LeanObject,
    mut v_inst_945_: *mut LeanObject,
    mut v_x_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_954_: *mut LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lake_ensureJob(
        v_00_u03b1_944_,
        v_inst_945_,
        v_x_946_,
        v_a_947_,
        v_a_948_,
        v_a_949_,
        v_a_950_,
        v_a_951_,
        v_a_952_,
    );
    lean_dec_ref(v_a_951_);
    lean_dec(v_a_950_);
    lean_dec(v_a_949_);
    lean_dec(v_a_948_);
    return v_res_954_;
}
pub unsafe fn l_Lake_withRegisterJob___redArg(
    mut v_inst_955_: *mut LeanObject,
    mut v_caption_956_: *mut LeanObject,
    mut v_x_957_: *mut LeanObject,
    mut v_optional_958_: u8,
    mut v_a_959_: *mut LeanObject,
    mut v_a_960_: *mut LeanObject,
    mut v_a_961_: *mut LeanObject,
    mut v_a_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
    mut v_a_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_971_: u8 = 0;
    let mut v_task_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v_registeredJobs_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut v_unused_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_966_ = l_Lake_ensureJob___redArg(
                    v_inst_955_,
                    v_x_957_,
                    v_a_959_,
                    v_a_960_,
                    v_a_961_,
                    v_a_962_,
                    v_a_963_,
                    v_a_964_,
                );
                v_a_967_ = lean_ctor_get(v___x_966_, 0);
                v_a_968_ = lean_ctor_get(v___x_966_, 1);
                v_isSharedCheck_991_ = (!lean_is_exclusive(v___x_966_)) as u8;
                if v_isSharedCheck_991_ == 0 {
                    v___x_970_ = v___x_966_;
                    v_isShared_971_ = v_isSharedCheck_991_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_968_);
                    lean_inc(v_a_967_);
                    lean_dec(v___x_966_);
                    v___x_970_ = lean_box(0);
                    v_isShared_971_ = v_isSharedCheck_991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_task_972_ = lean_ctor_get(v_a_967_, 0);
                v_kind_973_ = lean_ctor_get(v_a_967_, 1);
                v_isSharedCheck_989_ = (!lean_is_exclusive(v_a_967_)) as u8;
                if v_isSharedCheck_989_ == 0 {
                    v_unused_990_ = lean_ctor_get(v_a_967_, 2);
                    lean_dec(v_unused_990_);
                    v___x_975_ = v_a_967_;
                    v_isShared_976_ = v_isSharedCheck_989_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_973_);
                    lean_inc(v_task_972_);
                    lean_dec(v_a_967_);
                    v___x_975_ = lean_box(0);
                    v_isShared_976_ = v_isSharedCheck_989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_977_ = lean_ctor_get(v_a_963_, 3);
                v___x_978_ = lean_st_ref_take(v_registeredJobs_977_);
                if v_isShared_976_ == 0 {
                    lean_ctor_set(v___x_975_, 2, v_caption_956_);
                    v_job_980_ = v___x_975_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_988_, 0, v_task_972_);
                    lean_ctor_set(v_reuseFailAlloc_988_, 1, v_kind_973_);
                    lean_ctor_set(v_reuseFailAlloc_988_, 2, v_caption_956_);
                    v_job_980_ = v_reuseFailAlloc_988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_980_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_optional_958_,
                );
                lean_inc_ref(v_job_980_);
                v___x_981_ = l_Lake_Job_toOpaque___redArg(v_job_980_);
                v___x_982_ = lean_array_push(v___x_978_, v___x_981_);
                v___x_983_ = lean_st_ref_set(v_registeredJobs_977_, v___x_982_);
                v___x_984_ = l_Lake_Job_renew___redArg(v_job_980_);
                if v_isShared_971_ == 0 {
                    lean_ctor_set(v___x_970_, 0, v___x_984_);
                    v___x_986_ = v___x_970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
                    lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_968_);
                    v___x_986_ = v_reuseFailAlloc_987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_withRegisterJob___redArg___boxed(
    mut v_inst_992_: *mut LeanObject,
    mut v_caption_993_: *mut LeanObject,
    mut v_x_994_: *mut LeanObject,
    mut v_optional_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
    mut v_a_999_: *mut LeanObject,
    mut v_a_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
    mut v_a_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optional_boxed_1003_: u8 = 0;
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_optional_boxed_1003_ = (lean_unbox(v_optional_995_) as u8);
    v_res_1004_ = l_Lake_withRegisterJob___redArg(
        v_inst_992_,
        v_caption_993_,
        v_x_994_,
        v_optional_boxed_1003_,
        v_a_996_,
        v_a_997_,
        v_a_998_,
        v_a_999_,
        v_a_1000_,
        v_a_1001_,
    );
    lean_dec_ref(v_a_1000_);
    lean_dec(v_a_999_);
    lean_dec(v_a_998_);
    lean_dec(v_a_997_);
    return v_res_1004_;
}
pub unsafe fn l_Lake_withRegisterJob(
    mut v_00_u03b1_1005_: *mut LeanObject,
    mut v_inst_1006_: *mut LeanObject,
    mut v_caption_1007_: *mut LeanObject,
    mut v_x_1008_: *mut LeanObject,
    mut v_optional_1009_: u8,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v_task_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v_registeredJobs_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_unused_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1017_ = l_Lake_ensureJob___redArg(
                    v_inst_1006_,
                    v_x_1008_,
                    v_a_1010_,
                    v_a_1011_,
                    v_a_1012_,
                    v_a_1013_,
                    v_a_1014_,
                    v_a_1015_,
                );
                v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
                v_a_1019_ = lean_ctor_get(v___x_1017_, 1);
                v_isSharedCheck_1042_ = (!lean_is_exclusive(v___x_1017_)) as u8;
                if v_isSharedCheck_1042_ == 0 {
                    v___x_1021_ = v___x_1017_;
                    v_isShared_1022_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1019_);
                    lean_inc(v_a_1018_);
                    lean_dec(v___x_1017_);
                    v___x_1021_ = lean_box(0);
                    v_isShared_1022_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_task_1023_ = lean_ctor_get(v_a_1018_, 0);
                v_kind_1024_ = lean_ctor_get(v_a_1018_, 1);
                v_isSharedCheck_1040_ = (!lean_is_exclusive(v_a_1018_)) as u8;
                if v_isSharedCheck_1040_ == 0 {
                    v_unused_1041_ = lean_ctor_get(v_a_1018_, 2);
                    lean_dec(v_unused_1041_);
                    v___x_1026_ = v_a_1018_;
                    v_isShared_1027_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_1024_);
                    lean_inc(v_task_1023_);
                    lean_dec(v_a_1018_);
                    v___x_1026_ = lean_box(0);
                    v_isShared_1027_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1028_ = lean_ctor_get(v_a_1014_, 3);
                v___x_1029_ = lean_st_ref_take(v_registeredJobs_1028_);
                if v_isShared_1027_ == 0 {
                    lean_ctor_set(v___x_1026_, 2, v_caption_1007_);
                    v_job_1031_ = v___x_1026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_task_1023_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_kind_1024_);
                    lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_caption_1007_);
                    v_job_1031_ = v_reuseFailAlloc_1039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_1031_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_optional_1009_,
                );
                lean_inc_ref(v_job_1031_);
                v___x_1032_ = l_Lake_Job_toOpaque___redArg(v_job_1031_);
                v___x_1033_ = lean_array_push(v___x_1029_, v___x_1032_);
                v___x_1034_ = lean_st_ref_set(v_registeredJobs_1028_, v___x_1033_);
                v___x_1035_ = l_Lake_Job_renew___redArg(v_job_1031_);
                if v_isShared_1022_ == 0 {
                    lean_ctor_set(v___x_1021_, 0, v___x_1035_);
                    v___x_1037_ = v___x_1021_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
                    lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1019_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_withRegisterJob___boxed(
    mut v_00_u03b1_1043_: *mut LeanObject,
    mut v_inst_1044_: *mut LeanObject,
    mut v_caption_1045_: *mut LeanObject,
    mut v_x_1046_: *mut LeanObject,
    mut v_optional_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_a_1053_: *mut LeanObject,
    mut v_a_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_optional_boxed_1055_: u8 = 0;
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_optional_boxed_1055_ = (lean_unbox(v_optional_1047_) as u8);
    v_res_1056_ = l_Lake_withRegisterJob(
        v_00_u03b1_1043_,
        v_inst_1044_,
        v_caption_1045_,
        v_x_1046_,
        v_optional_boxed_1055_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
        v_a_1053_,
    );
    lean_dec_ref(v_a_1052_);
    lean_dec(v_a_1051_);
    lean_dec(v_a_1050_);
    lean_dec(v_a_1049_);
    return v_res_1056_;
}
pub unsafe fn l_Lake_maybeRegisterJob___redArg(
    mut v_caption_1057_: *mut LeanObject,
    mut v_job_1058_: *mut LeanObject,
    mut v_a_1059_: *mut LeanObject,
    mut v_a_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_task_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v_registeredJobs_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v_job_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut v_unused_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1062_ = lean_ctor_get(v_job_1058_, 0);
                v_kind_1063_ = lean_ctor_get(v_job_1058_, 1);
                v_caption_1064_ = lean_ctor_get(v_job_1058_, 2);
                v___x_1065_ = lean_string_utf8_byte_size(v_caption_1064_);
                v___x_1066_ = lean_unsigned_to_nat(0);
                v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
                if v___x_1067_ == 0 {
                    lean_dec_ref(v_caption_1057_);
                    v___x_1068_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1068_, 0, v_job_1058_);
                    lean_ctor_set(v___x_1068_, 1, v_a_1060_);
                    return v___x_1068_;
                } else {
                    lean_inc(v_kind_1063_);
                    lean_inc_ref(v_task_1062_);
                    v_isSharedCheck_1083_ = (!lean_is_exclusive(v_job_1058_)) as u8;
                    if v_isSharedCheck_1083_ == 0 {
                        v_unused_1084_ = lean_ctor_get(v_job_1058_, 2);
                        lean_dec(v_unused_1084_);
                        v_unused_1085_ = lean_ctor_get(v_job_1058_, 1);
                        lean_dec(v_unused_1085_);
                        v_unused_1086_ = lean_ctor_get(v_job_1058_, 0);
                        lean_dec(v_unused_1086_);
                        v___x_1070_ = v_job_1058_;
                        v_isShared_1071_ = v_isSharedCheck_1083_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_job_1058_);
                        v___x_1070_ = lean_box(0);
                        v_isShared_1071_ = v_isSharedCheck_1083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_registeredJobs_1072_ = lean_ctor_get(v_a_1059_, 3);
                v___x_1073_ = lean_st_ref_take(v_registeredJobs_1072_);
                v___x_1074_ = 0;
                if v_isShared_1071_ == 0 {
                    lean_ctor_set(v___x_1070_, 2, v_caption_1057_);
                    v_job_1076_ = v___x_1070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_task_1062_);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_kind_1063_);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_caption_1057_);
                    v_job_1076_ = v_reuseFailAlloc_1082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v_job_1076_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1074_,
                );
                lean_inc_ref(v_job_1076_);
                v___x_1077_ = l_Lake_Job_toOpaque___redArg(v_job_1076_);
                v___x_1078_ = lean_array_push(v___x_1073_, v___x_1077_);
                v___x_1079_ = lean_st_ref_set(v_registeredJobs_1072_, v___x_1078_);
                v___x_1080_ = l_Lake_Job_renew___redArg(v_job_1076_);
                v___x_1081_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1081_, 0, v___x_1080_);
                lean_ctor_set(v___x_1081_, 1, v_a_1060_);
                return v___x_1081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_maybeRegisterJob___redArg___boxed(
    mut v_caption_1087_: *mut LeanObject,
    mut v_job_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
    mut v_a_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ =
        l_Lake_maybeRegisterJob___redArg(v_caption_1087_, v_job_1088_, v_a_1089_, v_a_1090_);
    lean_dec_ref(v_a_1089_);
    return v_res_1092_;
}
pub unsafe fn l_Lake_maybeRegisterJob(
    mut v_00_u03b1_1093_: *mut LeanObject,
    mut v_caption_1094_: *mut LeanObject,
    mut v_job_1095_: *mut LeanObject,
    mut v_a_1096_: *mut LeanObject,
    mut v_a_1097_: *mut LeanObject,
    mut v_a_1098_: *mut LeanObject,
    mut v_a_1099_: *mut LeanObject,
    mut v_a_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_task_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_caption_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v_registeredJobs_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v_job_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut v_unused_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1103_ = lean_ctor_get(v_job_1095_, 0);
                v_kind_1104_ = lean_ctor_get(v_job_1095_, 1);
                v_caption_1105_ = lean_ctor_get(v_job_1095_, 2);
                v___x_1106_ = lean_string_utf8_byte_size(v_caption_1105_);
                v___x_1107_ = lean_unsigned_to_nat(0);
                v___x_1108_ = lean_nat_dec_eq(v___x_1106_, v___x_1107_);
                if v___x_1108_ == 0 {
                    lean_dec_ref(v_caption_1094_);
                    v___x_1109_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1109_, 0, v_job_1095_);
                    lean_ctor_set(v___x_1109_, 1, v_a_1101_);
                    return v___x_1109_;
                } else {
                    lean_inc(v_kind_1104_);
                    lean_inc_ref(v_task_1103_);
                    v_isSharedCheck_1124_ = (!lean_is_exclusive(v_job_1095_)) as u8;
                    if v_isSharedCheck_1124_ == 0 {
                        v_unused_1125_ = lean_ctor_get(v_job_1095_, 2);
                        lean_dec(v_unused_1125_);
                        v_unused_1126_ = lean_ctor_get(v_job_1095_, 1);
                        lean_dec(v_unused_1126_);
                        v_unused_1127_ = lean_ctor_get(v_job_1095_, 0);
                        lean_dec(v_unused_1127_);
                        v___x_1111_ = v_job_1095_;
                        v_isShared_1112_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_job_1095_);
                        v___x_1111_ = lean_box(0);
                        v_isShared_1112_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_registeredJobs_1113_ = lean_ctor_get(v_a_1100_, 3);
                v___x_1114_ = lean_st_ref_take(v_registeredJobs_1113_);
                v___x_1115_ = 0;
                if v_isShared_1112_ == 0 {
                    lean_ctor_set(v___x_1111_, 2, v_caption_1094_);
                    v_job_1117_ = v___x_1111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_task_1103_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_kind_1104_);
                    lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_caption_1094_);
                    v_job_1117_ = v_reuseFailAlloc_1123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v_job_1117_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1115_,
                );
                lean_inc_ref(v_job_1117_);
                v___x_1118_ = l_Lake_Job_toOpaque___redArg(v_job_1117_);
                v___x_1119_ = lean_array_push(v___x_1114_, v___x_1118_);
                v___x_1120_ = lean_st_ref_set(v_registeredJobs_1113_, v___x_1119_);
                v___x_1121_ = l_Lake_Job_renew___redArg(v_job_1117_);
                v___x_1122_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                lean_ctor_set(v___x_1122_, 1, v_a_1101_);
                return v___x_1122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_maybeRegisterJob___boxed(
    mut v_00_u03b1_1128_: *mut LeanObject,
    mut v_caption_1129_: *mut LeanObject,
    mut v_job_1130_: *mut LeanObject,
    mut v_a_1131_: *mut LeanObject,
    mut v_a_1132_: *mut LeanObject,
    mut v_a_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Lake_maybeRegisterJob(
        v_00_u03b1_1128_,
        v_caption_1129_,
        v_job_1130_,
        v_a_1131_,
        v_a_1132_,
        v_a_1133_,
        v_a_1134_,
        v_a_1135_,
        v_a_1136_,
    );
    lean_dec_ref(v_a_1135_);
    lean_dec(v_a_1134_);
    lean_dec(v_a_1133_);
    lean_dec(v_a_1132_);
    lean_dec_ref(v_a_1131_);
    return v_res_1138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Job_Register(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Job_Register(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Job_Register(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Job_Register(builtin);
}
