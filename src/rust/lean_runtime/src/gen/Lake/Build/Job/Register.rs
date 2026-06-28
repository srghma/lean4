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
pub static l_Lake_JobState_renew___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_JobState_renew___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobState_renew___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_renew___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Job_renew___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Job_renew___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_renew___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lake_ensureJob_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l_panic___at___00Lake_ensureJob_spec__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lake_ensureJob_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ensureJob___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ensureJob___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_ensureJob___redArg___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_ensureJob___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ensureJob___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ensureJob___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_ensureJob___redArg___closed__3_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_ensureJob___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ensureJob___redArg___closed__4_value: crate::leanh::LeanStringObject<23> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_Lake_ensureJob___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ensureJob___redArg___closed__5_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_ensureJob___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ensureJob___redArg___closed__6_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_Lake_ensureJob___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ensureJob___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ensureJob___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ensureJob___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_JobState_renew(
    mut v_s_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v_caption_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_578_: u64 = 0;
    let mut v_mtime_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_593_: u8 = 0;
    let mut v_unused_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_595_: u8 = 0;
    let mut v_unused_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trace_573_ = crate::leanh::lean_ctor_get(v_s_572_, 1);
                v_isSharedCheck_595_ = (!crate::leanh::lean_is_exclusive(v_s_572_)) as u8;
                if v_isSharedCheck_595_ == 0 {
                    v_unused_596_ = crate::leanh::lean_ctor_get(v_s_572_, 2);
                    crate::leanh::lean_dec(v_unused_596_);
                    v_unused_597_ = crate::leanh::lean_ctor_get(v_s_572_, 0);
                    crate::leanh::lean_dec(v_unused_597_);
                    v___x_575_ = v_s_572_;
                    v_isShared_576_ = v_isSharedCheck_595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_573_);
                    crate::leanh::lean_dec(v_s_572_);
                    v___x_575_ = crate::leanh::lean_box(0);
                    v_isShared_576_ = v_isSharedCheck_595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_caption_577_ = crate::leanh::lean_ctor_get(v_trace_573_, 0);
                v_hash_578_ = crate::leanh::lean_ctor_get_uint64(
                    v_trace_573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_579_ = crate::leanh::lean_ctor_get(v_trace_573_, 2);
                v_isSharedCheck_593_ = (!crate::leanh::lean_is_exclusive(v_trace_573_)) as u8;
                if v_isSharedCheck_593_ == 0 {
                    v_unused_594_ = crate::leanh::lean_ctor_get(v_trace_573_, 1);
                    crate::leanh::lean_dec(v_unused_594_);
                    v___x_581_ = v_trace_573_;
                    v_isShared_582_ = v_isSharedCheck_593_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mtime_579_);
                    crate::leanh::lean_inc(v_caption_577_);
                    crate::leanh::lean_dec(v_trace_573_);
                    v___x_581_ = crate::leanh::lean_box(0);
                    v_isShared_582_ = v_isSharedCheck_593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_583_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_584_ = l_Lake_JobState_renew___closed__0;
                v___x_585_ = 0;
                v___x_586_ = 0;
                if v_isShared_582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_581_, 1, v___x_584_);
                    v___x_588_ = v___x_581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_592_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_592_, 0, v_caption_577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_592_, 2, v_mtime_579_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_592_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_hash_578_,
                    );
                    v___x_588_ = v_reuseFailAlloc_592_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_575_, 2, v___x_583_);
                    crate::leanh::lean_ctor_set(v___x_575_, 1, v___x_588_);
                    crate::leanh::lean_ctor_set(v___x_575_, 0, v___x_584_);
                    v___x_590_ = v___x_575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 2, v___x_583_);
                    v___x_590_ = v_reuseFailAlloc_591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_585_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_586_,
                );
                return v___x_590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_renew___redArg___lam__0(
    mut v_x_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v_a_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v_caption_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_609_: u64 = 0;
    let mut v_mtime_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: u8 = 0;
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_unused_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_629_: u8 = 0;
    let mut v_unused_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_unused_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v_trace_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v_caption_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_643_: u64 = 0;
    let mut v_mtime_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_unused_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_unused_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_unused_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_598_) == 0 {
                    v_a_599_ = crate::leanh::lean_ctor_get(v_x_598_, 1);
                    crate::leanh::lean_inc(v_a_599_);
                    v_trace_600_ = crate::leanh::lean_ctor_get(v_a_599_, 1);
                    v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v_a_599_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v_unused_632_ = crate::leanh::lean_ctor_get(v_a_599_, 2);
                        crate::leanh::lean_dec(v_unused_632_);
                        v_unused_633_ = crate::leanh::lean_ctor_get(v_a_599_, 0);
                        crate::leanh::lean_dec(v_unused_633_);
                        v___x_602_ = v_a_599_;
                        v_isShared_603_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_trace_600_);
                        crate::leanh::lean_dec(v_a_599_);
                        v___x_602_ = crate::leanh::lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_634_ = crate::leanh::lean_ctor_get(v_x_598_, 1);
                    v_isSharedCheck_666_ = (!crate::leanh::lean_is_exclusive(v_x_598_)) as u8;
                    if v_isSharedCheck_666_ == 0 {
                        v_unused_667_ = crate::leanh::lean_ctor_get(v_x_598_, 0);
                        crate::leanh::lean_dec(v_unused_667_);
                        v___x_636_ = v_x_598_;
                        v_isShared_637_ = v_isSharedCheck_666_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_634_);
                        crate::leanh::lean_dec(v_x_598_);
                        v___x_636_ = crate::leanh::lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_666_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_a_604_ = crate::leanh::lean_ctor_get(v_x_598_, 0);
                v_isSharedCheck_629_ = (!crate::leanh::lean_is_exclusive(v_x_598_)) as u8;
                if v_isSharedCheck_629_ == 0 {
                    v_unused_630_ = crate::leanh::lean_ctor_get(v_x_598_, 1);
                    crate::leanh::lean_dec(v_unused_630_);
                    v___x_606_ = v_x_598_;
                    v_isShared_607_ = v_isSharedCheck_629_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_604_);
                    crate::leanh::lean_dec(v_x_598_);
                    v___x_606_ = crate::leanh::lean_box(0);
                    v_isShared_607_ = v_isSharedCheck_629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_caption_608_ = crate::leanh::lean_ctor_get(v_trace_600_, 0);
                v_hash_609_ = crate::leanh::lean_ctor_get_uint64(
                    v_trace_600_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_610_ = crate::leanh::lean_ctor_get(v_trace_600_, 2);
                v_isSharedCheck_627_ = (!crate::leanh::lean_is_exclusive(v_trace_600_)) as u8;
                if v_isSharedCheck_627_ == 0 {
                    v_unused_628_ = crate::leanh::lean_ctor_get(v_trace_600_, 1);
                    crate::leanh::lean_dec(v_unused_628_);
                    v___x_612_ = v_trace_600_;
                    v_isShared_613_ = v_isSharedCheck_627_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mtime_610_);
                    crate::leanh::lean_inc(v_caption_608_);
                    crate::leanh::lean_dec(v_trace_600_);
                    v___x_612_ = crate::leanh::lean_box(0);
                    v_isShared_613_ = v_isSharedCheck_627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_614_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_615_ = l_Lake_JobState_renew___closed__0;
                v___x_616_ = 0;
                v___x_617_ = 0;
                if v_isShared_613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_612_, 1, v___x_615_);
                    v___x_619_ = v___x_612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_caption_608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 2, v_mtime_610_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_626_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_hash_609_,
                    );
                    v___x_619_ = v_reuseFailAlloc_626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_602_, 2, v___x_614_);
                    crate::leanh::lean_ctor_set(v___x_602_, 1, v___x_619_);
                    crate::leanh::lean_ctor_set(v___x_602_, 0, v___x_615_);
                    v___x_621_ = v___x_602_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_625_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_614_);
                    v___x_621_ = v_reuseFailAlloc_625_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_616_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_617_,
                );
                if v_isShared_607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_606_, 1, v___x_621_);
                    v___x_623_ = v___x_606_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
                    v___x_623_ = v_reuseFailAlloc_624_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_623_;
            }
            7 => {
                v_trace_638_ = crate::leanh::lean_ctor_get(v_a_634_, 1);
                v_isSharedCheck_663_ = (!crate::leanh::lean_is_exclusive(v_a_634_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v_unused_664_ = crate::leanh::lean_ctor_get(v_a_634_, 2);
                    crate::leanh::lean_dec(v_unused_664_);
                    v_unused_665_ = crate::leanh::lean_ctor_get(v_a_634_, 0);
                    crate::leanh::lean_dec(v_unused_665_);
                    v___x_640_ = v_a_634_;
                    v_isShared_641_ = v_isSharedCheck_663_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_638_);
                    crate::leanh::lean_dec(v_a_634_);
                    v___x_640_ = crate::leanh::lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_663_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_caption_642_ = crate::leanh::lean_ctor_get(v_trace_638_, 0);
                v_hash_643_ = crate::leanh::lean_ctor_get_uint64(
                    v_trace_638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_644_ = crate::leanh::lean_ctor_get(v_trace_638_, 2);
                v_isSharedCheck_661_ = (!crate::leanh::lean_is_exclusive(v_trace_638_)) as u8;
                if v_isSharedCheck_661_ == 0 {
                    v_unused_662_ = crate::leanh::lean_ctor_get(v_trace_638_, 1);
                    crate::leanh::lean_dec(v_unused_662_);
                    v___x_646_ = v_trace_638_;
                    v_isShared_647_ = v_isSharedCheck_661_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mtime_644_);
                    crate::leanh::lean_inc(v_caption_642_);
                    crate::leanh::lean_dec(v_trace_638_);
                    v___x_646_ = crate::leanh::lean_box(0);
                    v_isShared_647_ = v_isSharedCheck_661_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_648_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_649_ = l_Lake_JobState_renew___closed__0;
                v___x_650_ = 0;
                v___x_651_ = 0;
                if v_isShared_647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_646_, 1, v___x_649_);
                    v___x_653_ = v___x_646_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 0, v_caption_642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 2, v_mtime_644_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_660_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_hash_643_,
                    );
                    v___x_653_ = v_reuseFailAlloc_660_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_640_, 2, v___x_648_);
                    crate::leanh::lean_ctor_set(v___x_640_, 1, v___x_653_);
                    crate::leanh::lean_ctor_set(v___x_640_, 0, v___x_649_);
                    v___x_655_ = v___x_640_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 2, v___x_648_);
                    v___x_655_ = v_reuseFailAlloc_659_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_655_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_650_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_655_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_651_,
                );
                if v_isShared_637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_655_);
                    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_648_);
                    v___x_657_ = v___x_636_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
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
pub unsafe fn l_Lake_Job_renew___redArg(
    mut v_self_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_673_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___f_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_670_ = crate::leanh::lean_ctor_get(v_self_669_, 0);
                v_kind_671_ = crate::leanh::lean_ctor_get(v_self_669_, 1);
                v_caption_672_ = crate::leanh::lean_ctor_get(v_self_669_, 2);
                v_optional_673_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_669_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_684_ = (!crate::leanh::lean_is_exclusive(v_self_669_)) as u8;
                if v_isSharedCheck_684_ == 0 {
                    v___x_675_ = v_self_669_;
                    v_isShared_676_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_672_);
                    crate::leanh::lean_inc(v_kind_671_);
                    crate::leanh::lean_inc(v_task_670_);
                    crate::leanh::lean_dec(v_self_669_);
                    v___x_675_ = crate::leanh::lean_box(0);
                    v_isShared_676_ = v_isSharedCheck_684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_677_ = l_Lake_Job_renew___redArg___closed__0;
                v___x_678_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_679_ = 1;
                v___x_680_ = lean_task_map(v___f_677_, v_task_670_, v___x_678_, v___x_679_);
                if v_isShared_676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_680_);
                    v___x_682_ = v___x_675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 1, v_kind_671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 2, v_caption_672_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
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
    mut v_00_u03b1_685_: *mut crate::leanh::LeanObject,
    mut v_self_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lake_Job_renew___redArg(v_self_686_);
    return v___x_687_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__0(
    mut v_job_688_: *mut crate::leanh::LeanObject,
    mut v_x_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = l_Lake_Job_toOpaque___redArg(v_job_688_);
    v___x_691_ = lean_array_push(v_x_689_, v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__1(
    mut v_job_692_: *mut crate::leanh::LeanObject,
    mut v_toPure_693_: *mut crate::leanh::LeanObject,
    mut v_____r_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Lake_Job_renew___redArg(v_job_692_);
    v___x_696_ = crate::leanh::lean_apply_2(v_toPure_693_, crate::leanh::lean_box(0), v___x_695_);
    return v___x_696_;
}
pub unsafe fn l_Lake_registerJob___redArg___lam__2(
    mut v___f_697_: *mut crate::leanh::LeanObject,
    mut v_inst_698_: *mut crate::leanh::LeanObject,
    mut v_toBind_699_: *mut crate::leanh::LeanObject,
    mut v___f_700_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_registeredJobs_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_registeredJobs_702_ = crate::leanh::lean_ctor_get(v_____do__lift_701_, 3);
    crate::leanh::lean_inc(v_registeredJobs_702_);
    crate::leanh::lean_dec_ref(v_____do__lift_701_);
    v___x_703_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyUnsafe___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_703_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_703_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_703_, 2, v_registeredJobs_702_);
    crate::leanh::lean_closure_set(v___x_703_, 3, v___f_697_);
    v___x_704_ = crate::leanh::lean_apply_2(v_inst_698_, crate::leanh::lean_box(0), v___x_703_);
    v___x_705_ = crate::leanh::lean_apply_4(
        v_toBind_699_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_704_,
        v___f_700_,
    );
    return v___x_705_;
}
pub unsafe fn l_Lake_registerJob___redArg(
    mut v_inst_706_: *mut crate::leanh::LeanObject,
    mut v_inst_707_: *mut crate::leanh::LeanObject,
    mut v_inst_708_: *mut crate::leanh::LeanObject,
    mut v_caption_709_: *mut crate::leanh::LeanObject,
    mut v_job_710_: *mut crate::leanh::LeanObject,
    mut v_optional_711_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_717_: u8 = 0;
    let mut v_toBind_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_job_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_unused_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_712_ = crate::leanh::lean_ctor_get(v_inst_706_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_712_);
                v_task_713_ = crate::leanh::lean_ctor_get(v_job_710_, 0);
                v_kind_714_ = crate::leanh::lean_ctor_get(v_job_710_, 1);
                v_isSharedCheck_727_ = (!crate::leanh::lean_is_exclusive(v_job_710_)) as u8;
                if v_isSharedCheck_727_ == 0 {
                    v_unused_728_ = crate::leanh::lean_ctor_get(v_job_710_, 2);
                    crate::leanh::lean_dec(v_unused_728_);
                    v___x_716_ = v_job_710_;
                    v_isShared_717_ = v_isSharedCheck_727_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_714_);
                    crate::leanh::lean_inc(v_task_713_);
                    crate::leanh::lean_dec(v_job_710_);
                    v___x_716_ = crate::leanh::lean_box(0);
                    v_isShared_717_ = v_isSharedCheck_727_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_718_ = crate::leanh::lean_ctor_get(v_inst_706_, 1);
                crate::leanh::lean_inc(v_toBind_718_);
                crate::leanh::lean_dec_ref(v_inst_706_);
                v_toPure_719_ = crate::leanh::lean_ctor_get(v_toApplicative_712_, 1);
                crate::leanh::lean_inc(v_toPure_719_);
                crate::leanh::lean_dec_ref(v_toApplicative_712_);
                if v_isShared_717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_716_, 2, v_caption_709_);
                    v_job_721_ = v___x_716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 0, v_task_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 1, v_kind_714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 2, v_caption_709_);
                    v_job_721_ = v_reuseFailAlloc_726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_optional_711_,
                );
                crate::leanh::lean_inc_ref(v_job_721_);
                v___f_722_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_722_, 0, v_job_721_);
                v___f_723_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_723_, 0, v_job_721_);
                crate::leanh::lean_closure_set(v___f_723_, 1, v_toPure_719_);
                crate::leanh::lean_inc(v_toBind_718_);
                v___f_724_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_724_, 0, v___f_722_);
                crate::leanh::lean_closure_set(v___f_724_, 1, v_inst_707_);
                crate::leanh::lean_closure_set(v___f_724_, 2, v_toBind_718_);
                crate::leanh::lean_closure_set(v___f_724_, 3, v___f_723_);
                v___x_725_ = crate::leanh::lean_apply_4(
                    v_toBind_718_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_729_: *mut crate::leanh::LeanObject,
    mut v_inst_730_: *mut crate::leanh::LeanObject,
    mut v_inst_731_: *mut crate::leanh::LeanObject,
    mut v_caption_732_: *mut crate::leanh::LeanObject,
    mut v_job_733_: *mut crate::leanh::LeanObject,
    mut v_optional_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optional_boxed_735_: u8 = 0;
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optional_boxed_735_ = (crate::leanh::lean_unbox(v_optional_734_) as u8);
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
    mut v_m_737_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_738_: *mut crate::leanh::LeanObject,
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_caption_742_: *mut crate::leanh::LeanObject,
    mut v_job_743_: *mut crate::leanh::LeanObject,
    mut v_optional_744_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_750_: u8 = 0;
    let mut v_toBind_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_job_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_760_: u8 = 0;
    let mut v_unused_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_745_ = crate::leanh::lean_ctor_get(v_inst_739_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_745_);
                v_task_746_ = crate::leanh::lean_ctor_get(v_job_743_, 0);
                v_kind_747_ = crate::leanh::lean_ctor_get(v_job_743_, 1);
                v_isSharedCheck_760_ = (!crate::leanh::lean_is_exclusive(v_job_743_)) as u8;
                if v_isSharedCheck_760_ == 0 {
                    v_unused_761_ = crate::leanh::lean_ctor_get(v_job_743_, 2);
                    crate::leanh::lean_dec(v_unused_761_);
                    v___x_749_ = v_job_743_;
                    v_isShared_750_ = v_isSharedCheck_760_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_747_);
                    crate::leanh::lean_inc(v_task_746_);
                    crate::leanh::lean_dec(v_job_743_);
                    v___x_749_ = crate::leanh::lean_box(0);
                    v_isShared_750_ = v_isSharedCheck_760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toBind_751_ = crate::leanh::lean_ctor_get(v_inst_739_, 1);
                crate::leanh::lean_inc(v_toBind_751_);
                crate::leanh::lean_dec_ref(v_inst_739_);
                v_toPure_752_ = crate::leanh::lean_ctor_get(v_toApplicative_745_, 1);
                crate::leanh::lean_inc(v_toPure_752_);
                crate::leanh::lean_dec_ref(v_toApplicative_745_);
                if v_isShared_750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_749_, 2, v_caption_742_);
                    v_job_754_ = v___x_749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_759_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 0, v_task_746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 1, v_kind_747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 2, v_caption_742_);
                    v_job_754_ = v_reuseFailAlloc_759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_optional_744_,
                );
                crate::leanh::lean_inc_ref(v_job_754_);
                v___f_755_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_755_, 0, v_job_754_);
                v___f_756_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_756_, 0, v_job_754_);
                crate::leanh::lean_closure_set(v___f_756_, 1, v_toPure_752_);
                crate::leanh::lean_inc(v_toBind_751_);
                v___f_757_ = crate::leanh::lean_alloc_closure(
                    l_Lake_registerJob___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_757_, 0, v___f_755_);
                crate::leanh::lean_closure_set(v___f_757_, 1, v_inst_740_);
                crate::leanh::lean_closure_set(v___f_757_, 2, v_toBind_751_);
                crate::leanh::lean_closure_set(v___f_757_, 3, v___f_756_);
                v___x_758_ = crate::leanh::lean_apply_4(
                    v_toBind_751_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_m_762_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_inst_765_: *mut crate::leanh::LeanObject,
    mut v_inst_766_: *mut crate::leanh::LeanObject,
    mut v_caption_767_: *mut crate::leanh::LeanObject,
    mut v_job_768_: *mut crate::leanh::LeanObject,
    mut v_optional_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optional_boxed_770_: u8 = 0;
    let mut v_res_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optional_boxed_770_ = (crate::leanh::lean_unbox(v_optional_769_) as u8);
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
    mut v_msg_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = l_panic___at___00Lake_ensureJob_spec__0___closed__0;
    v___x_775_ = lean_panic_fn_borrowed(v___x_774_, v_msg_773_);
    return v___x_775_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__0(
    mut v_val_776_: *mut crate::leanh::LeanObject,
    mut v_val_777_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_781_ = lean_get_set_stdout(v_val_776_);
    crate::leanh::lean_dec_ref(v___x_781_);
    v___x_782_ = lean_get_set_stderr(v_val_777_);
    crate::leanh::lean_dec_ref(v___x_782_);
    v___x_783_ = crate::leanh::lean_box(0);
    v___x_784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_784_, 0, v___x_783_);
    crate::leanh::lean_ctor_set(v___x_784_, 1, v___y_779_);
    return v___x_784_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__0___boxed(
    mut v_val_785_: *mut crate::leanh::LeanObject,
    mut v_val_786_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ =
        l_Lake_ensureJob___redArg___lam__0(v_val_785_, v_val_786_, v_a_x3f_787_, v___y_788_);
    crate::leanh::lean_dec(v_a_x3f_787_);
    return v_res_790_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__1(
    mut v___x_791_: *mut crate::leanh::LeanObject,
    mut v_x_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lake_JobResult_prependLog___redArg(v___x_791_, v_x_792_);
    return v___x_793_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__2(
    mut v_a_794_: *mut crate::leanh::LeanObject,
    mut v_____r_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
    mut v___y_798_: *mut crate::leanh::LeanObject,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_803_, 0, v_a_794_);
    crate::leanh::lean_ctor_set(v___x_803_, 1, v___y_801_);
    return v___x_803_;
}
pub unsafe fn l_Lake_ensureJob___redArg___lam__2___boxed(
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_____r_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v___y_810_);
    crate::leanh::lean_dec(v___y_809_);
    crate::leanh::lean_dec(v___y_808_);
    crate::leanh::lean_dec(v___y_807_);
    crate::leanh::lean_dec_ref(v___y_806_);
    return v_res_813_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_815_ = l_ByteArray_empty;
    v___x_816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_816_, 0, v___x_815_);
    crate::leanh::lean_ctor_set(v___x_816_, 1, v___x_814_);
    return v___x_816_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Lake_ensureJob___redArg___closed__1;
    v___x_819_ = l_Lake_BuildTrace_nil(v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Lake_ensureJob___redArg___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l_Lake_ensureJob___redArg___closed__6;
    v___x_825_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_826_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_827_ = l_Lake_ensureJob___redArg___closed__5;
    v___x_828_ = l_Lake_ensureJob___redArg___closed__4;
    v___x_829_ =
        l_mkPanicMessageWithDecl(v___x_828_, v___x_827_, v___x_826_, v___x_825_, v___x_824_);
    return v___x_829_;
}
pub unsafe fn l_Lake_ensureJob___redArg(
    mut v_inst_830_: *mut crate::leanh::LeanObject,
    mut v_x_831_: *mut crate::leanh::LeanObject,
    mut v_a_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_iniPos_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v_task_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_872_: u8 = 0;
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_875_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_unused_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v_unused_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_839_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_840_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__0_once),
                    _init_l_Lake_ensureJob___redArg___closed__0,
                );
                v___x_841_ = lean_st_mk_ref(v___x_840_);
                crate::leanh::lean_inc(v___x_841_);
                v___x_842_ = l_IO_FS_Stream_ofBuffer(v___x_841_);
                crate::leanh::lean_inc_ref(v___x_842_);
                v___x_843_ = lean_get_set_stdout(v___x_842_);
                v___x_844_ = lean_get_set_stderr(v___x_842_);
                crate::leanh::lean_inc_ref(v_a_837_);
                crate::leanh::lean_inc_ref(v_a_836_);
                crate::leanh::lean_inc(v_a_835_);
                crate::leanh::lean_inc(v_a_834_);
                crate::leanh::lean_inc(v_a_833_);
                crate::leanh::lean_inc_ref(v_a_832_);
                v___x_845_ = crate::leanh::lean_apply_7(
                    v_x_831_,
                    v_a_832_,
                    v_a_833_,
                    v_a_834_,
                    v_a_835_,
                    v_a_836_,
                    v_a_837_,
                    crate::leanh::lean_box(0),
                );
                v_iniPos_846_ = lean_array_get_size(v_a_837_);
                crate::leanh::lean_dec_ref(v_a_837_);
                if crate::leanh::lean_obj_tag(v___x_845_) == 0 {
                    v_a_892_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                    crate::leanh::lean_inc_n(v_a_892_, 2);
                    v_a_893_ = crate::leanh::lean_ctor_get(v___x_845_, 1);
                    crate::leanh::lean_inc(v_a_893_);
                    crate::leanh::lean_dec_ref_known(v___x_845_, 2);
                    v___x_894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_894_, 0, v_a_892_);
                    v___x_895_ = l_Lake_ensureJob___redArg___lam__0(
                        v___x_843_, v___x_844_, v___x_894_, v_a_893_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_894_, 1);
                    v_a_896_ = crate::leanh::lean_ctor_get(v___x_895_, 1);
                    crate::leanh::lean_inc(v_a_896_);
                    crate::leanh::lean_dec_ref(v___x_895_);
                    v___x_897_ = lean_st_ref_get(v___x_841_);
                    crate::leanh::lean_dec(v___x_841_);
                    v_data_898_ = crate::leanh::lean_ctor_get(v___x_897_, 0);
                    crate::leanh::lean_inc_ref(v_data_898_);
                    crate::leanh::lean_dec(v___x_897_);
                    v___x_915_ = lean_string_validate_utf8(v_data_898_);
                    if v___x_915_ == 0 {
                        crate::leanh::lean_dec_ref(v_data_898_);
                        v___x_916_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v___x_841_);
                    crate::leanh::lean_dec_ref(v_a_832_);
                    v_a_919_ = crate::leanh::lean_ctor_get(v___x_845_, 1);
                    crate::leanh::lean_inc(v_a_919_);
                    crate::leanh::lean_dec_ref_known(v___x_845_, 2);
                    v___x_920_ = crate::leanh::lean_box(0);
                    v___x_921_ = l_Lake_ensureJob___redArg___lam__0(
                        v___x_843_, v___x_844_, v___x_920_, v_a_919_,
                    );
                    v_a_922_ = crate::leanh::lean_ctor_get(v___x_921_, 1);
                    crate::leanh::lean_inc(v_a_922_);
                    crate::leanh::lean_dec_ref(v___x_921_);
                    v_a_848_ = v_a_922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_a_848_);
                v___x_849_ = l_Array_shrink___redArg(v_a_848_, v_iniPos_846_);
                v___x_850_ = lean_array_get_size(v_a_848_);
                v___x_851_ = l_Array_extract___redArg(v_a_848_, v_iniPos_846_, v___x_850_);
                crate::leanh::lean_dec_ref(v_a_848_);
                v___x_852_ = l_panic___at___00Lake_ensureJob_spec__0___closed__0;
                v___x_853_ = 0;
                v___x_854_ = 0;
                v___x_855_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_ensureJob___redArg___closed__2_once),
                    _init_l_Lake_ensureJob___redArg___closed__2,
                );
                v___x_856_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_856_, 0, v___x_851_);
                crate::leanh::lean_ctor_set(v___x_856_, 1, v___x_855_);
                crate::leanh::lean_ctor_set(v___x_856_, 2, v___x_839_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_853_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_854_,
                );
                v___x_857_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_839_);
                crate::leanh::lean_ctor_set(v___x_857_, 1, v___x_856_);
                v___x_858_ = lean_task_pure(v___x_857_);
                v___x_859_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_858_);
                crate::leanh::lean_ctor_set(v___x_859_, 1, v_inst_830_);
                crate::leanh::lean_ctor_set(v___x_859_, 2, v___x_852_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_859_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_854_,
                );
                v___x_860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_860_, 0, v___x_859_);
                crate::leanh::lean_ctor_set(v___x_860_, 1, v___x_849_);
                return v___x_860_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_862_) == 0 {
                    v_a_863_ = crate::leanh::lean_ctor_get(v___y_862_, 0);
                    crate::leanh::lean_inc(v_a_863_);
                    v_a_864_ = crate::leanh::lean_ctor_get(v___y_862_, 1);
                    v___x_865_ = lean_array_get_size(v_a_864_);
                    v___x_866_ = lean_nat_dec_lt(v_iniPos_846_, v___x_865_);
                    if v___x_866_ == 0 {
                        crate::leanh::lean_dec(v_a_863_);
                        crate::leanh::lean_dec(v_inst_830_);
                        return v___y_862_;
                    } else {
                        crate::leanh::lean_inc(v_a_864_);
                        v_isSharedCheck_888_ = (!crate::leanh::lean_is_exclusive(v___y_862_)) as u8;
                        if v_isSharedCheck_888_ == 0 {
                            v_unused_889_ = crate::leanh::lean_ctor_get(v___y_862_, 1);
                            crate::leanh::lean_dec(v_unused_889_);
                            v_unused_890_ = crate::leanh::lean_ctor_get(v___y_862_, 0);
                            crate::leanh::lean_dec(v_unused_890_);
                            v___x_868_ = v___y_862_;
                            v_isShared_869_ = v_isSharedCheck_888_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_862_);
                            v___x_868_ = crate::leanh::lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_888_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_891_ = crate::leanh::lean_ctor_get(v___y_862_, 1);
                    crate::leanh::lean_inc(v_a_891_);
                    crate::leanh::lean_dec_ref_known(v___y_862_, 2);
                    v_a_848_ = v_a_891_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_task_870_ = crate::leanh::lean_ctor_get(v_a_863_, 0);
                v_caption_871_ = crate::leanh::lean_ctor_get(v_a_863_, 2);
                v_optional_872_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_863_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v_a_863_)) as u8;
                if v_isSharedCheck_886_ == 0 {
                    v_unused_887_ = crate::leanh::lean_ctor_get(v_a_863_, 1);
                    crate::leanh::lean_dec(v_unused_887_);
                    v___x_874_ = v_a_863_;
                    v_isShared_875_ = v_isSharedCheck_886_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_871_);
                    crate::leanh::lean_inc(v_task_870_);
                    crate::leanh::lean_dec(v_a_863_);
                    v___x_874_ = crate::leanh::lean_box(0);
                    v_isShared_875_ = v_isSharedCheck_886_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_864_);
                v___x_876_ = l_Array_shrink___redArg(v_a_864_, v_iniPos_846_);
                v___x_877_ = l_Array_extract___redArg(v_a_864_, v_iniPos_846_, v___x_865_);
                crate::leanh::lean_dec(v_a_864_);
                v___f_878_ = crate::leanh::lean_alloc_closure(
                    l_Lake_ensureJob___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_878_, 0, v___x_877_);
                v___x_879_ = lean_task_map(v___f_878_, v_task_870_, v___x_839_, v___x_866_);
                if v_isShared_875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_874_, 1, v_inst_830_);
                    crate::leanh::lean_ctor_set(v___x_874_, 0, v___x_879_);
                    v___x_881_ = v___x_874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_inst_830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 2, v_caption_871_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_885_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_872_,
                    );
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_876_);
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_881_);
                    v___x_883_ = v___x_868_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_876_);
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
                    v___x_904_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_904_, 0, v___y_900_);
                    crate::leanh::lean_ctor_set(v___x_904_, 1, v___x_839_);
                    crate::leanh::lean_ctor_set(v___x_904_, 2, v___x_901_);
                    v___x_905_ = l_String_Slice_trimAscii(v___x_904_);
                    v___x_906_ = l_String_Slice_toString(v___x_905_);
                    crate::leanh::lean_dec_ref(v___x_905_);
                    v___x_907_ = lean_string_append(v___x_903_, v___x_906_);
                    crate::leanh::lean_dec_ref(v___x_906_);
                    v___x_908_ = 1;
                    v___x_909_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_907_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_909_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_908_,
                    );
                    v___x_910_ = crate::leanh::lean_box(0);
                    v___x_911_ = lean_array_push(v_a_896_, v___x_909_);
                    v___x_912_ = l_Lake_ensureJob___redArg___lam__2(
                        v_a_892_, v___x_910_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_,
                        v___x_911_,
                    );
                    crate::leanh::lean_dec_ref(v_a_832_);
                    v___y_862_ = v___x_912_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_900_);
                    v___x_913_ = crate::leanh::lean_box(0);
                    v___x_914_ = l_Lake_ensureJob___redArg___lam__2(
                        v_a_892_, v___x_913_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_,
                        v_a_896_,
                    );
                    crate::leanh::lean_dec_ref(v_a_832_);
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
    mut v_inst_923_: *mut crate::leanh::LeanObject,
    mut v_x_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_929_);
    crate::leanh::lean_dec(v_a_928_);
    crate::leanh::lean_dec(v_a_927_);
    crate::leanh::lean_dec(v_a_926_);
    return v_res_932_;
}
pub unsafe fn l_Lake_ensureJob(
    mut v_00_u03b1_933_: *mut crate::leanh::LeanObject,
    mut v_inst_934_: *mut crate::leanh::LeanObject,
    mut v_x_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
    mut v_a_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_944_: *mut crate::leanh::LeanObject,
    mut v_inst_945_: *mut crate::leanh::LeanObject,
    mut v_x_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_951_);
    crate::leanh::lean_dec(v_a_950_);
    crate::leanh::lean_dec(v_a_949_);
    crate::leanh::lean_dec(v_a_948_);
    return v_res_954_;
}
pub unsafe fn l_Lake_withRegisterJob___redArg(
    mut v_inst_955_: *mut crate::leanh::LeanObject,
    mut v_caption_956_: *mut crate::leanh::LeanObject,
    mut v_x_957_: *mut crate::leanh::LeanObject,
    mut v_optional_958_: u8,
    mut v_a_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
    mut v_a_961_: *mut crate::leanh::LeanObject,
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
    mut v_a_964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_971_: u8 = 0;
    let mut v_task_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v_registeredJobs_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_job_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut v_unused_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_967_ = crate::leanh::lean_ctor_get(v___x_966_, 0);
                v_a_968_ = crate::leanh::lean_ctor_get(v___x_966_, 1);
                v_isSharedCheck_991_ = (!crate::leanh::lean_is_exclusive(v___x_966_)) as u8;
                if v_isSharedCheck_991_ == 0 {
                    v___x_970_ = v___x_966_;
                    v_isShared_971_ = v_isSharedCheck_991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_968_);
                    crate::leanh::lean_inc(v_a_967_);
                    crate::leanh::lean_dec(v___x_966_);
                    v___x_970_ = crate::leanh::lean_box(0);
                    v_isShared_971_ = v_isSharedCheck_991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_task_972_ = crate::leanh::lean_ctor_get(v_a_967_, 0);
                v_kind_973_ = crate::leanh::lean_ctor_get(v_a_967_, 1);
                v_isSharedCheck_989_ = (!crate::leanh::lean_is_exclusive(v_a_967_)) as u8;
                if v_isSharedCheck_989_ == 0 {
                    v_unused_990_ = crate::leanh::lean_ctor_get(v_a_967_, 2);
                    crate::leanh::lean_dec(v_unused_990_);
                    v___x_975_ = v_a_967_;
                    v_isShared_976_ = v_isSharedCheck_989_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_973_);
                    crate::leanh::lean_inc(v_task_972_);
                    crate::leanh::lean_dec(v_a_967_);
                    v___x_975_ = crate::leanh::lean_box(0);
                    v_isShared_976_ = v_isSharedCheck_989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_977_ = crate::leanh::lean_ctor_get(v_a_963_, 3);
                v___x_978_ = lean_st_ref_take(v_registeredJobs_977_);
                if v_isShared_976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_975_, 2, v_caption_956_);
                    v_job_980_ = v___x_975_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_988_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_988_, 0, v_task_972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_988_, 1, v_kind_973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_988_, 2, v_caption_956_);
                    v_job_980_ = v_reuseFailAlloc_988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_980_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_optional_958_,
                );
                crate::leanh::lean_inc_ref(v_job_980_);
                v___x_981_ = l_Lake_Job_toOpaque___redArg(v_job_980_);
                v___x_982_ = lean_array_push(v___x_978_, v___x_981_);
                v___x_983_ = lean_st_ref_set(v_registeredJobs_977_, v___x_982_);
                v___x_984_ = l_Lake_Job_renew___redArg(v_job_980_);
                if v_isShared_971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_970_, 0, v___x_984_);
                    v___x_986_ = v___x_970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_968_);
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
    mut v_inst_992_: *mut crate::leanh::LeanObject,
    mut v_caption_993_: *mut crate::leanh::LeanObject,
    mut v_x_994_: *mut crate::leanh::LeanObject,
    mut v_optional_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
    mut v_a_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
    mut v_a_1001_: *mut crate::leanh::LeanObject,
    mut v_a_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optional_boxed_1003_: u8 = 0;
    let mut v_res_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optional_boxed_1003_ = (crate::leanh::lean_unbox(v_optional_995_) as u8);
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
    crate::leanh::lean_dec_ref(v_a_1000_);
    crate::leanh::lean_dec(v_a_999_);
    crate::leanh::lean_dec(v_a_998_);
    crate::leanh::lean_dec(v_a_997_);
    return v_res_1004_;
}
pub unsafe fn l_Lake_withRegisterJob(
    mut v_00_u03b1_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_caption_1007_: *mut crate::leanh::LeanObject,
    mut v_x_1008_: *mut crate::leanh::LeanObject,
    mut v_optional_1009_: u8,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v_task_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v_registeredJobs_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_job_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_unused_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_1018_ = crate::leanh::lean_ctor_get(v___x_1017_, 0);
                v_a_1019_ = crate::leanh::lean_ctor_get(v___x_1017_, 1);
                v_isSharedCheck_1042_ = (!crate::leanh::lean_is_exclusive(v___x_1017_)) as u8;
                if v_isSharedCheck_1042_ == 0 {
                    v___x_1021_ = v___x_1017_;
                    v_isShared_1022_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1019_);
                    crate::leanh::lean_inc(v_a_1018_);
                    crate::leanh::lean_dec(v___x_1017_);
                    v___x_1021_ = crate::leanh::lean_box(0);
                    v_isShared_1022_ = v_isSharedCheck_1042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_task_1023_ = crate::leanh::lean_ctor_get(v_a_1018_, 0);
                v_kind_1024_ = crate::leanh::lean_ctor_get(v_a_1018_, 1);
                v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v_a_1018_)) as u8;
                if v_isSharedCheck_1040_ == 0 {
                    v_unused_1041_ = crate::leanh::lean_ctor_get(v_a_1018_, 2);
                    crate::leanh::lean_dec(v_unused_1041_);
                    v___x_1026_ = v_a_1018_;
                    v_isShared_1027_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1024_);
                    crate::leanh::lean_inc(v_task_1023_);
                    crate::leanh::lean_dec(v_a_1018_);
                    v___x_1026_ = crate::leanh::lean_box(0);
                    v_isShared_1027_ = v_isSharedCheck_1040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1028_ = crate::leanh::lean_ctor_get(v_a_1014_, 3);
                v___x_1029_ = lean_st_ref_take(v_registeredJobs_1028_);
                if v_isShared_1027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1026_, 2, v_caption_1007_);
                    v_job_1031_ = v___x_1026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_task_1023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_kind_1024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_caption_1007_);
                    v_job_1031_ = v_reuseFailAlloc_1039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1031_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_optional_1009_,
                );
                crate::leanh::lean_inc_ref(v_job_1031_);
                v___x_1032_ = l_Lake_Job_toOpaque___redArg(v_job_1031_);
                v___x_1033_ = lean_array_push(v___x_1029_, v___x_1032_);
                v___x_1034_ = lean_st_ref_set(v_registeredJobs_1028_, v___x_1033_);
                v___x_1035_ = l_Lake_Job_renew___redArg(v_job_1031_);
                if v_isShared_1022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1035_);
                    v___x_1037_ = v___x_1021_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1019_);
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
    mut v_00_u03b1_1043_: *mut crate::leanh::LeanObject,
    mut v_inst_1044_: *mut crate::leanh::LeanObject,
    mut v_caption_1045_: *mut crate::leanh::LeanObject,
    mut v_x_1046_: *mut crate::leanh::LeanObject,
    mut v_optional_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
    mut v_a_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optional_boxed_1055_: u8 = 0;
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optional_boxed_1055_ = (crate::leanh::lean_unbox(v_optional_1047_) as u8);
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
    crate::leanh::lean_dec_ref(v_a_1052_);
    crate::leanh::lean_dec(v_a_1051_);
    crate::leanh::lean_dec(v_a_1050_);
    crate::leanh::lean_dec(v_a_1049_);
    return v_res_1056_;
}
pub unsafe fn l_Lake_maybeRegisterJob___redArg(
    mut v_caption_1057_: *mut crate::leanh::LeanObject,
    mut v_job_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
    mut v_a_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v_registeredJobs_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v_job_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut v_unused_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1062_ = crate::leanh::lean_ctor_get(v_job_1058_, 0);
                v_kind_1063_ = crate::leanh::lean_ctor_get(v_job_1058_, 1);
                v_caption_1064_ = crate::leanh::lean_ctor_get(v_job_1058_, 2);
                v___x_1065_ = lean_string_utf8_byte_size(v_caption_1064_);
                v___x_1066_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
                if v___x_1067_ == 0 {
                    crate::leanh::lean_dec_ref(v_caption_1057_);
                    v___x_1068_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1068_, 0, v_job_1058_);
                    crate::leanh::lean_ctor_set(v___x_1068_, 1, v_a_1060_);
                    return v___x_1068_;
                } else {
                    crate::leanh::lean_inc(v_kind_1063_);
                    crate::leanh::lean_inc_ref(v_task_1062_);
                    v_isSharedCheck_1083_ = (!crate::leanh::lean_is_exclusive(v_job_1058_)) as u8;
                    if v_isSharedCheck_1083_ == 0 {
                        v_unused_1084_ = crate::leanh::lean_ctor_get(v_job_1058_, 2);
                        crate::leanh::lean_dec(v_unused_1084_);
                        v_unused_1085_ = crate::leanh::lean_ctor_get(v_job_1058_, 1);
                        crate::leanh::lean_dec(v_unused_1085_);
                        v_unused_1086_ = crate::leanh::lean_ctor_get(v_job_1058_, 0);
                        crate::leanh::lean_dec(v_unused_1086_);
                        v___x_1070_ = v_job_1058_;
                        v_isShared_1071_ = v_isSharedCheck_1083_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_job_1058_);
                        v___x_1070_ = crate::leanh::lean_box(0);
                        v_isShared_1071_ = v_isSharedCheck_1083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_registeredJobs_1072_ = crate::leanh::lean_ctor_get(v_a_1059_, 3);
                v___x_1073_ = lean_st_ref_take(v_registeredJobs_1072_);
                v___x_1074_ = 0;
                if v_isShared_1071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1070_, 2, v_caption_1057_);
                    v_job_1076_ = v___x_1070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_task_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_kind_1063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_caption_1057_);
                    v_job_1076_ = v_reuseFailAlloc_1082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1076_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1074_,
                );
                crate::leanh::lean_inc_ref(v_job_1076_);
                v___x_1077_ = l_Lake_Job_toOpaque___redArg(v_job_1076_);
                v___x_1078_ = lean_array_push(v___x_1073_, v___x_1077_);
                v___x_1079_ = lean_st_ref_set(v_registeredJobs_1072_, v___x_1078_);
                v___x_1080_ = l_Lake_Job_renew___redArg(v_job_1076_);
                v___x_1081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
                crate::leanh::lean_ctor_set(v___x_1081_, 1, v_a_1060_);
                return v___x_1081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_maybeRegisterJob___redArg___boxed(
    mut v_caption_1087_: *mut crate::leanh::LeanObject,
    mut v_job_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ =
        l_Lake_maybeRegisterJob___redArg(v_caption_1087_, v_job_1088_, v_a_1089_, v_a_1090_);
    crate::leanh::lean_dec_ref(v_a_1089_);
    return v_res_1092_;
}
pub unsafe fn l_Lake_maybeRegisterJob(
    mut v_00_u03b1_1093_: *mut crate::leanh::LeanObject,
    mut v_caption_1094_: *mut crate::leanh::LeanObject,
    mut v_job_1095_: *mut crate::leanh::LeanObject,
    mut v_a_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
    mut v_a_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v_registeredJobs_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v_job_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut v_unused_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1103_ = crate::leanh::lean_ctor_get(v_job_1095_, 0);
                v_kind_1104_ = crate::leanh::lean_ctor_get(v_job_1095_, 1);
                v_caption_1105_ = crate::leanh::lean_ctor_get(v_job_1095_, 2);
                v___x_1106_ = lean_string_utf8_byte_size(v_caption_1105_);
                v___x_1107_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1108_ = lean_nat_dec_eq(v___x_1106_, v___x_1107_);
                if v___x_1108_ == 0 {
                    crate::leanh::lean_dec_ref(v_caption_1094_);
                    v___x_1109_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1109_, 0, v_job_1095_);
                    crate::leanh::lean_ctor_set(v___x_1109_, 1, v_a_1101_);
                    return v___x_1109_;
                } else {
                    crate::leanh::lean_inc(v_kind_1104_);
                    crate::leanh::lean_inc_ref(v_task_1103_);
                    v_isSharedCheck_1124_ = (!crate::leanh::lean_is_exclusive(v_job_1095_)) as u8;
                    if v_isSharedCheck_1124_ == 0 {
                        v_unused_1125_ = crate::leanh::lean_ctor_get(v_job_1095_, 2);
                        crate::leanh::lean_dec(v_unused_1125_);
                        v_unused_1126_ = crate::leanh::lean_ctor_get(v_job_1095_, 1);
                        crate::leanh::lean_dec(v_unused_1126_);
                        v_unused_1127_ = crate::leanh::lean_ctor_get(v_job_1095_, 0);
                        crate::leanh::lean_dec(v_unused_1127_);
                        v___x_1111_ = v_job_1095_;
                        v_isShared_1112_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_job_1095_);
                        v___x_1111_ = crate::leanh::lean_box(0);
                        v_isShared_1112_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_registeredJobs_1113_ = crate::leanh::lean_ctor_get(v_a_1100_, 3);
                v___x_1114_ = lean_st_ref_take(v_registeredJobs_1113_);
                v___x_1115_ = 0;
                if v_isShared_1112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1111_, 2, v_caption_1094_);
                    v_job_1117_ = v___x_1111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1123_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_task_1103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_kind_1104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_caption_1094_);
                    v_job_1117_ = v_reuseFailAlloc_1123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1117_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1115_,
                );
                crate::leanh::lean_inc_ref(v_job_1117_);
                v___x_1118_ = l_Lake_Job_toOpaque___redArg(v_job_1117_);
                v___x_1119_ = lean_array_push(v___x_1114_, v___x_1118_);
                v___x_1120_ = lean_st_ref_set(v_registeredJobs_1113_, v___x_1119_);
                v___x_1121_ = l_Lake_Job_renew___redArg(v_job_1117_);
                v___x_1122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                crate::leanh::lean_ctor_set(v___x_1122_, 1, v_a_1101_);
                return v___x_1122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_maybeRegisterJob___boxed(
    mut v_00_u03b1_1128_: *mut crate::leanh::LeanObject,
    mut v_caption_1129_: *mut crate::leanh::LeanObject,
    mut v_job_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
    mut v_a_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_a_1135_);
    crate::leanh::lean_dec(v_a_1134_);
    crate::leanh::lean_dec(v_a_1133_);
    crate::leanh::lean_dec(v_a_1132_);
    crate::leanh::lean_dec_ref(v_a_1131_);
    return v_res_1138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Job_Register(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Job_Register(
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
pub unsafe fn initialize_Lake_Build_Job_Register(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Job_Register(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Job_Register(builtin);
}
