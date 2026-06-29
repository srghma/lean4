// Lean compiler output
// Module: Lake.Util.Proc
// Imports: Lake.Util.Log Init.Data.String.TakeDrop
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_io_process_child_wait,
    lean_io_process_spawn, lean_nat_dec_eq, lean_string_append, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_uint32_dec_eq, lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::System::IO::l_IO_Process_output;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lake::Util::Log::{initialize_Lake_Util_Log, runtime_initialize_Lake_Util_Log};
pub static l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [80, 65, 84, 72, 0],
};
static mut l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [61, 0],
};
static mut l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3_value:
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
static mut l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [80, 65, 84, 72, 32, 0],
};
static mut l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkCmdLog___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [62, 32, 0],
    };
static mut l_Lake_mkCmdLog___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkCmdLog___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_mkCmdLog___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_mkCmdLog___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkCmdLog___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_logOutput___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 116, 100, 101, 114, 114, 58, 10, 0],
    };
static mut l_Lake_logOutput___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_logOutput___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_logOutput___redArg___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 116, 100, 111, 117, 116, 58, 10, 0],
    };
static mut l_Lake_logOutput___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_logOutput___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_rawProc___lam__0___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 120, 101, 99, 117, 116, 101, 32,
            39, 0,
        ],
    };
static mut l_Lake_rawProc___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_rawProc___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_rawProc___lam__0___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [39, 58, 32, 0],
    };
static mut l_Lake_rawProc___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_rawProc___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_proc___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            101, 120, 116, 101, 114, 110, 97, 108, 32, 99, 111, 109, 109, 97, 110, 100, 32, 39, 0,
        ],
    };
static mut l_Lake_proc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_proc___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_proc___closed__1_value: crate::leanh::LeanStringObject<20> =
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
            39, 32, 101, 120, 105, 116, 101, 100, 32, 119, 105, 116, 104, 32, 99, 111, 100, 101,
            32, 0,
        ],
    };
static mut l_Lake_proc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_proc___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_testProc___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [131586 as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_testProc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_testProc___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0(
    mut v_a_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u8 = 0;
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_512_) == 0 {
                    v___x_514_ = l_List_reverse___redArg(v_a_513_);
                    return v___x_514_;
                } else {
                    v_head_515_ = crate::leanh::lean_ctor_get(v_a_512_, 0);
                    v_tail_516_ = crate::leanh::lean_ctor_get(v_a_512_, 1);
                    v_isSharedCheck_540_ = (!crate::leanh::lean_is_exclusive(v_a_512_)) as u8;
                    if v_isSharedCheck_540_ == 0 {
                        v___x_518_ = v_a_512_;
                        v_isShared_519_ = v_isSharedCheck_540_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_516_);
                        crate::leanh::lean_inc(v_head_515_);
                        crate::leanh::lean_dec(v_a_512_);
                        v___x_518_ = crate::leanh::lean_box(0);
                        v_isShared_519_ = v_isSharedCheck_540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_526_ = crate::leanh::lean_ctor_get(v_head_515_, 0);
                crate::leanh::lean_inc(v_fst_526_);
                v_snd_527_ = crate::leanh::lean_ctor_get(v_head_515_, 1);
                crate::leanh::lean_inc(v_snd_527_);
                crate::leanh::lean_dec(v_head_515_);
                v___x_528_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0;
                v___x_529_ = lean_string_dec_eq(v_fst_526_, v___x_528_);
                if v___x_529_ == 0 {
                    v___x_530_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1;
                    v___x_531_ = lean_string_append(v_fst_526_, v___x_530_);
                    if crate::leanh::lean_obj_tag(v_snd_527_) == 0 {
                        v___x_537_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3;
                        v___y_533_ = v___x_537_;
                        state = 4;
                        continue;
                    } else {
                        v_val_538_ = crate::leanh::lean_ctor_get(v_snd_527_, 0);
                        crate::leanh::lean_inc(v_val_538_);
                        crate::leanh::lean_dec_ref_known(v_snd_527_, 1);
                        v___y_533_ = v_val_538_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_527_);
                    crate::leanh::lean_dec(v_fst_526_);
                    v___x_539_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4;
                    v___y_521_ = v___x_539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_518_, 1, v_a_513_);
                    crate::leanh::lean_ctor_set(v___x_518_, 0, v___y_521_);
                    v___x_523_ = v___x_518_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 1, v_a_513_);
                    v___x_523_ = v_reuseFailAlloc_525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_512_ = v_tail_516_;
                v_a_513_ = v___x_523_;
                state = 0;
                continue;
            }
            4 => {
                v___x_534_ = lean_string_append(v___x_531_, v___y_533_);
                crate::leanh::lean_dec_ref(v___y_533_);
                v___x_535_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2;
                v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
                v___y_521_ = v___x_536_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lake_mkCmdLog_spec__1(
    mut v_x_541_: *mut crate::leanh::LeanObject,
    mut v_x_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_542_) == 0 {
                    return v_x_541_;
                } else {
                    v_head_543_ = crate::leanh::lean_ctor_get(v_x_542_, 0);
                    v_tail_544_ = crate::leanh::lean_ctor_get(v_x_542_, 1);
                    v___x_545_ = lean_string_append(v_x_541_, v_head_543_);
                    v_x_541_ = v___x_545_;
                    v_x_542_ = v_tail_544_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lake_mkCmdLog_spec__1___boxed(
    mut v_x_547_: *mut crate::leanh::LeanObject,
    mut v_x_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_List_foldl___at___00Lake_mkCmdLog_spec__1(v_x_547_, v_x_548_);
    crate::leanh::lean_dec(v_x_548_);
    return v_res_549_;
}
pub unsafe fn l_Lake_mkCmdLog(
    mut v_args_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cmd_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cwd_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_envStr_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdStr_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cmd_553_ = crate::leanh::lean_ctor_get(v_args_552_, 1);
                crate::leanh::lean_inc_ref(v_cmd_553_);
                v_args_554_ = crate::leanh::lean_ctor_get(v_args_552_, 2);
                crate::leanh::lean_inc_ref(v_args_554_);
                v_cwd_555_ = crate::leanh::lean_ctor_get(v_args_552_, 3);
                crate::leanh::lean_inc(v_cwd_555_);
                v_env_556_ = crate::leanh::lean_ctor_get(v_args_552_, 4);
                crate::leanh::lean_inc_ref(v_env_556_);
                crate::leanh::lean_dec_ref(v_args_552_);
                v___x_557_ = lean_array_to_list(v_env_556_);
                v___x_558_ = crate::leanh::lean_box(0);
                v___x_559_ =
                    l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0(v___x_557_, v___x_558_);
                v___x_560_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3;
                v_envStr_561_ = l_List_foldl___at___00Lake_mkCmdLog_spec__1(v___x_560_, v___x_559_);
                crate::leanh::lean_dec(v___x_559_);
                v___x_562_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2;
                v___x_563_ = lean_array_to_list(v_args_554_);
                v___x_564_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_564_, 0, v_cmd_553_);
                crate::leanh::lean_ctor_set(v___x_564_, 1, v___x_563_);
                v_cmdStr_565_ = l_String_intercalate(v___x_562_, v___x_564_);
                if crate::leanh::lean_obj_tag(v_cwd_555_) == 0 {
                    v___x_572_ = l_Lake_mkCmdLog___closed__1;
                    v___y_567_ = v___x_572_;
                    state = 1;
                    continue;
                } else {
                    v_val_573_ = crate::leanh::lean_ctor_get(v_cwd_555_, 0);
                    crate::leanh::lean_inc(v_val_573_);
                    crate::leanh::lean_dec_ref_known(v_cwd_555_, 1);
                    v___y_567_ = v_val_573_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_568_ = l_Lake_mkCmdLog___closed__0;
                v___x_569_ = lean_string_append(v___y_567_, v___x_568_);
                v___x_570_ = lean_string_append(v___x_569_, v_envStr_561_);
                crate::leanh::lean_dec_ref(v_envStr_561_);
                v___x_571_ = lean_string_append(v___x_570_, v_cmdStr_565_);
                crate::leanh::lean_dec_ref(v_cmdStr_565_);
                return v___x_571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_logOutput___redArg___lam__0(
    mut v_stderr_575_: *mut crate::leanh::LeanObject,
    mut v_log_576_: *mut crate::leanh::LeanObject,
    mut v_inst_577_: *mut crate::leanh::LeanObject,
    mut v_____r_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    v___x_579_ = lean_string_utf8_byte_size(v_stderr_575_);
    v___x_580_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_581_ = lean_nat_dec_eq(v___x_579_, v___x_580_);
    if v___x_581_ == 0 {
        let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_577_);
        v___x_582_ = l_Lake_logOutput___redArg___lam__0___closed__0;
        v___x_583_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_583_, 0, v_stderr_575_);
        crate::leanh::lean_ctor_set(v___x_583_, 1, v___x_580_);
        crate::leanh::lean_ctor_set(v___x_583_, 2, v___x_579_);
        v___x_584_ = l_String_Slice_trimAscii(v___x_583_);
        v___x_585_ = l_String_Slice_toString(v___x_584_);
        crate::leanh::lean_dec_ref(v___x_584_);
        v___x_586_ = lean_string_append(v___x_582_, v___x_585_);
        crate::leanh::lean_dec_ref(v___x_585_);
        v___x_587_ = crate::leanh::lean_apply_1(v_log_576_, v___x_586_);
        return v___x_587_;
    } else {
        let mut v_toApplicative_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_log_576_);
        crate::leanh::lean_dec_ref(v_stderr_575_);
        v_toApplicative_588_ = crate::leanh::lean_ctor_get(v_inst_577_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_588_);
        crate::leanh::lean_dec_ref(v_inst_577_);
        v_toPure_589_ = crate::leanh::lean_ctor_get(v_toApplicative_588_, 1);
        crate::leanh::lean_inc(v_toPure_589_);
        crate::leanh::lean_dec_ref(v_toApplicative_588_);
        v___x_590_ = crate::leanh::lean_box(0);
        v___x_591_ =
            crate::leanh::lean_apply_2(v_toPure_589_, crate::leanh::lean_box(0), v___x_590_);
        return v___x_591_;
    }
}
pub unsafe fn l_Lake_logOutput___redArg___lam__1(
    mut v___f_592_: *mut crate::leanh::LeanObject,
    mut v_____r_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = crate::leanh::lean_apply_1(v___f_592_, v_____r_593_);
    return v___x_594_;
}
pub unsafe fn l_Lake_logOutput___redArg(
    mut v_inst_596_: *mut crate::leanh::LeanObject,
    mut v_out_597_: *mut crate::leanh::LeanObject,
    mut v_log_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stdout_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    v_stdout_599_ = crate::leanh::lean_ctor_get(v_out_597_, 0);
    crate::leanh::lean_inc_ref(v_stdout_599_);
    v_stderr_600_ = crate::leanh::lean_ctor_get(v_out_597_, 1);
    crate::leanh::lean_inc_ref_n(v_stderr_600_, 2);
    crate::leanh::lean_dec_ref(v_out_597_);
    crate::leanh::lean_inc_ref(v_inst_596_);
    crate::leanh::lean_inc(v_log_598_);
    v___f_601_ = crate::leanh::lean_alloc_closure(
        l_Lake_logOutput___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_601_, 0, v_stderr_600_);
    crate::leanh::lean_closure_set(v___f_601_, 1, v_log_598_);
    crate::leanh::lean_closure_set(v___f_601_, 2, v_inst_596_);
    v___x_602_ = lean_string_utf8_byte_size(v_stdout_599_);
    v___x_603_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_604_ = lean_nat_dec_eq(v___x_602_, v___x_603_);
    if v___x_604_ == 0 {
        let mut v_toBind_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_stderr_600_);
        v_toBind_605_ = crate::leanh::lean_ctor_get(v_inst_596_, 1);
        crate::leanh::lean_inc(v_toBind_605_);
        crate::leanh::lean_dec_ref(v_inst_596_);
        v___f_606_ = crate::leanh::lean_alloc_closure(
            l_Lake_logOutput___redArg___lam__1 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_606_, 0, v___f_601_);
        v___x_607_ = l_Lake_logOutput___redArg___closed__0;
        v___x_608_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_608_, 0, v_stdout_599_);
        crate::leanh::lean_ctor_set(v___x_608_, 1, v___x_603_);
        crate::leanh::lean_ctor_set(v___x_608_, 2, v___x_602_);
        v___x_609_ = l_String_Slice_trimAscii(v___x_608_);
        v___x_610_ = l_String_Slice_toString(v___x_609_);
        crate::leanh::lean_dec_ref(v___x_609_);
        v___x_611_ = lean_string_append(v___x_607_, v___x_610_);
        crate::leanh::lean_dec_ref(v___x_610_);
        v___x_612_ = crate::leanh::lean_apply_1(v_log_598_, v___x_611_);
        v___x_613_ = crate::leanh::lean_apply_4(
            v_toBind_605_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_612_,
            v___f_606_,
        );
        return v___x_613_;
    } else {
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_601_);
        crate::leanh::lean_dec_ref(v_stdout_599_);
        v___x_614_ = crate::leanh::lean_box(0);
        v___x_615_ =
            l_Lake_logOutput___redArg___lam__0(v_stderr_600_, v_log_598_, v_inst_596_, v___x_614_);
        return v___x_615_;
    }
}
pub unsafe fn l_Lake_logOutput(
    mut v_m_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_out_618_: *mut crate::leanh::LeanObject,
    mut v_log_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stdout_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    v_stdout_620_ = crate::leanh::lean_ctor_get(v_out_618_, 0);
    crate::leanh::lean_inc_ref(v_stdout_620_);
    v_stderr_621_ = crate::leanh::lean_ctor_get(v_out_618_, 1);
    crate::leanh::lean_inc_ref_n(v_stderr_621_, 2);
    crate::leanh::lean_dec_ref(v_out_618_);
    crate::leanh::lean_inc_ref(v_inst_617_);
    crate::leanh::lean_inc(v_log_619_);
    v___f_622_ = crate::leanh::lean_alloc_closure(
        l_Lake_logOutput___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_622_, 0, v_stderr_621_);
    crate::leanh::lean_closure_set(v___f_622_, 1, v_log_619_);
    crate::leanh::lean_closure_set(v___f_622_, 2, v_inst_617_);
    v___x_623_ = lean_string_utf8_byte_size(v_stdout_620_);
    v___x_624_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_625_ = lean_nat_dec_eq(v___x_623_, v___x_624_);
    if v___x_625_ == 0 {
        let mut v_toBind_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_stderr_621_);
        v_toBind_626_ = crate::leanh::lean_ctor_get(v_inst_617_, 1);
        crate::leanh::lean_inc(v_toBind_626_);
        crate::leanh::lean_dec_ref(v_inst_617_);
        v___f_627_ = crate::leanh::lean_alloc_closure(
            l_Lake_logOutput___redArg___lam__1 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_627_, 0, v___f_622_);
        v___x_628_ = l_Lake_logOutput___redArg___closed__0;
        v___x_629_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_629_, 0, v_stdout_620_);
        crate::leanh::lean_ctor_set(v___x_629_, 1, v___x_624_);
        crate::leanh::lean_ctor_set(v___x_629_, 2, v___x_623_);
        v___x_630_ = l_String_Slice_trimAscii(v___x_629_);
        v___x_631_ = l_String_Slice_toString(v___x_630_);
        crate::leanh::lean_dec_ref(v___x_630_);
        v___x_632_ = lean_string_append(v___x_628_, v___x_631_);
        crate::leanh::lean_dec_ref(v___x_631_);
        v___x_633_ = crate::leanh::lean_apply_1(v_log_619_, v___x_632_);
        v___x_634_ = crate::leanh::lean_apply_4(
            v_toBind_626_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_633_,
            v___f_627_,
        );
        return v___x_634_;
    } else {
        let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_622_);
        crate::leanh::lean_dec_ref(v_stdout_620_);
        v___x_635_ = crate::leanh::lean_box(0);
        v___x_636_ =
            l_Lake_logOutput___redArg___lam__0(v_stderr_621_, v_log_619_, v_inst_617_, v___x_635_);
        return v___x_636_;
    }
}
pub unsafe fn l_Lake_rawProc___lam__0(
    mut v_args_639_: *mut crate::leanh::LeanObject,
    mut v_____r_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_args_639_);
    v___x_644_ = l_IO_Process_output(v_args_639_, v___x_643_);
    if crate::leanh::lean_obj_tag(v___x_644_) == 0 {
        let mut v_a_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_args_639_);
        v_a_645_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
        crate::leanh::lean_inc(v_a_645_);
        crate::leanh::lean_dec_ref_known(v___x_644_, 1);
        v___x_646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_646_, 0, v_a_645_);
        crate::leanh::lean_ctor_set(v___x_646_, 1, v___y_641_);
        return v___x_646_;
    } else {
        let mut v_a_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_cmd_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_655_: u8 = 0;
        let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_647_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
        crate::leanh::lean_inc(v_a_647_);
        crate::leanh::lean_dec_ref_known(v___x_644_, 1);
        v_cmd_648_ = crate::leanh::lean_ctor_get(v_args_639_, 1);
        crate::leanh::lean_inc_ref(v_cmd_648_);
        crate::leanh::lean_dec_ref(v_args_639_);
        v___x_649_ = l_Lake_rawProc___lam__0___closed__0;
        v___x_650_ = lean_string_append(v___x_649_, v_cmd_648_);
        crate::leanh::lean_dec_ref(v_cmd_648_);
        v___x_651_ = l_Lake_rawProc___lam__0___closed__1;
        v___x_652_ = lean_string_append(v___x_650_, v___x_651_);
        v___x_653_ = lean_io_error_to_string(v_a_647_);
        v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
        crate::leanh::lean_dec_ref(v___x_653_);
        v___x_655_ = 3;
        v___x_656_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_656_, 0, v___x_654_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_656_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_655_,
        );
        v___x_657_ = lean_array_get_size(v___y_641_);
        v___x_658_ = lean_array_push(v___y_641_, v___x_656_);
        v___x_659_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_659_, 0, v___x_657_);
        crate::leanh::lean_ctor_set(v___x_659_, 1, v___x_658_);
        return v___x_659_;
    }
}
pub unsafe fn l_Lake_rawProc___lam__0___boxed(
    mut v_args_660_: *mut crate::leanh::LeanObject,
    mut v_____r_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Lake_rawProc___lam__0(v_args_660_, v_____r_661_, v___y_662_);
    return v_res_664_;
}
pub unsafe fn l_Lake_rawProc(
    mut v_args_665_: *mut crate::leanh::LeanObject,
    mut v_quiet_666_: u8,
    mut v_a_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v_unused_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_669_ = lean_array_get_size(v_a_667_);
                if v_quiet_666_ == 0 {
                    crate::leanh::lean_inc_ref(v_args_665_);
                    v___x_681_ = l_Lake_mkCmdLog(v_args_665_);
                    v___x_682_ = 0;
                    v___x_683_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_681_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_683_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_682_,
                    );
                    v___x_684_ = crate::leanh::lean_box(0);
                    v___x_685_ = lean_array_push(v_a_667_, v___x_683_);
                    v___x_686_ = l_Lake_rawProc___lam__0(v_args_665_, v___x_684_, v___x_685_);
                    v___y_671_ = v___x_686_;
                    state = 1;
                    continue;
                } else {
                    v___x_687_ = crate::leanh::lean_box(0);
                    v___x_688_ = l_Lake_rawProc___lam__0(v_args_665_, v___x_687_, v_a_667_);
                    v___y_671_ = v___x_688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_671_) == 0 {
                    return v___y_671_;
                } else {
                    v_a_672_ = crate::leanh::lean_ctor_get(v___y_671_, 1);
                    v_isSharedCheck_679_ = (!crate::leanh::lean_is_exclusive(v___y_671_)) as u8;
                    if v_isSharedCheck_679_ == 0 {
                        v_unused_680_ = crate::leanh::lean_ctor_get(v___y_671_, 0);
                        crate::leanh::lean_dec(v_unused_680_);
                        v___x_674_ = v___y_671_;
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_672_);
                        crate::leanh::lean_dec(v___y_671_);
                        v___x_674_ = crate::leanh::lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_669_);
                    v___x_677_ = v___x_674_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_672_);
                    v___x_677_ = v_reuseFailAlloc_678_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_rawProc___boxed(
    mut v_args_689_: *mut crate::leanh::LeanObject,
    mut v_quiet_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_quiet_boxed_693_: u8 = 0;
    let mut v_res_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_quiet_boxed_693_ = (crate::leanh::lean_unbox(v_quiet_690_) as u8);
    v_res_694_ = l_Lake_rawProc(v_args_689_, v_quiet_boxed_693_, v_a_691_);
    return v_res_694_;
}
pub unsafe fn l_Lake_proc___lam__0(
    mut v_stderr_695_: *mut crate::leanh::LeanObject,
    mut v_____r_696_: *mut crate::leanh::LeanObject,
    mut v___y_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    v___x_699_ = lean_string_utf8_byte_size(v_stderr_695_);
    v___x_700_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_701_ = lean_nat_dec_eq(v___x_699_, v___x_700_);
    if v___x_701_ == 0 {
        let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_707_: u8 = 0;
        let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_702_ = l_Lake_logOutput___redArg___lam__0___closed__0;
        v___x_703_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_703_, 0, v_stderr_695_);
        crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_700_);
        crate::leanh::lean_ctor_set(v___x_703_, 2, v___x_699_);
        v___x_704_ = l_String_Slice_trimAscii(v___x_703_);
        v___x_705_ = l_String_Slice_toString(v___x_704_);
        crate::leanh::lean_dec_ref(v___x_704_);
        v___x_706_ = lean_string_append(v___x_702_, v___x_705_);
        crate::leanh::lean_dec_ref(v___x_705_);
        v___x_707_ = 1;
        v___x_708_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_708_, 0, v___x_706_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_708_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_707_,
        );
        v___x_709_ = crate::leanh::lean_box(0);
        v___x_710_ = lean_array_push(v___y_697_, v___x_708_);
        v___x_711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_711_, 0, v___x_709_);
        crate::leanh::lean_ctor_set(v___x_711_, 1, v___x_710_);
        return v___x_711_;
    } else {
        let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_stderr_695_);
        v___x_712_ = crate::leanh::lean_box(0);
        v___x_713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_712_);
        crate::leanh::lean_ctor_set(v___x_713_, 1, v___y_697_);
        return v___x_713_;
    }
}
pub unsafe fn l_Lake_proc___lam__0___boxed(
    mut v_stderr_714_: *mut crate::leanh::LeanObject,
    mut v_____r_715_: *mut crate::leanh::LeanObject,
    mut v___y_716_: *mut crate::leanh::LeanObject,
    mut v___y_717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Lake_proc___lam__0(v_stderr_714_, v_____r_715_, v___y_716_);
    return v_res_718_;
}
pub unsafe fn l_Lake_proc___lam__1(
    mut v_quiet_719_: u8,
    mut v___x_720_: u8,
    mut v___y_721_: *mut crate::leanh::LeanObject,
    mut v___y_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_quiet_719_ == 0 {
        let mut v___x_724_: u8 = 0;
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_724_ = 1;
        v___x_725_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_725_, 0, v___y_721_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_725_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_724_,
        );
        v___x_726_ = crate::leanh::lean_box(0);
        v___x_727_ = lean_array_push(v___y_722_, v___x_725_);
        v___x_728_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_726_);
        crate::leanh::lean_ctor_set(v___x_728_, 1, v___x_727_);
        return v___x_728_;
    } else {
        let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_729_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_729_, 0, v___y_721_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_729_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_720_,
        );
        v___x_730_ = crate::leanh::lean_box(0);
        v___x_731_ = lean_array_push(v___y_722_, v___x_729_);
        v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_730_);
        crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_731_);
        return v___x_732_;
    }
}
pub unsafe fn l_Lake_proc___lam__1___boxed(
    mut v_quiet_733_: *mut crate::leanh::LeanObject,
    mut v___x_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_quiet_boxed_738_: u8 = 0;
    let mut v___x_5499__boxed_739_: u8 = 0;
    let mut v_res_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_quiet_boxed_738_ = (crate::leanh::lean_unbox(v_quiet_733_) as u8);
    v___x_5499__boxed_739_ = (crate::leanh::lean_unbox(v___x_734_) as u8);
    v_res_740_ = l_Lake_proc___lam__1(
        v_quiet_boxed_738_,
        v___x_5499__boxed_739_,
        v___y_735_,
        v___y_736_,
    );
    return v_res_740_;
}
pub unsafe fn l_Lake_proc___lam__2(
    mut v_stderr_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v_____r_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    v___x_746_ = lean_string_utf8_byte_size(v_stderr_741_);
    v___x_747_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_748_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
    if v___x_748_ == 0 {
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_749_ = l_Lake_logOutput___redArg___lam__0___closed__0;
        v___x_750_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_750_, 0, v_stderr_741_);
        crate::leanh::lean_ctor_set(v___x_750_, 1, v___x_747_);
        crate::leanh::lean_ctor_set(v___x_750_, 2, v___x_746_);
        v___x_751_ = l_String_Slice_trimAscii(v___x_750_);
        v___x_752_ = l_String_Slice_toString(v___x_751_);
        crate::leanh::lean_dec_ref(v___x_751_);
        v___x_753_ = lean_string_append(v___x_749_, v___x_752_);
        crate::leanh::lean_dec_ref(v___x_752_);
        v___x_754_ = crate::leanh::lean_apply_3(
            v___y_742_,
            v___x_753_,
            v___y_744_,
            crate::leanh::lean_box(0),
        );
        return v___x_754_;
    } else {
        let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___y_742_);
        crate::leanh::lean_dec_ref(v_stderr_741_);
        v___x_755_ = crate::leanh::lean_box(0);
        v___x_756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_755_);
        crate::leanh::lean_ctor_set(v___x_756_, 1, v___y_744_);
        return v___x_756_;
    }
}
pub unsafe fn l_Lake_proc___lam__2___boxed(
    mut v_stderr_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v_____r_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_762_ = l_Lake_proc___lam__2(v_stderr_757_, v___y_758_, v_____r_759_, v___y_760_);
    return v_res_762_;
}
pub unsafe fn l_Lake_proc(
    mut v_args_765_: *mut crate::leanh::LeanObject,
    mut v_quiet_766_: u8,
    mut v_a_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exitCode_783_: u32 = 0;
    let mut v_stdout_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u32 = 0;
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_769_ = lean_array_get_size(v_a_767_);
                crate::leanh::lean_inc_ref_n(v_args_765_, 2);
                v___x_776_ = l_Lake_mkCmdLog(v_args_765_);
                v___x_777_ = 0;
                v___x_778_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_777_,
                );
                v___x_779_ = lean_array_push(v_a_767_, v___x_778_);
                v___x_780_ = crate::leanh::lean_box(0);
                v___x_781_ = l_IO_Process_output(v_args_765_, v___x_780_);
                if crate::leanh::lean_obj_tag(v___x_781_) == 0 {
                    v_a_782_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                    crate::leanh::lean_inc(v_a_782_);
                    crate::leanh::lean_dec_ref_known(v___x_781_, 1);
                    v_exitCode_783_ = crate::leanh::lean_ctor_get_uint32(
                        v_a_782_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_stdout_784_ = crate::leanh::lean_ctor_get(v_a_782_, 0);
                    crate::leanh::lean_inc_ref(v_stdout_784_);
                    v_stderr_785_ = crate::leanh::lean_ctor_get(v_a_782_, 1);
                    crate::leanh::lean_inc_ref(v_stderr_785_);
                    crate::leanh::lean_dec(v_a_782_);
                    v___x_801_ = 0;
                    v___x_802_ = lean_uint32_dec_eq(v_exitCode_783_, v___x_801_);
                    if v___x_802_ == 0 {
                        v___x_803_ = lean_string_utf8_byte_size(v_stdout_784_);
                        v___x_804_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
                        if v___x_805_ == 0 {
                            v___x_806_ = l_Lake_logOutput___redArg___closed__0;
                            v___x_807_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_807_, 0, v_stdout_784_);
                            crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_804_);
                            crate::leanh::lean_ctor_set(v___x_807_, 2, v___x_803_);
                            v___x_808_ = l_String_Slice_trimAscii(v___x_807_);
                            v___x_809_ = l_String_Slice_toString(v___x_808_);
                            crate::leanh::lean_dec_ref(v___x_808_);
                            v___x_810_ = lean_string_append(v___x_806_, v___x_809_);
                            crate::leanh::lean_dec_ref(v___x_809_);
                            v___x_811_ = 1;
                            v___x_812_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_810_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_812_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_811_,
                            );
                            v___x_813_ = crate::leanh::lean_box(0);
                            v___x_814_ = lean_array_push(v___x_779_, v___x_812_);
                            v___x_815_ =
                                l_Lake_proc___lam__0(v_stderr_785_, v___x_813_, v___x_814_);
                            v___y_787_ = v___x_815_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_stdout_784_);
                            v___x_816_ = crate::leanh::lean_box(0);
                            v___x_817_ =
                                l_Lake_proc___lam__0(v_stderr_785_, v___x_816_, v___x_779_);
                            v___y_787_ = v___x_817_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_765_);
                        v___x_818_ = crate::leanh::lean_box((v_quiet_766_) as usize);
                        v___x_819_ = crate::leanh::lean_box((v___x_777_) as usize);
                        v___y_820_ = crate::leanh::lean_alloc_closure(
                            l_Lake_proc___lam__1___boxed as *mut core::ffi::c_void,
                            5,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___y_820_, 0, v___x_818_);
                        crate::leanh::lean_closure_set(v___y_820_, 1, v___x_819_);
                        v___x_821_ = lean_string_utf8_byte_size(v_stdout_784_);
                        v___x_822_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_823_ = lean_nat_dec_eq(v___x_821_, v___x_822_);
                        if v___x_823_ == 0 {
                            v___x_824_ = l_Lake_logOutput___redArg___closed__0;
                            v___x_825_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_825_, 0, v_stdout_784_);
                            crate::leanh::lean_ctor_set(v___x_825_, 1, v___x_822_);
                            crate::leanh::lean_ctor_set(v___x_825_, 2, v___x_821_);
                            v___x_826_ = l_String_Slice_trimAscii(v___x_825_);
                            v___x_827_ = l_String_Slice_toString(v___x_826_);
                            crate::leanh::lean_dec_ref(v___x_826_);
                            v___x_828_ = lean_string_append(v___x_824_, v___x_827_);
                            crate::leanh::lean_dec_ref(v___x_827_);
                            v___x_829_ = l_Lake_proc___lam__1(
                                v_quiet_766_,
                                v___x_777_,
                                v___x_828_,
                                v___x_779_,
                            );
                            v_a_830_ = crate::leanh::lean_ctor_get(v___x_829_, 0);
                            crate::leanh::lean_inc(v_a_830_);
                            v_a_831_ = crate::leanh::lean_ctor_get(v___x_829_, 1);
                            crate::leanh::lean_inc(v_a_831_);
                            crate::leanh::lean_dec_ref(v___x_829_);
                            v___x_832_ =
                                l_Lake_proc___lam__2(v_stderr_785_, v___y_820_, v_a_830_, v_a_831_);
                            v___y_774_ = v___x_832_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_stdout_784_);
                            v___x_833_ = crate::leanh::lean_box(0);
                            v___x_834_ = l_Lake_proc___lam__2(
                                v_stderr_785_,
                                v___y_820_,
                                v___x_833_,
                                v___x_779_,
                            );
                            v___y_774_ = v___x_834_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_835_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                    crate::leanh::lean_inc(v_a_835_);
                    crate::leanh::lean_dec_ref_known(v___x_781_, 1);
                    v_cmd_836_ = crate::leanh::lean_ctor_get(v_args_765_, 1);
                    crate::leanh::lean_inc_ref(v_cmd_836_);
                    crate::leanh::lean_dec_ref(v_args_765_);
                    v___x_837_ = l_Lake_rawProc___lam__0___closed__0;
                    v___x_838_ = lean_string_append(v___x_837_, v_cmd_836_);
                    crate::leanh::lean_dec_ref(v_cmd_836_);
                    v___x_839_ = l_Lake_rawProc___lam__0___closed__1;
                    v___x_840_ = lean_string_append(v___x_838_, v___x_839_);
                    v___x_841_ = lean_io_error_to_string(v_a_835_);
                    v___x_842_ = lean_string_append(v___x_840_, v___x_841_);
                    crate::leanh::lean_dec_ref(v___x_841_);
                    v___x_843_ = 3;
                    v___x_844_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_842_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_844_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_843_,
                    );
                    v___x_845_ = lean_array_push(v___x_779_, v___x_844_);
                    v_a_771_ = v___x_845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_772_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_769_);
                crate::leanh::lean_ctor_set(v___x_772_, 1, v_a_771_);
                return v___x_772_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_774_) == 0 {
                    return v___y_774_;
                } else {
                    v_a_775_ = crate::leanh::lean_ctor_get(v___y_774_, 1);
                    crate::leanh::lean_inc(v_a_775_);
                    crate::leanh::lean_dec_ref_known(v___y_774_, 2);
                    v_a_771_ = v_a_775_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_787_) == 0 {
                    v_a_788_ = crate::leanh::lean_ctor_get(v___y_787_, 1);
                    crate::leanh::lean_inc(v_a_788_);
                    crate::leanh::lean_dec_ref_known(v___y_787_, 2);
                    v_cmd_789_ = crate::leanh::lean_ctor_get(v_args_765_, 1);
                    crate::leanh::lean_inc_ref(v_cmd_789_);
                    crate::leanh::lean_dec_ref(v_args_765_);
                    v___x_790_ = l_Lake_proc___closed__0;
                    v___x_791_ = lean_string_append(v___x_790_, v_cmd_789_);
                    crate::leanh::lean_dec_ref(v_cmd_789_);
                    v___x_792_ = l_Lake_proc___closed__1;
                    v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
                    v___x_794_ = lean_uint32_to_nat(v_exitCode_783_);
                    v___x_795_ = l_Nat_reprFast(v___x_794_);
                    v___x_796_ = lean_string_append(v___x_793_, v___x_795_);
                    crate::leanh::lean_dec_ref(v___x_795_);
                    v___x_797_ = 3;
                    v___x_798_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_798_, 0, v___x_796_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_798_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_797_,
                    );
                    v___x_799_ = lean_array_push(v_a_788_, v___x_798_);
                    v_a_771_ = v___x_799_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_args_765_);
                    v_a_800_ = crate::leanh::lean_ctor_get(v___y_787_, 1);
                    crate::leanh::lean_inc(v_a_800_);
                    crate::leanh::lean_dec_ref_known(v___y_787_, 2);
                    v_a_771_ = v_a_800_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_proc___boxed(
    mut v_args_846_: *mut crate::leanh::LeanObject,
    mut v_quiet_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_quiet_boxed_850_: u8 = 0;
    let mut v_res_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_quiet_boxed_850_ = (crate::leanh::lean_unbox(v_quiet_847_) as u8);
    v_res_851_ = l_Lake_proc(v_args_846_, v_quiet_boxed_850_, v_a_848_);
    return v_res_851_;
}
pub unsafe fn l_Lake_captureProc_x27(
    mut v_args_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exitCode_858_: u32 = 0;
    let mut v_stdout_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u32 = 0;
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: u8 = 0;
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_855_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_args_852_);
                v___x_856_ = l_IO_Process_output(v_args_852_, v___x_855_);
                if crate::leanh::lean_obj_tag(v___x_856_) == 0 {
                    v_a_857_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                    crate::leanh::lean_inc(v_a_857_);
                    crate::leanh::lean_dec_ref_known(v___x_856_, 1);
                    v_exitCode_858_ = crate::leanh::lean_ctor_get_uint32(
                        v_a_857_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_stdout_859_ = crate::leanh::lean_ctor_get(v_a_857_, 0);
                    v_stderr_860_ = crate::leanh::lean_ctor_get(v_a_857_, 1);
                    v___x_861_ = 0;
                    v___x_862_ = lean_uint32_dec_eq(v_exitCode_858_, v___x_861_);
                    if v___x_862_ == 0 {
                        crate::leanh::lean_inc_ref(v_stderr_860_);
                        crate::leanh::lean_inc_ref(v_stdout_859_);
                        crate::leanh::lean_dec(v_a_857_);
                        crate::leanh::lean_inc_ref(v_args_852_);
                        v___x_863_ = l_Lake_mkCmdLog(v_args_852_);
                        v___x_864_ = 0;
                        v___x_865_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_863_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_865_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_864_,
                        );
                        v___x_866_ = lean_array_get_size(v_a_853_);
                        v___x_885_ = lean_array_push(v_a_853_, v___x_865_);
                        v___x_886_ = lean_string_utf8_byte_size(v_stdout_859_);
                        v___x_887_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_888_ = lean_nat_dec_eq(v___x_886_, v___x_887_);
                        if v___x_888_ == 0 {
                            v___x_889_ = l_Lake_logOutput___redArg___closed__0;
                            v___x_890_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_890_, 0, v_stdout_859_);
                            crate::leanh::lean_ctor_set(v___x_890_, 1, v___x_887_);
                            crate::leanh::lean_ctor_set(v___x_890_, 2, v___x_886_);
                            v___x_891_ = l_String_Slice_trimAscii(v___x_890_);
                            v___x_892_ = l_String_Slice_toString(v___x_891_);
                            crate::leanh::lean_dec_ref(v___x_891_);
                            v___x_893_ = lean_string_append(v___x_889_, v___x_892_);
                            crate::leanh::lean_dec_ref(v___x_892_);
                            v___x_894_ = 1;
                            v___x_895_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_895_, 0, v___x_893_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_895_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_894_,
                            );
                            v___x_896_ = crate::leanh::lean_box(0);
                            v___x_897_ = lean_array_push(v___x_885_, v___x_895_);
                            v___x_898_ =
                                l_Lake_proc___lam__0(v_stderr_860_, v___x_896_, v___x_897_);
                            v___y_871_ = v___x_898_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_stdout_859_);
                            v___x_899_ = crate::leanh::lean_box(0);
                            v___x_900_ =
                                l_Lake_proc___lam__0(v_stderr_860_, v___x_899_, v___x_885_);
                            v___y_871_ = v___x_900_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_852_);
                        v___x_901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_901_, 0, v_a_857_);
                        crate::leanh::lean_ctor_set(v___x_901_, 1, v_a_853_);
                        return v___x_901_;
                    }
                } else {
                    v_a_902_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                    crate::leanh::lean_inc(v_a_902_);
                    crate::leanh::lean_dec_ref_known(v___x_856_, 1);
                    v_cmd_903_ = crate::leanh::lean_ctor_get(v_args_852_, 1);
                    crate::leanh::lean_inc_ref(v_cmd_903_);
                    crate::leanh::lean_dec_ref(v_args_852_);
                    v___x_904_ = lean_array_get_size(v_a_853_);
                    v___x_905_ = l_Lake_rawProc___lam__0___closed__0;
                    v___x_906_ = lean_string_append(v___x_905_, v_cmd_903_);
                    crate::leanh::lean_dec_ref(v_cmd_903_);
                    v___x_907_ = l_Lake_rawProc___lam__0___closed__1;
                    v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
                    v___x_909_ = lean_io_error_to_string(v_a_902_);
                    v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
                    crate::leanh::lean_dec_ref(v___x_909_);
                    v___x_911_ = 3;
                    v___x_912_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_912_, 0, v___x_910_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_912_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_911_,
                    );
                    v___x_913_ = lean_array_push(v_a_853_, v___x_912_);
                    v___x_914_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_914_, 0, v___x_904_);
                    crate::leanh::lean_ctor_set(v___x_914_, 1, v___x_913_);
                    return v___x_914_;
                }
            }
            1 => {
                v___x_869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_866_);
                crate::leanh::lean_ctor_set(v___x_869_, 1, v_a_868_);
                return v___x_869_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_871_) == 0 {
                    v_a_872_ = crate::leanh::lean_ctor_get(v___y_871_, 1);
                    crate::leanh::lean_inc(v_a_872_);
                    crate::leanh::lean_dec_ref_known(v___y_871_, 2);
                    v_cmd_873_ = crate::leanh::lean_ctor_get(v_args_852_, 1);
                    crate::leanh::lean_inc_ref(v_cmd_873_);
                    crate::leanh::lean_dec_ref(v_args_852_);
                    v___x_874_ = l_Lake_proc___closed__0;
                    v___x_875_ = lean_string_append(v___x_874_, v_cmd_873_);
                    crate::leanh::lean_dec_ref(v_cmd_873_);
                    v___x_876_ = l_Lake_proc___closed__1;
                    v___x_877_ = lean_string_append(v___x_875_, v___x_876_);
                    v___x_878_ = lean_uint32_to_nat(v_exitCode_858_);
                    v___x_879_ = l_Nat_reprFast(v___x_878_);
                    v___x_880_ = lean_string_append(v___x_877_, v___x_879_);
                    crate::leanh::lean_dec_ref(v___x_879_);
                    v___x_881_ = 3;
                    v___x_882_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_882_, 0, v___x_880_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_882_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_881_,
                    );
                    v___x_883_ = lean_array_push(v_a_872_, v___x_882_);
                    v_a_868_ = v___x_883_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_args_852_);
                    v_a_884_ = crate::leanh::lean_ctor_get(v___y_871_, 1);
                    crate::leanh::lean_inc(v_a_884_);
                    crate::leanh::lean_dec_ref_known(v___y_871_, 2);
                    v_a_868_ = v_a_884_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_captureProc_x27___boxed(
    mut v_args_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Lake_captureProc_x27(v_args_915_, v_a_916_);
    return v_res_918_;
}
pub unsafe fn l_Lake_captureProc(
    mut v_args_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v_stdout_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v_a_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_945_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_922_ = l_Lake_captureProc_x27(v_args_919_, v_a_920_);
                if crate::leanh::lean_obj_tag(v___x_922_) == 0 {
                    v_a_923_ = crate::leanh::lean_ctor_get(v___x_922_, 0);
                    v_a_924_ = crate::leanh::lean_ctor_get(v___x_922_, 1);
                    v_isSharedCheck_940_ = (!crate::leanh::lean_is_exclusive(v___x_922_)) as u8;
                    if v_isSharedCheck_940_ == 0 {
                        v___x_926_ = v___x_922_;
                        v_isShared_927_ = v_isSharedCheck_940_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_924_);
                        crate::leanh::lean_inc(v_a_923_);
                        crate::leanh::lean_dec(v___x_922_);
                        v___x_926_ = crate::leanh::lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_940_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_941_ = crate::leanh::lean_ctor_get(v___x_922_, 0);
                    v_a_942_ = crate::leanh::lean_ctor_get(v___x_922_, 1);
                    v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v___x_922_)) as u8;
                    if v_isSharedCheck_949_ == 0 {
                        v___x_944_ = v___x_922_;
                        v_isShared_945_ = v_isSharedCheck_949_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_942_);
                        crate::leanh::lean_inc(v_a_941_);
                        crate::leanh::lean_dec(v___x_922_);
                        v___x_944_ = crate::leanh::lean_box(0);
                        v_isShared_945_ = v_isSharedCheck_949_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_stdout_928_ = crate::leanh::lean_ctor_get(v_a_923_, 0);
                crate::leanh::lean_inc_ref(v_stdout_928_);
                crate::leanh::lean_dec(v_a_923_);
                v___x_929_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_930_ = lean_string_utf8_byte_size(v_stdout_928_);
                v___x_931_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_931_, 0, v_stdout_928_);
                crate::leanh::lean_ctor_set(v___x_931_, 1, v___x_929_);
                crate::leanh::lean_ctor_set(v___x_931_, 2, v___x_930_);
                v___x_932_ = l_String_Slice_trimAscii(v___x_931_);
                v_str_933_ = crate::leanh::lean_ctor_get(v___x_932_, 0);
                crate::leanh::lean_inc_ref(v_str_933_);
                v_startInclusive_934_ = crate::leanh::lean_ctor_get(v___x_932_, 1);
                crate::leanh::lean_inc(v_startInclusive_934_);
                v_endExclusive_935_ = crate::leanh::lean_ctor_get(v___x_932_, 2);
                crate::leanh::lean_inc(v_endExclusive_935_);
                crate::leanh::lean_dec_ref(v___x_932_);
                v___x_936_ = lean_string_utf8_extract(
                    v_str_933_,
                    v_startInclusive_934_,
                    v_endExclusive_935_,
                );
                crate::leanh::lean_dec(v_endExclusive_935_);
                crate::leanh::lean_dec(v_startInclusive_934_);
                crate::leanh::lean_dec_ref(v_str_933_);
                if v_isShared_927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_936_);
                    v___x_938_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 1, v_a_924_);
                    v___x_938_ = v_reuseFailAlloc_939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_938_;
            }
            3 => {
                if v_isShared_945_ == 0 {
                    v___x_947_ = v___x_944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 1, v_a_942_);
                    v___x_947_ = v_reuseFailAlloc_948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_captureProc___boxed(
    mut v_args_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Lake_captureProc(v_args_950_, v_a_951_);
    return v_res_953_;
}
pub unsafe fn l_Lake_captureProc_x3f(
    mut v_args_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v_exitCode_962_: u32 = 0;
    let mut v_stdout_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u32 = 0;
    let mut v___x_965_: u8 = 0;
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_956_ = crate::leanh::lean_box(0);
                v___x_957_ = l_IO_Process_output(v_args_954_, v___x_956_);
                if crate::leanh::lean_obj_tag(v___x_957_) == 0 {
                    v_a_958_ = crate::leanh::lean_ctor_get(v___x_957_, 0);
                    v_isSharedCheck_977_ = (!crate::leanh::lean_is_exclusive(v___x_957_)) as u8;
                    if v_isSharedCheck_977_ == 0 {
                        v___x_960_ = v___x_957_;
                        v_isShared_961_ = v_isSharedCheck_977_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_958_);
                        crate::leanh::lean_dec(v___x_957_);
                        v___x_960_ = crate::leanh::lean_box(0);
                        v_isShared_961_ = v_isSharedCheck_977_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_957_, 1);
                    return v___x_956_;
                }
            }
            1 => {
                v_exitCode_962_ = crate::leanh::lean_ctor_get_uint32(
                    v_a_958_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_stdout_963_ = crate::leanh::lean_ctor_get(v_a_958_, 0);
                crate::leanh::lean_inc_ref(v_stdout_963_);
                crate::leanh::lean_dec(v_a_958_);
                v___x_964_ = 0;
                v___x_965_ = lean_uint32_dec_eq(v_exitCode_962_, v___x_964_);
                if v___x_965_ == 0 {
                    crate::leanh::lean_dec_ref(v_stdout_963_);
                    crate::leanh::lean_del_object(v___x_960_);
                    return v___x_956_;
                } else {
                    v___x_966_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_967_ = lean_string_utf8_byte_size(v_stdout_963_);
                    v___x_968_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_968_, 0, v_stdout_963_);
                    crate::leanh::lean_ctor_set(v___x_968_, 1, v___x_966_);
                    crate::leanh::lean_ctor_set(v___x_968_, 2, v___x_967_);
                    v___x_969_ = l_String_Slice_trimAscii(v___x_968_);
                    v_str_970_ = crate::leanh::lean_ctor_get(v___x_969_, 0);
                    crate::leanh::lean_inc_ref(v_str_970_);
                    v_startInclusive_971_ = crate::leanh::lean_ctor_get(v___x_969_, 1);
                    crate::leanh::lean_inc(v_startInclusive_971_);
                    v_endExclusive_972_ = crate::leanh::lean_ctor_get(v___x_969_, 2);
                    crate::leanh::lean_inc(v_endExclusive_972_);
                    crate::leanh::lean_dec_ref(v___x_969_);
                    v___x_973_ = lean_string_utf8_extract(
                        v_str_970_,
                        v_startInclusive_971_,
                        v_endExclusive_972_,
                    );
                    crate::leanh::lean_dec(v_endExclusive_972_);
                    crate::leanh::lean_dec(v_startInclusive_971_);
                    crate::leanh::lean_dec_ref(v_str_970_);
                    if v_isShared_961_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_960_, 1);
                        crate::leanh::lean_ctor_set(v___x_960_, 0, v___x_973_);
                        v___x_975_ = v___x_960_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
                        v___x_975_ = v_reuseFailAlloc_976_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_captureProc_x3f___boxed(
    mut v_args_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_980_ = l_Lake_captureProc_x3f(v_args_978_);
    return v_res_980_;
}
pub unsafe fn l_Lake_testProc(mut v_args_983_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cwd_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritEnv_992_: u8 = 0;
    let mut v_setsid_993_: u8 = 0;
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u32 = 0;
    let mut v___x_1004_: u32 = 0;
    let mut v___x_1005_: u8 = 0;
    let mut v_reuseFailAlloc_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v_unused_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_987_ = l_Lake_testProc___closed__0;
                v_cmd_988_ = crate::leanh::lean_ctor_get(v_args_983_, 1);
                v_args_989_ = crate::leanh::lean_ctor_get(v_args_983_, 2);
                v_cwd_990_ = crate::leanh::lean_ctor_get(v_args_983_, 3);
                v_env_991_ = crate::leanh::lean_ctor_get(v_args_983_, 4);
                v_inheritEnv_992_ = crate::leanh::lean_ctor_get_uint8(
                    v_args_983_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_setsid_993_ = crate::leanh::lean_ctor_get_uint8(
                    v_args_983_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_isSharedCheck_1007_ = (!crate::leanh::lean_is_exclusive(v_args_983_)) as u8;
                if v_isSharedCheck_1007_ == 0 {
                    v_unused_1008_ = crate::leanh::lean_ctor_get(v_args_983_, 0);
                    crate::leanh::lean_dec(v_unused_1008_);
                    v___x_995_ = v_args_983_;
                    v_isShared_996_ = v_isSharedCheck_1007_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_env_991_);
                    crate::leanh::lean_inc(v_cwd_990_);
                    crate::leanh::lean_inc(v_args_989_);
                    crate::leanh::lean_inc(v_cmd_988_);
                    crate::leanh::lean_dec(v_args_983_);
                    v___x_995_ = crate::leanh::lean_box(0);
                    v_isShared_996_ = v_isSharedCheck_1007_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_986_ = 0;
                return v___x_986_;
            }
            2 => {
                if v_isShared_996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_987_);
                    v___x_998_ = v___x_995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_cmd_988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_args_989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_cwd_990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_env_991_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v_inheritEnv_992_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                        v_setsid_993_,
                    );
                    v___x_998_ = v_reuseFailAlloc_1006_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_999_ = lean_io_process_spawn(v___x_998_);
                if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                    v_a_1000_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                    crate::leanh::lean_inc(v_a_1000_);
                    crate::leanh::lean_dec_ref_known(v___x_999_, 1);
                    v___x_1001_ = lean_io_process_child_wait(v___x_987_, v_a_1000_);
                    crate::leanh::lean_dec(v_a_1000_);
                    if crate::leanh::lean_obj_tag(v___x_1001_) == 0 {
                        v_a_1002_ = crate::leanh::lean_ctor_get(v___x_1001_, 0);
                        crate::leanh::lean_inc(v_a_1002_);
                        crate::leanh::lean_dec_ref_known(v___x_1001_, 1);
                        v___x_1003_ = 0;
                        v___x_1004_ = crate::leanh::lean_unbox_uint32(v_a_1002_);
                        crate::leanh::lean_dec(v_a_1002_);
                        v___x_1005_ = lean_uint32_dec_eq(v___x_1004_, v___x_1003_);
                        return v___x_1005_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1001_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_999_, 1);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_testProc___boxed(
    mut v_args_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1011_: u8 = 0;
    let mut v_r_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ = l_Lake_testProc(v_args_1009_);
    v_r_1012_ = crate::leanh::lean_box((v_res_1011_) as usize);
    return v_r_1012_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Proc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Proc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Proc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Proc(builtin);
}
