// Lean compiler output
// Module: Std.Http.Internal.String
// Imports: Init.Grind Init.Data.String.TakeDrop Std.Http.Internal.Char
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Http::Internal::Char::{
    initialize_Std_Http_Internal_Char, runtime_initialize_Std_Http_Internal_Char,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_data, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le,
};
pub static l_Std_Http_Internal_quoteCore___redArg___closed__0_value:
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
static mut l_Std_Http_Internal_quoteCore___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteCore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_quoteCore___redArg___closed__1_value:
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
    m_data: [92, 0],
};
static mut l_Std_Http_Internal_quoteCore___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteCore___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value:
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
    m_data: [34, 0],
};
static mut l_Std_Http_Internal_quoteHttpString___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteHttpString___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_quoteHttpString_x21___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 83, 116,
        114, 105, 110, 103, 0,
    ],
};
static mut l_Std_Http_Internal_quoteHttpString_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteHttpString_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_quoteHttpString_x21___closed__1_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 113,
        117, 111, 116, 101, 72, 116, 116, 112, 83, 116, 114, 105, 110, 103, 33, 0,
    ],
};
static mut l_Std_Http_Internal_quoteHttpString_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteHttpString_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_quoteHttpString_x21___closed__2_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 72, 84, 84, 80, 32, 113, 117, 111, 116, 101, 100, 45,
        115, 116, 114, 105, 110, 103, 32, 99, 111, 110, 116, 101, 110, 116, 0,
    ],
};
static mut l_Std_Http_Internal_quoteHttpString_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_quoteHttpString_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Internal_quoteHttpString_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_quoteHttpString_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Http_Internal_quoteCore___redArg(
    mut v_c_587_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u32 = 0;
    let mut v___x_598_: u8 = 0;
    let mut v___x_599_: u32 = 0;
    let mut v___x_600_: u8 = 0;
    let mut v___x_602_: u32 = 0;
    let mut v___x_603_: u8 = 0;
    let mut v___x_604_: u32 = 0;
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: u32 = 0;
    let mut v___x_607_: u8 = 0;
    let mut v___x_608_: u32 = 0;
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: u32 = 0;
    let mut v___x_611_: u8 = 0;
    let mut v___x_612_: u32 = 0;
    let mut v___x_613_: u8 = 0;
    let mut v___x_614_: u32 = 0;
    let mut v___x_615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_606_ = 9;
                v___x_607_ = lean_uint32_dec_eq(v_c_587_, v___x_606_);
                if v___x_607_ == 0 {
                    v___x_608_ = 32;
                    v___x_609_ = lean_uint32_dec_eq(v_c_587_, v___x_608_);
                    if v___x_609_ == 0 {
                        v___x_610_ = 33;
                        v___x_611_ = lean_uint32_dec_eq(v_c_587_, v___x_610_);
                        if v___x_611_ == 0 {
                            v___x_612_ = 35;
                            v___x_613_ = lean_uint32_dec_le(v___x_612_, v_c_587_);
                            if v___x_613_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_614_ = 91;
                                v___x_615_ = lean_uint32_dec_le(v_c_587_, v___x_614_);
                                if v___x_615_ == 0 {
                                    state = 4;
                                    continue;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_589_ = l_Std_Http_Internal_quoteCore___redArg___closed__0;
                v___x_590_ = lean_string_push(v___x_589_, v_c_587_);
                return v___x_590_;
            }
            2 => {
                v___x_592_ = l_Std_Http_Internal_quoteCore___redArg___closed__1;
                v___x_593_ = l_Std_Http_Internal_quoteCore___redArg___closed__0;
                v___x_594_ = lean_string_push(v___x_593_, v_c_587_);
                v___x_595_ = lean_string_append(v___x_592_, v___x_594_);
                crate::leanh::lean_dec_ref(v___x_594_);
                return v___x_595_;
            }
            3 => {
                v___x_597_ = 34;
                v___x_598_ = lean_uint32_dec_eq(v_c_587_, v___x_597_);
                if v___x_598_ == 0 {
                    v___x_599_ = 92;
                    v___x_600_ = lean_uint32_dec_eq(v_c_587_, v___x_599_);
                    state = 2;
                    continue;
                } else {
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_602_ = 93;
                v___x_603_ = lean_uint32_dec_le(v___x_602_, v_c_587_);
                if v___x_603_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_604_ = 126;
                    v___x_605_ = lean_uint32_dec_le(v_c_587_, v___x_604_);
                    if v___x_605_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_quoteCore___redArg___boxed(
    mut v_c_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_617_: u32 = 0;
    let mut v_res_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_617_ = crate::leanh::lean_unbox_uint32(v_c_616_);
    crate::leanh::lean_dec(v_c_616_);
    v_res_618_ = l_Std_Http_Internal_quoteCore___redArg(v_c_boxed_617_);
    return v_res_618_;
}
pub unsafe fn l_Std_Http_Internal_quoteCore(
    mut v_c_619_: u32,
    mut v_h_u2080_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_621_ = l_Std_Http_Internal_quoteCore___redArg(v_c_619_);
    return v___x_621_;
}
pub unsafe fn l_Std_Http_Internal_quoteCore___boxed(
    mut v_c_622_: *mut crate::leanh::LeanObject,
    mut v_h_u2080_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_624_: u32 = 0;
    let mut v_res_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_624_ = crate::leanh::lean_unbox_uint32(v_c_622_);
    crate::leanh::lean_dec(v_c_622_);
    v_res_625_ = l_Std_Http_Internal_quoteCore(v_c_boxed_624_, v_h_u2080_623_);
    return v_res_625_;
}
pub unsafe fn l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(
    mut v_x_626_: *mut crate::leanh::LeanObject,
    mut v_x_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u32 = 0;
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_627_) == 0 {
                    return v_x_626_;
                } else {
                    v_head_628_ = crate::leanh::lean_ctor_get(v_x_627_, 0);
                    v_tail_629_ = crate::leanh::lean_ctor_get(v_x_627_, 1);
                    v___x_630_ = crate::leanh::lean_unbox_uint32(v_head_628_);
                    v___x_631_ = l_Std_Http_Internal_quoteCore___redArg(v___x_630_);
                    v___x_632_ = lean_string_append(v_x_626_, v___x_631_);
                    crate::leanh::lean_dec_ref(v___x_631_);
                    v_x_626_ = v___x_632_;
                    v_x_627_ = v_tail_629_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0___boxed(
    mut v_x_634_: *mut crate::leanh::LeanObject,
    mut v_x_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_636_ =
        l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(v_x_634_, v_x_635_);
    crate::leanh::lean_dec(v_x_635_);
    return v_res_636_;
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(
    mut v_x_637_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_638_: u8 = 0;
    let mut v_head_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_642_: u8 = 0;
    let mut v___x_645_: u32 = 0;
    let mut v___x_646_: u32 = 0;
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u32 = 0;
    let mut v___x_649_: u32 = 0;
    let mut v___x_650_: u8 = 0;
    let mut v___y_652_: u8 = 0;
    let mut v___x_653_: u32 = 0;
    let mut v___x_654_: u32 = 0;
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: u32 = 0;
    let mut v___x_657_: u32 = 0;
    let mut v___x_658_: u8 = 0;
    let mut v___x_661_: u32 = 0;
    let mut v___x_662_: u32 = 0;
    let mut v___x_663_: u8 = 0;
    let mut v___x_664_: u32 = 0;
    let mut v___x_665_: u32 = 0;
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: u32 = 0;
    let mut v___x_668_: u32 = 0;
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: u32 = 0;
    let mut v___x_671_: u32 = 0;
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: u32 = 0;
    let mut v___x_674_: u32 = 0;
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: u32 = 0;
    let mut v___x_677_: u32 = 0;
    let mut v___x_678_: u8 = 0;
    let mut v___x_679_: u32 = 0;
    let mut v___x_680_: u32 = 0;
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: u32 = 0;
    let mut v___x_683_: u32 = 0;
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: u32 = 0;
    let mut v___x_686_: u32 = 0;
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u32 = 0;
    let mut v___x_689_: u32 = 0;
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: u32 = 0;
    let mut v___x_692_: u32 = 0;
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: u32 = 0;
    let mut v___x_695_: u32 = 0;
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: u32 = 0;
    let mut v___x_698_: u32 = 0;
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: u32 = 0;
    let mut v___x_701_: u32 = 0;
    let mut v___x_702_: u8 = 0;
    let mut v___x_703_: u32 = 0;
    let mut v___x_704_: u32 = 0;
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: u32 = 0;
    let mut v___x_707_: u32 = 0;
    let mut v___x_708_: u8 = 0;
    let mut v___x_709_: u32 = 0;
    let mut v___x_710_: u32 = 0;
    let mut v___x_711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_637_) == 0 {
                    v___x_638_ = 1;
                    return v___x_638_;
                } else {
                    v_head_639_ = crate::leanh::lean_ctor_get(v_x_637_, 0);
                    v_tail_640_ = crate::leanh::lean_ctor_get(v_x_637_, 1);
                    v___x_661_ = 33;
                    v___x_662_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                    v___x_663_ = lean_uint32_dec_eq(v___x_662_, v___x_661_);
                    if v___x_663_ == 0 {
                        v___x_664_ = 35;
                        v___x_665_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                        v___x_666_ = lean_uint32_dec_eq(v___x_665_, v___x_664_);
                        if v___x_666_ == 0 {
                            v___x_667_ = 36;
                            v___x_668_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                            v___x_669_ = lean_uint32_dec_eq(v___x_668_, v___x_667_);
                            if v___x_669_ == 0 {
                                v___x_670_ = 37;
                                v___x_671_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                v___x_672_ = lean_uint32_dec_eq(v___x_671_, v___x_670_);
                                if v___x_672_ == 0 {
                                    v___x_673_ = 38;
                                    v___x_674_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                    v___x_675_ = lean_uint32_dec_eq(v___x_674_, v___x_673_);
                                    if v___x_675_ == 0 {
                                        v___x_676_ = 39;
                                        v___x_677_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                        v___x_678_ = lean_uint32_dec_eq(v___x_677_, v___x_676_);
                                        if v___x_678_ == 0 {
                                            v___x_679_ = 42;
                                            v___x_680_ =
                                                crate::leanh::lean_unbox_uint32(v_head_639_);
                                            v___x_681_ = lean_uint32_dec_eq(v___x_680_, v___x_679_);
                                            if v___x_681_ == 0 {
                                                v___x_682_ = 43;
                                                v___x_683_ =
                                                    crate::leanh::lean_unbox_uint32(v_head_639_);
                                                v___x_684_ =
                                                    lean_uint32_dec_eq(v___x_683_, v___x_682_);
                                                if v___x_684_ == 0 {
                                                    v___x_685_ = 45;
                                                    v___x_686_ = crate::leanh::lean_unbox_uint32(
                                                        v_head_639_,
                                                    );
                                                    v___x_687_ =
                                                        lean_uint32_dec_eq(v___x_686_, v___x_685_);
                                                    if v___x_687_ == 0 {
                                                        v___x_688_ = 46;
                                                        v___x_689_ =
                                                            crate::leanh::lean_unbox_uint32(
                                                                v_head_639_,
                                                            );
                                                        v___x_690_ = lean_uint32_dec_eq(
                                                            v___x_689_, v___x_688_,
                                                        );
                                                        if v___x_690_ == 0 {
                                                            v___x_691_ = 94;
                                                            v___x_692_ =
                                                                crate::leanh::lean_unbox_uint32(
                                                                    v_head_639_,
                                                                );
                                                            v___x_693_ = lean_uint32_dec_eq(
                                                                v___x_692_, v___x_691_,
                                                            );
                                                            if v___x_693_ == 0 {
                                                                v___x_694_ = 95;
                                                                v___x_695_ =
                                                                    crate::leanh::lean_unbox_uint32(
                                                                        v_head_639_,
                                                                    );
                                                                v___x_696_ = lean_uint32_dec_eq(
                                                                    v___x_695_, v___x_694_,
                                                                );
                                                                if v___x_696_ == 0 {
                                                                    v___x_697_ = 96;
                                                                    v___x_698_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                                                    v___x_699_ = lean_uint32_dec_eq(
                                                                        v___x_698_, v___x_697_,
                                                                    );
                                                                    if v___x_699_ == 0 {
                                                                        v___x_700_ = 124;
                                                                        v___x_701_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                                                        v___x_702_ =
                                                                            lean_uint32_dec_eq(
                                                                                v___x_701_,
                                                                                v___x_700_,
                                                                            );
                                                                        if v___x_702_ == 0 {
                                                                            v___x_703_ = 126;
                                                                            v___x_704_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                                                            v___x_705_ =
                                                                                lean_uint32_dec_eq(
                                                                                    v___x_704_,
                                                                                    v___x_703_,
                                                                                );
                                                                            if v___x_705_ == 0 {
                                                                                v___x_706_ = 48;
                                                                                v___x_707_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                                                                v___x_708_ = lean_uint32_dec_le(v___x_706_, v___x_707_);
                                                                                if v___x_708_ == 0 {
                                                                                    v___y_652_ =
                                                                                        v___x_708_;
                                                                                    state = 3;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_709_ = 57;
                                                                                    v___x_710_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                                                                                    v___x_711_ = lean_uint32_dec_le(v___x_710_, v___x_709_);
                                                                                    v___y_652_ =
                                                                                        v___x_711_;
                                                                                    state = 3;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                v_x_637_ =
                                                                                    v_tail_640_;
                                                                                state = 0;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            v_x_637_ = v_tail_640_;
                                                                            state = 0;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_x_637_ = v_tail_640_;
                                                                        state = 0;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    v_x_637_ = v_tail_640_;
                                                                    state = 0;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_x_637_ = v_tail_640_;
                                                                state = 0;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_x_637_ = v_tail_640_;
                                                            state = 0;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_x_637_ = v_tail_640_;
                                                        state = 0;
                                                        continue;
                                                    }
                                                } else {
                                                    v_x_637_ = v_tail_640_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                v_x_637_ = v_tail_640_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            v_x_637_ = v_tail_640_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        v_x_637_ = v_tail_640_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    v_x_637_ = v_tail_640_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v_x_637_ = v_tail_640_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_637_ = v_tail_640_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_637_ = v_tail_640_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_642_ == 0 {
                    return v___y_642_;
                } else {
                    v_x_637_ = v_tail_640_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_645_ = 97;
                v___x_646_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                v___x_647_ = lean_uint32_dec_le(v___x_645_, v___x_646_);
                if v___x_647_ == 0 {
                    v___y_642_ = v___x_647_;
                    state = 1;
                    continue;
                } else {
                    v___x_648_ = 122;
                    v___x_649_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                    v___x_650_ = lean_uint32_dec_le(v___x_649_, v___x_648_);
                    v___y_642_ = v___x_650_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_652_ == 0 {
                    v___x_653_ = 65;
                    v___x_654_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                    v___x_655_ = lean_uint32_dec_le(v___x_653_, v___x_654_);
                    if v___x_655_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_656_ = 90;
                        v___x_657_ = crate::leanh::lean_unbox_uint32(v_head_639_);
                        v___x_658_ = lean_uint32_dec_le(v___x_657_, v___x_656_);
                        if v___x_658_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_x_637_ = v_tail_640_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v_x_637_ = v_tail_640_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1___boxed(
    mut v_x_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_728_: u8 = 0;
    let mut v_r_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_728_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_x_727_);
    crate::leanh::lean_dec(v_x_727_);
    v_r_729_ = crate::leanh::lean_box((v_res_728_) as usize);
    return v_r_729_;
}
pub unsafe fn l_Std_Http_Internal_quoteHttpString___redArg(
    mut v_s_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sl_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_s_731_);
                v_sl_732_ = lean_string_data(v_s_731_);
                v___x_737_ =
                    l_List_all___at___00Std_Http_Internal_quoteHttpString_spec__1(v_sl_732_);
                if v___x_737_ == 0 {
                    crate::leanh::lean_dec_ref(v_s_731_);
                    state = 1;
                    continue;
                } else {
                    v___x_738_ = l_List_isEmpty___redArg(v_sl_732_);
                    if v___x_738_ == 0 {
                        crate::leanh::lean_dec(v_sl_732_);
                        return v_s_731_;
                    } else {
                        crate::leanh::lean_dec_ref(v_s_731_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_734_ = l_Std_Http_Internal_quoteHttpString___redArg___closed__0;
                v___x_735_ = l_List_foldl___at___00Std_Http_Internal_quoteHttpString_spec__0(
                    v___x_734_, v_sl_732_,
                );
                crate::leanh::lean_dec(v_sl_732_);
                v___x_736_ = lean_string_append(v___x_735_, v___x_734_);
                return v___x_736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_quoteHttpString(
    mut v_s_739_: *mut crate::leanh::LeanObject,
    mut v_h_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_739_);
    return v___x_741_;
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(
    mut v_x_742_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_743_: u8 = 0;
    let mut v_head_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: u32 = 0;
    let mut v___x_748_: u32 = 0;
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: u32 = 0;
    let mut v___x_751_: u32 = 0;
    let mut v___x_752_: u8 = 0;
    let mut v___x_753_: u32 = 0;
    let mut v___x_754_: u32 = 0;
    let mut v___x_755_: u8 = 0;
    let mut v___x_756_: u32 = 0;
    let mut v___x_757_: u32 = 0;
    let mut v___x_758_: u8 = 0;
    let mut v___x_763_: u32 = 0;
    let mut v___x_764_: u32 = 0;
    let mut v___x_765_: u8 = 0;
    let mut v___x_766_: u32 = 0;
    let mut v___x_767_: u32 = 0;
    let mut v___x_768_: u8 = 0;
    let mut v___x_770_: u32 = 0;
    let mut v___x_771_: u32 = 0;
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: u32 = 0;
    let mut v___x_774_: u32 = 0;
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: u32 = 0;
    let mut v___x_777_: u32 = 0;
    let mut v___x_778_: u8 = 0;
    let mut v___x_779_: u32 = 0;
    let mut v___x_780_: u32 = 0;
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: u32 = 0;
    let mut v___x_783_: u32 = 0;
    let mut v___x_784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_742_) == 0 {
                    v___x_743_ = 1;
                    return v___x_743_;
                } else {
                    v_head_744_ = crate::leanh::lean_ctor_get(v_x_742_, 0);
                    v_tail_745_ = crate::leanh::lean_ctor_get(v_x_742_, 1);
                    v___x_770_ = 9;
                    v___x_771_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                    v___x_772_ = lean_uint32_dec_eq(v___x_771_, v___x_770_);
                    if v___x_772_ == 0 {
                        v___x_773_ = 32;
                        v___x_774_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                        v___x_775_ = lean_uint32_dec_eq(v___x_774_, v___x_773_);
                        if v___x_775_ == 0 {
                            v___x_776_ = 33;
                            v___x_777_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                            v___x_778_ = lean_uint32_dec_eq(v___x_777_, v___x_776_);
                            if v___x_778_ == 0 {
                                v___x_779_ = 35;
                                v___x_780_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                                v___x_781_ = lean_uint32_dec_le(v___x_779_, v___x_780_);
                                if v___x_781_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_782_ = 91;
                                    v___x_783_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                                    v___x_784_ = lean_uint32_dec_le(v___x_783_, v___x_782_);
                                    if v___x_784_ == 0 {
                                        state = 2;
                                        continue;
                                    } else {
                                        v_x_742_ = v_tail_745_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                v_x_742_ = v_tail_745_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_742_ = v_tail_745_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_742_ = v_tail_745_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_747_ = 9;
                v___x_748_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                v___x_749_ = lean_uint32_dec_eq(v___x_748_, v___x_747_);
                if v___x_749_ == 0 {
                    v___x_750_ = 32;
                    v___x_751_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                    v___x_752_ = lean_uint32_dec_eq(v___x_751_, v___x_750_);
                    if v___x_752_ == 0 {
                        v___x_753_ = 33;
                        v___x_754_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                        v___x_755_ = lean_uint32_dec_le(v___x_753_, v___x_754_);
                        if v___x_755_ == 0 {
                            return v___x_755_;
                        } else {
                            v___x_756_ = 126;
                            v___x_757_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                            v___x_758_ = lean_uint32_dec_le(v___x_757_, v___x_756_);
                            if v___x_758_ == 0 {
                                return v___x_758_;
                            } else {
                                v_x_742_ = v_tail_745_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v_x_742_ = v_tail_745_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_x_742_ = v_tail_745_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_763_ = 93;
                v___x_764_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                v___x_765_ = lean_uint32_dec_le(v___x_763_, v___x_764_);
                if v___x_765_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_766_ = 126;
                    v___x_767_ = crate::leanh::lean_unbox_uint32(v_head_744_);
                    v___x_768_ = lean_uint32_dec_le(v___x_767_, v___x_766_);
                    if v___x_768_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_x_742_ = v_tail_745_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0___boxed(
    mut v_x_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: u8 = 0;
    let mut v_r_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v_x_789_);
    crate::leanh::lean_dec(v_x_789_);
    v_r_791_ = crate::leanh::lean_box((v_res_790_) as usize);
    return v_r_791_;
}
pub unsafe fn l_Std_Http_Internal_quoteHttpString_x3f(
    mut v_s_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    crate::leanh::lean_inc_ref(v_s_792_);
    v___x_793_ = lean_string_data(v_s_792_);
    v___x_794_ = l_List_all___at___00Std_Http_Internal_quoteHttpString_x3f_spec__0(v___x_793_);
    crate::leanh::lean_dec(v___x_793_);
    if v___x_794_ == 0 {
        let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_792_);
        v___x_795_ = crate::leanh::lean_box(0);
        return v___x_795_;
    } else {
        let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_796_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_792_);
        v___x_797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
        return v___x_797_;
    }
}
pub unsafe fn l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(
    mut v_msg_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Std_Http_Internal_quoteCore___redArg___closed__0;
    v___x_800_ = lean_panic_fn_borrowed(v___x_799_, v_msg_798_);
    return v___x_800_;
}
pub unsafe fn _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Std_Http_Internal_quoteHttpString_x21___closed__2;
    v___x_805_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_806_ = crate::leanh::lean_unsigned_to_nat(83);
    v___x_807_ = l_Std_Http_Internal_quoteHttpString_x21___closed__1;
    v___x_808_ = l_Std_Http_Internal_quoteHttpString_x21___closed__0;
    v___x_809_ =
        l_mkPanicMessageWithDecl(v___x_808_, v___x_807_, v___x_806_, v___x_805_, v___x_804_);
    return v___x_809_;
}
pub unsafe fn l_Std_Http_Internal_quoteHttpString_x21(
    mut v_s_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Std_Http_Internal_quoteHttpString_x3f(v_s_810_);
    if crate::leanh::lean_obj_tag(v___x_811_) == 0 {
        let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_812_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_Internal_quoteHttpString_x21___closed__3),
            core::ptr::addr_of_mut!(l_Std_Http_Internal_quoteHttpString_x21___closed__3_once),
            _init_l_Std_Http_Internal_quoteHttpString_x21___closed__3,
        );
        v___x_813_ = l_panic___at___00Std_Http_Internal_quoteHttpString_x21_spec__0(v___x_812_);
        return v___x_813_;
    } else {
        let mut v_val_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_814_ = crate::leanh::lean_ctor_get(v___x_811_, 0);
        crate::leanh::lean_inc(v_val_814_);
        crate::leanh::lean_dec_ref_known(v___x_811_, 1);
        return v_val_814_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(
    mut v_x_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_815_) {
        0 => {
            let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_816_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_816_;
        }
        1 => {
            let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_817_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_817_;
        }
        2 => {
            let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_818_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_818_;
        }
        _ => {
            let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_819_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_819_;
        }
    }
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx___boxed(
    mut v_x_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_821_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorIdx(v_x_820_);
    crate::leanh::lean_dec(v_x_820_);
    return v_res_821_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
    mut v_t_822_: *mut crate::leanh::LeanObject,
    mut v_k_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_822_) {
        1 => {
            let mut v_escaped_824_: u8 = 0;
            let mut v_acc_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_escaped_824_ = crate::leanh::lean_ctor_get_uint8(
                v_t_822_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            );
            v_acc_825_ = crate::leanh::lean_ctor_get(v_t_822_, 0);
            crate::leanh::lean_inc_ref(v_acc_825_);
            crate::leanh::lean_dec_ref_known(v_t_822_, 1);
            v___x_826_ = crate::leanh::lean_box((v_escaped_824_) as usize);
            v___x_827_ = crate::leanh::lean_apply_2(v_k_823_, v___x_826_, v_acc_825_);
            return v___x_827_;
        }
        2 => {
            let mut v_result_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_result_828_ = crate::leanh::lean_ctor_get(v_t_822_, 0);
            crate::leanh::lean_inc_ref(v_result_828_);
            crate::leanh::lean_dec_ref_known(v_t_822_, 1);
            v___x_829_ = crate::leanh::lean_apply_1(v_k_823_, v_result_828_);
            return v___x_829_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_822_);
            return v_k_823_;
        }
    }
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(
    mut v_motive_830_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_831_: *mut crate::leanh::LeanObject,
    mut v_t_832_: *mut crate::leanh::LeanObject,
    mut v_h_833_: *mut crate::leanh::LeanObject,
    mut v_k_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_832_, v_k_834_,
        );
    return v___x_835_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___boxed(
    mut v_motive_836_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_837_: *mut crate::leanh::LeanObject,
    mut v_t_838_: *mut crate::leanh::LeanObject,
    mut v_h_839_: *mut crate::leanh::LeanObject,
    mut v_k_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_841_ = l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim(
        v_motive_836_,
        v_ctorIdx_837_,
        v_t_838_,
        v_h_839_,
        v_k_840_,
    );
    crate::leanh::lean_dec(v_ctorIdx_837_);
    return v_res_841_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim___redArg(
    mut v_t_842_: *mut crate::leanh::LeanObject,
    mut v_start_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_842_,
            v_start_843_,
        );
    return v___x_844_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_start_elim(
    mut v_motive_845_: *mut crate::leanh::LeanObject,
    mut v_t_846_: *mut crate::leanh::LeanObject,
    mut v_h_847_: *mut crate::leanh::LeanObject,
    mut v_start_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_846_,
            v_start_848_,
        );
    return v___x_849_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim___redArg(
    mut v_t_850_: *mut crate::leanh::LeanObject,
    mut v_valid_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_850_,
            v_valid_851_,
        );
    return v___x_852_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_valid_elim(
    mut v_motive_853_: *mut crate::leanh::LeanObject,
    mut v_t_854_: *mut crate::leanh::LeanObject,
    mut v_h_855_: *mut crate::leanh::LeanObject,
    mut v_valid_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_854_,
            v_valid_856_,
        );
    return v___x_857_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim___redArg(
    mut v_t_858_: *mut crate::leanh::LeanObject,
    mut v_done_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_858_,
            v_done_859_,
        );
    return v___x_860_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_done_elim(
    mut v_motive_861_: *mut crate::leanh::LeanObject,
    mut v_t_862_: *mut crate::leanh::LeanObject,
    mut v_h_863_: *mut crate::leanh::LeanObject,
    mut v_done_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_862_,
            v_done_864_,
        );
    return v___x_865_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim___redArg(
    mut v_t_866_: *mut crate::leanh::LeanObject,
    mut v_invalid_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_866_,
            v_invalid_867_,
        );
    return v___x_868_;
}
pub unsafe fn l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_invalid_elim(
    mut v_motive_869_: *mut crate::leanh::LeanObject,
    mut v_t_870_: *mut crate::leanh::LeanObject,
    mut v_h_871_: *mut crate::leanh::LeanObject,
    mut v_invalid_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_873_ =
        l___private_Std_Http_Internal_String_0__Std_Http_Internal_UnquoteState_ctorElim___redArg(
            v_t_870_,
            v_invalid_872_,
        );
    return v___x_873_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(
    mut v_s_874_: *mut crate::leanh::LeanObject,
    mut v_pos_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___y_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_891_: u32 = 0;
    let mut v___x_893_: u32 = 0;
    let mut v___x_894_: u8 = 0;
    let mut v___x_895_: u32 = 0;
    let mut v___x_896_: u8 = 0;
    let mut v___y_898_: u8 = 0;
    let mut v___x_899_: u32 = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u32 = 0;
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: u32 = 0;
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: u32 = 0;
    let mut v___x_906_: u8 = 0;
    let mut v___x_907_: u32 = 0;
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: u32 = 0;
    let mut v___x_910_: u8 = 0;
    let mut v___x_911_: u32 = 0;
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: u32 = 0;
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: u32 = 0;
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: u32 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: u32 = 0;
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: u32 = 0;
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: u32 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: u32 = 0;
    let mut v___x_926_: u8 = 0;
    let mut v___x_927_: u32 = 0;
    let mut v___x_928_: u8 = 0;
    let mut v___x_929_: u32 = 0;
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: u32 = 0;
    let mut v___x_932_: u8 = 0;
    let mut v___x_933_: u32 = 0;
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: u32 = 0;
    let mut v___x_936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_876_ = crate::leanh::lean_ctor_get(v_s_874_, 0);
                v_startInclusive_877_ = crate::leanh::lean_ctor_get(v_s_874_, 1);
                v_endExclusive_878_ = crate::leanh::lean_ctor_get(v_s_874_, 2);
                v___x_879_ = lean_nat_add(v_startInclusive_877_, v_pos_875_);
                v___x_888_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_889_ = lean_nat_sub(v_endExclusive_878_, v___x_879_);
                v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
                crate::leanh::lean_dec(v___x_889_);
                if v___x_890_ == 0 {
                    v___x_891_ = lean_string_utf8_get_fast(v_str_876_, v___x_879_);
                    v___x_903_ = 33;
                    v___x_904_ = lean_uint32_dec_eq(v___x_891_, v___x_903_);
                    if v___x_904_ == 0 {
                        v___x_905_ = 35;
                        v___x_906_ = lean_uint32_dec_eq(v___x_891_, v___x_905_);
                        if v___x_906_ == 0 {
                            v___x_907_ = 36;
                            v___x_908_ = lean_uint32_dec_eq(v___x_891_, v___x_907_);
                            if v___x_908_ == 0 {
                                v___x_909_ = 37;
                                v___x_910_ = lean_uint32_dec_eq(v___x_891_, v___x_909_);
                                if v___x_910_ == 0 {
                                    v___x_911_ = 38;
                                    v___x_912_ = lean_uint32_dec_eq(v___x_891_, v___x_911_);
                                    if v___x_912_ == 0 {
                                        v___x_913_ = 39;
                                        v___x_914_ = lean_uint32_dec_eq(v___x_891_, v___x_913_);
                                        if v___x_914_ == 0 {
                                            v___x_915_ = 42;
                                            v___x_916_ = lean_uint32_dec_eq(v___x_891_, v___x_915_);
                                            if v___x_916_ == 0 {
                                                v___x_917_ = 43;
                                                v___x_918_ =
                                                    lean_uint32_dec_eq(v___x_891_, v___x_917_);
                                                if v___x_918_ == 0 {
                                                    v___x_919_ = 45;
                                                    v___x_920_ =
                                                        lean_uint32_dec_eq(v___x_891_, v___x_919_);
                                                    if v___x_920_ == 0 {
                                                        v___x_921_ = 46;
                                                        v___x_922_ = lean_uint32_dec_eq(
                                                            v___x_891_, v___x_921_,
                                                        );
                                                        if v___x_922_ == 0 {
                                                            v___x_923_ = 94;
                                                            v___x_924_ = lean_uint32_dec_eq(
                                                                v___x_891_, v___x_923_,
                                                            );
                                                            if v___x_924_ == 0 {
                                                                v___x_925_ = 95;
                                                                v___x_926_ = lean_uint32_dec_eq(
                                                                    v___x_891_, v___x_925_,
                                                                );
                                                                if v___x_926_ == 0 {
                                                                    v___x_927_ = 96;
                                                                    v___x_928_ = lean_uint32_dec_eq(
                                                                        v___x_891_, v___x_927_,
                                                                    );
                                                                    if v___x_928_ == 0 {
                                                                        v___x_929_ = 124;
                                                                        v___x_930_ =
                                                                            lean_uint32_dec_eq(
                                                                                v___x_891_,
                                                                                v___x_929_,
                                                                            );
                                                                        if v___x_930_ == 0 {
                                                                            v___x_931_ = 126;
                                                                            v___x_932_ =
                                                                                lean_uint32_dec_eq(
                                                                                    v___x_891_,
                                                                                    v___x_931_,
                                                                                );
                                                                            if v___x_932_ == 0 {
                                                                                v___x_933_ = 48;
                                                                                v___x_934_ = lean_uint32_dec_le(v___x_933_, v___x_891_);
                                                                                if v___x_934_ == 0 {
                                                                                    v___y_898_ =
                                                                                        v___x_934_;
                                                                                    state = 4;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_935_ = 57;
                                                                                    v___x_936_ = lean_uint32_dec_le(v___x_891_, v___x_935_);
                                                                                    v___y_898_ =
                                                                                        v___x_936_;
                                                                                    state = 4;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                state = 1;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            } else {
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    state = 1;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_879_);
                    return v_pos_875_;
                }
            }
            1 => {
                v___x_881_ = lean_string_utf8_next_fast(v_str_876_, v___x_879_);
                v___x_882_ = lean_nat_sub(v___x_881_, v___x_879_);
                crate::leanh::lean_dec(v___x_879_);
                v___x_883_ = lean_nat_add(v_pos_875_, v___x_882_);
                crate::leanh::lean_dec(v___x_882_);
                v___x_884_ = lean_nat_dec_lt(v_pos_875_, v___x_883_);
                if v___x_884_ == 0 {
                    crate::leanh::lean_dec(v___x_883_);
                    return v_pos_875_;
                } else {
                    crate::leanh::lean_dec(v_pos_875_);
                    v_pos_875_ = v___x_883_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_887_ == 0 {
                    crate::leanh::lean_dec(v___x_879_);
                    return v_pos_875_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_893_ = 97;
                v___x_894_ = lean_uint32_dec_le(v___x_893_, v___x_891_);
                if v___x_894_ == 0 {
                    v___y_887_ = v___x_894_;
                    state = 2;
                    continue;
                } else {
                    v___x_895_ = 122;
                    v___x_896_ = lean_uint32_dec_le(v___x_891_, v___x_895_);
                    v___y_887_ = v___x_896_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_898_ == 0 {
                    v___x_899_ = 65;
                    v___x_900_ = lean_uint32_dec_le(v___x_899_, v___x_891_);
                    if v___x_900_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_901_ = 90;
                        v___x_902_ = lean_uint32_dec_le(v___x_891_, v___x_901_);
                        if v___x_902_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
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
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0___boxed(
    mut v_s_937_: *mut crate::leanh::LeanObject,
    mut v_pos_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_939_ =
        l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(
            v_s_937_, v_pos_938_,
        );
    crate::leanh::lean_dec_ref(v_s_937_);
    return v_res_939_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(
    mut v___x_940_: u32,
    mut v___x_941_: *mut crate::leanh::LeanObject,
    mut v_s_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_b_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: u32 = 0;
    let mut v___x_950_: u32 = 0;
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_escaped_964_: u8 = 0;
    let mut v_acc_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_968_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u32 = 0;
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: u32 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: u32 = 0;
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u32 = 0;
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: u32 = 0;
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: u32 = 0;
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: u32 = 0;
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: u32 = 0;
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u32 = 0;
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: u32 = 0;
    let mut v___x_1005_: u8 = 0;
    let mut v___x_1006_: u32 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: u32 = 0;
    let mut v___x_1009_: u8 = 0;
    let mut v_isSharedCheck_1010_: u8 = 0;
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_945_ = crate::leanh::lean_ctor_get(v___x_941_, 1);
                v_endExclusive_946_ = crate::leanh::lean_ctor_get(v___x_941_, 2);
                v___x_947_ = lean_nat_sub(v_endExclusive_946_, v_startInclusive_945_);
                v___x_948_ = lean_nat_dec_eq(v_a_943_, v___x_947_);
                crate::leanh::lean_dec(v___x_947_);
                if v___x_948_ == 0 {
                    v___x_949_ = 34;
                    v___x_950_ = lean_string_utf8_get_fast(v_s_942_, v_a_943_);
                    v___x_951_ = lean_string_utf8_next_fast(v_s_942_, v_a_943_);
                    crate::leanh::lean_dec(v_a_943_);
                    match crate::leanh::lean_obj_tag(v_b_944_) {
                        0 => {
                            v___x_958_ = lean_uint32_dec_eq(v___x_950_, v___x_949_);
                            if v___x_958_ == 0 {
                                v___x_959_ = crate::leanh::lean_box(3);
                                v_a_943_ = v___x_951_;
                                v_b_944_ = v___x_959_;
                                state = 0;
                                continue;
                            } else {
                                v___x_961_ = l_Std_Http_Internal_quoteCore___redArg___closed__0;
                                v___x_962_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_962_, 0, v___x_961_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_962_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_948_,
                                );
                                v_a_943_ = v___x_951_;
                                v_b_944_ = v___x_962_;
                                state = 0;
                                continue;
                            }
                        }
                        1 => {
                            v_escaped_964_ = crate::leanh::lean_ctor_get_uint8(
                                v_b_944_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            v_acc_965_ = crate::leanh::lean_ctor_get(v_b_944_, 0);
                            v_isSharedCheck_1010_ =
                                (!crate::leanh::lean_is_exclusive(v_b_944_)) as u8;
                            if v_isSharedCheck_1010_ == 0 {
                                v___x_967_ = v_b_944_;
                                v_isShared_968_ = v_isSharedCheck_1010_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_acc_965_);
                                crate::leanh::lean_dec(v_b_944_);
                                v___x_967_ = crate::leanh::lean_box(0);
                                v_isShared_968_ = v_isSharedCheck_1010_;
                                state = 3;
                                continue;
                            }
                        }
                        2 => {
                            crate::leanh::lean_dec_ref_known(v_b_944_, 1);
                            v___x_1011_ = crate::leanh::lean_box(3);
                            v_a_943_ = v___x_951_;
                            v_b_944_ = v___x_1011_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v_a_943_ = v___x_951_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_943_);
                    return v_b_944_;
                }
            }
            1 => {
                v___x_953_ = crate::leanh::lean_box(3);
                v_a_943_ = v___x_951_;
                v_b_944_ = v___x_953_;
                state = 0;
                continue;
            }
            2 => {
                v___x_956_ = crate::leanh::lean_box(3);
                v_a_943_ = v___x_951_;
                v_b_944_ = v___x_956_;
                state = 0;
                continue;
            }
            3 => {
                if v_escaped_964_ == 0 {
                    crate::leanh::lean_del_object(v___x_967_);
                    v___x_984_ = 92;
                    v___x_985_ = lean_uint32_dec_eq(v___x_950_, v___x_984_);
                    if v___x_985_ == 0 {
                        v___x_986_ = lean_uint32_dec_eq(v___x_950_, v___x_949_);
                        if v___x_986_ == 0 {
                            v___x_987_ = 9;
                            v___x_988_ = lean_uint32_dec_eq(v___x_950_, v___x_987_);
                            if v___x_988_ == 0 {
                                v___x_989_ = 32;
                                v___x_990_ = lean_uint32_dec_eq(v___x_950_, v___x_989_);
                                if v___x_990_ == 0 {
                                    v___x_991_ = 33;
                                    v___x_992_ = lean_uint32_dec_eq(v___x_950_, v___x_991_);
                                    if v___x_992_ == 0 {
                                        v___x_993_ = 35;
                                        v___x_994_ = lean_uint32_dec_le(v___x_993_, v___x_950_);
                                        if v___x_994_ == 0 {
                                            state = 7;
                                            continue;
                                        } else {
                                            v___x_995_ = 91;
                                            v___x_996_ = lean_uint32_dec_le(v___x_950_, v___x_995_);
                                            if v___x_996_ == 0 {
                                                state = 7;
                                                continue;
                                            } else {
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    state = 6;
                                    continue;
                                }
                            } else {
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_997_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_997_, 0, v_acc_965_);
                            v_a_943_ = v___x_951_;
                            v_b_944_ = v___x_997_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_999_ = lean_uint32_dec_eq(v___x_940_, v___x_949_);
                        v___x_1000_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1000_, 0, v_acc_965_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1000_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_999_,
                        );
                        v_a_943_ = v___x_951_;
                        v_b_944_ = v___x_1000_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1002_ = 9;
                    v___x_1003_ = lean_uint32_dec_eq(v___x_950_, v___x_1002_);
                    if v___x_1003_ == 0 {
                        v___x_1004_ = 32;
                        v___x_1005_ = lean_uint32_dec_eq(v___x_950_, v___x_1004_);
                        if v___x_1005_ == 0 {
                            v___x_1006_ = 33;
                            v___x_1007_ = lean_uint32_dec_le(v___x_1006_, v___x_950_);
                            if v___x_1007_ == 0 {
                                crate::leanh::lean_del_object(v___x_967_);
                                crate::leanh::lean_dec_ref(v_acc_965_);
                                state = 2;
                                continue;
                            } else {
                                v___x_1008_ = 126;
                                v___x_1009_ = lean_uint32_dec_le(v___x_950_, v___x_1008_);
                                if v___x_1009_ == 0 {
                                    crate::leanh::lean_del_object(v___x_967_);
                                    crate::leanh::lean_dec_ref(v_acc_965_);
                                    state = 2;
                                    continue;
                                } else {
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_970_ = lean_string_push(v_acc_965_, v___x_950_);
                if v_isShared_968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_967_, 0, v___x_970_);
                    v___x_972_ = v___x_967_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_974_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_970_);
                    v___x_972_ = v_reuseFailAlloc_974_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_972_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_948_,
                );
                v_a_943_ = v___x_951_;
                v_b_944_ = v___x_972_;
                state = 0;
                continue;
            }
            6 => {
                v___x_976_ = lean_string_push(v_acc_965_, v___x_950_);
                v___x_977_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_977_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_escaped_964_,
                );
                v_a_943_ = v___x_951_;
                v_b_944_ = v___x_977_;
                state = 0;
                continue;
            }
            7 => {
                v___x_980_ = 93;
                v___x_981_ = lean_uint32_dec_le(v___x_980_, v___x_950_);
                if v___x_981_ == 0 {
                    crate::leanh::lean_dec_ref(v_acc_965_);
                    state = 1;
                    continue;
                } else {
                    v___x_982_ = 126;
                    v___x_983_ = lean_uint32_dec_le(v___x_950_, v___x_982_);
                    if v___x_983_ == 0 {
                        crate::leanh::lean_dec_ref(v_acc_965_);
                        state = 1;
                        continue;
                    } else {
                        state = 6;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg___boxed(
    mut v___x_1014_: *mut crate::leanh::LeanObject,
    mut v___x_1015_: *mut crate::leanh::LeanObject,
    mut v_s_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_b_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507__boxed_1019_: u32 = 0;
    let mut v_res_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507__boxed_1019_ = crate::leanh::lean_unbox_uint32(v___x_1014_);
    crate::leanh::lean_dec(v___x_1014_);
    v_res_1020_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_2507__boxed_1019_, v___x_1015_, v_s_1016_, v_a_1017_, v_b_1018_);
    crate::leanh::lean_dec_ref(v_s_1016_);
    crate::leanh::lean_dec_ref(v___x_1015_);
    return v_res_1020_;
}
pub unsafe fn l_Std_Http_Internal_unquoteHttpString_x3f(
    mut v_s_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u32 = 0;
    let mut v___x_1034_: u32 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1030_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1031_ = lean_string_utf8_byte_size(v_s_1021_);
                v___x_1032_ = lean_nat_dec_eq(v___x_1030_, v___x_1031_);
                if v___x_1032_ == 0 {
                    v___x_1033_ = 34;
                    v___x_1034_ = lean_string_utf8_get_fast(v_s_1021_, v___x_1030_);
                    v___x_1035_ = lean_uint32_dec_eq(v___x_1034_, v___x_1033_);
                    if v___x_1035_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_s_1021_);
                        v___x_1036_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1036_, 0, v_s_1021_);
                        crate::leanh::lean_ctor_set(v___x_1036_, 1, v___x_1030_);
                        crate::leanh::lean_ctor_set(v___x_1036_, 2, v___x_1031_);
                        v___x_1037_ = crate::leanh::lean_box(0);
                        v___x_1038_ = l_String_Slice_positions(v___x_1036_);
                        v___x_1039_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_1034_, v___x_1036_, v_s_1021_, v___x_1038_, v___x_1037_);
                        crate::leanh::lean_dec_ref(v_s_1021_);
                        crate::leanh::lean_dec_ref_known(v___x_1036_, 3);
                        if crate::leanh::lean_obj_tag(v___x_1039_) == 2 {
                            v_result_1040_ = crate::leanh::lean_ctor_get(v___x_1039_, 0);
                            v_isSharedCheck_1047_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1039_)) as u8;
                            if v_isSharedCheck_1047_ == 0 {
                                v___x_1042_ = v___x_1039_;
                                v_isShared_1043_ = v_isSharedCheck_1047_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_result_1040_);
                                crate::leanh::lean_dec(v___x_1039_);
                                v___x_1042_ = crate::leanh::lean_box(0);
                                v_isShared_1043_ = v_isSharedCheck_1047_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1039_);
                            v___x_1048_ = crate::leanh::lean_box(0);
                            return v___x_1048_;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1023_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1024_ = lean_string_utf8_byte_size(v_s_1021_);
                crate::leanh::lean_inc_ref(v_s_1021_);
                v___x_1025_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1025_, 0, v_s_1021_);
                crate::leanh::lean_ctor_set(v___x_1025_, 1, v___x_1023_);
                crate::leanh::lean_ctor_set(v___x_1025_, 2, v___x_1024_);
                v___x_1026_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__0(v___x_1025_, v___x_1023_);
                crate::leanh::lean_dec_ref_known(v___x_1025_, 3);
                v___x_1027_ = lean_nat_dec_eq(v___x_1026_, v___x_1024_);
                crate::leanh::lean_dec(v___x_1026_);
                if v___x_1027_ == 0 {
                    crate::leanh::lean_dec_ref(v_s_1021_);
                    v___x_1028_ = crate::leanh::lean_box(0);
                    return v___x_1028_;
                } else {
                    v___x_1029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1029_, 0, v_s_1021_);
                    return v___x_1029_;
                }
            }
            2 => {
                if v_isShared_1043_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1042_, 1);
                    v___x_1045_ = v___x_1042_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_result_1040_);
                    v___x_1045_ = v_reuseFailAlloc_1046_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(
    mut v___x_1049_: u32,
    mut v___x_1050_: *mut crate::leanh::LeanObject,
    mut v_s_1051_: *mut crate::leanh::LeanObject,
    mut v_inst_1052_: *mut crate::leanh::LeanObject,
    mut v_R_1053_: *mut crate::leanh::LeanObject,
    mut v_a_1054_: *mut crate::leanh::LeanObject,
    mut v_b_1055_: *mut crate::leanh::LeanObject,
    mut v_c_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___redArg(v___x_1049_, v___x_1050_, v_s_1051_, v_a_1054_, v_b_1055_);
    return v___x_1057_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1___boxed(
    mut v___x_1058_: *mut crate::leanh::LeanObject,
    mut v___x_1059_: *mut crate::leanh::LeanObject,
    mut v_s_1060_: *mut crate::leanh::LeanObject,
    mut v_inst_1061_: *mut crate::leanh::LeanObject,
    mut v_R_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_b_1064_: *mut crate::leanh::LeanObject,
    mut v_c_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702__boxed_1066_: u32 = 0;
    let mut v_res_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702__boxed_1066_ = crate::leanh::lean_unbox_uint32(v___x_1058_);
    crate::leanh::lean_dec(v___x_1058_);
    v_res_1067_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Http_Internal_unquoteHttpString_x3f_spec__1(
            v___x_2702__boxed_1066_,
            v___x_1059_,
            v_s_1060_,
            v_inst_1061_,
            v_R_1062_,
            v_a_1063_,
            v_b_1064_,
            v_c_1065_,
        );
    crate::leanh::lean_dec_ref(v_s_1060_);
    crate::leanh::lean_dec_ref(v___x_1059_);
    return v_res_1067_;
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_isToken_spec__0(
    mut v_x_1068_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1069_: u8 = 0;
    let mut v_head_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1073_: u8 = 0;
    let mut v___x_1076_: u32 = 0;
    let mut v___x_1077_: u32 = 0;
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: u32 = 0;
    let mut v___x_1080_: u32 = 0;
    let mut v___x_1081_: u8 = 0;
    let mut v___y_1083_: u8 = 0;
    let mut v___x_1084_: u32 = 0;
    let mut v___x_1085_: u32 = 0;
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u32 = 0;
    let mut v___x_1088_: u32 = 0;
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1092_: u32 = 0;
    let mut v___x_1093_: u32 = 0;
    let mut v___x_1094_: u8 = 0;
    let mut v___x_1095_: u32 = 0;
    let mut v___x_1096_: u32 = 0;
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: u32 = 0;
    let mut v___x_1099_: u32 = 0;
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: u32 = 0;
    let mut v___x_1102_: u32 = 0;
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: u32 = 0;
    let mut v___x_1105_: u32 = 0;
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: u32 = 0;
    let mut v___x_1108_: u32 = 0;
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: u32 = 0;
    let mut v___x_1111_: u32 = 0;
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1113_: u32 = 0;
    let mut v___x_1114_: u32 = 0;
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: u32 = 0;
    let mut v___x_1117_: u32 = 0;
    let mut v___x_1118_: u8 = 0;
    let mut v___x_1119_: u32 = 0;
    let mut v___x_1120_: u32 = 0;
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: u32 = 0;
    let mut v___x_1123_: u32 = 0;
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: u32 = 0;
    let mut v___x_1126_: u32 = 0;
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: u32 = 0;
    let mut v___x_1129_: u32 = 0;
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: u32 = 0;
    let mut v___x_1132_: u32 = 0;
    let mut v___x_1133_: u8 = 0;
    let mut v___x_1134_: u32 = 0;
    let mut v___x_1135_: u32 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: u32 = 0;
    let mut v___x_1138_: u32 = 0;
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: u32 = 0;
    let mut v___x_1141_: u32 = 0;
    let mut v___x_1142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1068_) == 0 {
                    v___x_1069_ = 1;
                    return v___x_1069_;
                } else {
                    v_head_1070_ = crate::leanh::lean_ctor_get(v_x_1068_, 0);
                    v_tail_1071_ = crate::leanh::lean_ctor_get(v_x_1068_, 1);
                    v___x_1092_ = 33;
                    v___x_1093_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                    v___x_1094_ = lean_uint32_dec_eq(v___x_1093_, v___x_1092_);
                    if v___x_1094_ == 0 {
                        v___x_1095_ = 35;
                        v___x_1096_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                        v___x_1097_ = lean_uint32_dec_eq(v___x_1096_, v___x_1095_);
                        if v___x_1097_ == 0 {
                            v___x_1098_ = 36;
                            v___x_1099_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                            v___x_1100_ = lean_uint32_dec_eq(v___x_1099_, v___x_1098_);
                            if v___x_1100_ == 0 {
                                v___x_1101_ = 37;
                                v___x_1102_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                v___x_1103_ = lean_uint32_dec_eq(v___x_1102_, v___x_1101_);
                                if v___x_1103_ == 0 {
                                    v___x_1104_ = 38;
                                    v___x_1105_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                    v___x_1106_ = lean_uint32_dec_eq(v___x_1105_, v___x_1104_);
                                    if v___x_1106_ == 0 {
                                        v___x_1107_ = 39;
                                        v___x_1108_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                        v___x_1109_ = lean_uint32_dec_eq(v___x_1108_, v___x_1107_);
                                        if v___x_1109_ == 0 {
                                            v___x_1110_ = 42;
                                            v___x_1111_ =
                                                crate::leanh::lean_unbox_uint32(v_head_1070_);
                                            v___x_1112_ =
                                                lean_uint32_dec_eq(v___x_1111_, v___x_1110_);
                                            if v___x_1112_ == 0 {
                                                v___x_1113_ = 43;
                                                v___x_1114_ =
                                                    crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                v___x_1115_ =
                                                    lean_uint32_dec_eq(v___x_1114_, v___x_1113_);
                                                if v___x_1115_ == 0 {
                                                    v___x_1116_ = 45;
                                                    v___x_1117_ = crate::leanh::lean_unbox_uint32(
                                                        v_head_1070_,
                                                    );
                                                    v___x_1118_ = lean_uint32_dec_eq(
                                                        v___x_1117_,
                                                        v___x_1116_,
                                                    );
                                                    if v___x_1118_ == 0 {
                                                        v___x_1119_ = 46;
                                                        v___x_1120_ =
                                                            crate::leanh::lean_unbox_uint32(
                                                                v_head_1070_,
                                                            );
                                                        v___x_1121_ = lean_uint32_dec_eq(
                                                            v___x_1120_,
                                                            v___x_1119_,
                                                        );
                                                        if v___x_1121_ == 0 {
                                                            v___x_1122_ = 94;
                                                            v___x_1123_ =
                                                                crate::leanh::lean_unbox_uint32(
                                                                    v_head_1070_,
                                                                );
                                                            v___x_1124_ = lean_uint32_dec_eq(
                                                                v___x_1123_,
                                                                v___x_1122_,
                                                            );
                                                            if v___x_1124_ == 0 {
                                                                v___x_1125_ = 95;
                                                                v___x_1126_ =
                                                                    crate::leanh::lean_unbox_uint32(
                                                                        v_head_1070_,
                                                                    );
                                                                v___x_1127_ = lean_uint32_dec_eq(
                                                                    v___x_1126_,
                                                                    v___x_1125_,
                                                                );
                                                                if v___x_1127_ == 0 {
                                                                    v___x_1128_ = 96;
                                                                    v___x_1129_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                                    v___x_1130_ =
                                                                        lean_uint32_dec_eq(
                                                                            v___x_1129_,
                                                                            v___x_1128_,
                                                                        );
                                                                    if v___x_1130_ == 0 {
                                                                        v___x_1131_ = 124;
                                                                        v___x_1132_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                                        v___x_1133_ =
                                                                            lean_uint32_dec_eq(
                                                                                v___x_1132_,
                                                                                v___x_1131_,
                                                                            );
                                                                        if v___x_1133_ == 0 {
                                                                            v___x_1134_ = 126;
                                                                            v___x_1135_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                                            v___x_1136_ =
                                                                                lean_uint32_dec_eq(
                                                                                    v___x_1135_,
                                                                                    v___x_1134_,
                                                                                );
                                                                            if v___x_1136_ == 0 {
                                                                                v___x_1137_ = 48;
                                                                                v___x_1138_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                                                v___x_1139_ = lean_uint32_dec_le(v___x_1137_, v___x_1138_);
                                                                                if v___x_1139_ == 0
                                                                                {
                                                                                    v___y_1083_ =
                                                                                        v___x_1139_;
                                                                                    state = 3;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_1140_ =
                                                                                        57;
                                                                                    v___x_1141_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                                                                                    v___x_1142_ = lean_uint32_dec_le(v___x_1141_, v___x_1140_);
                                                                                    v___y_1083_ =
                                                                                        v___x_1142_;
                                                                                    state = 3;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                v_x_1068_ =
                                                                                    v_tail_1071_;
                                                                                state = 0;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            v_x_1068_ =
                                                                                v_tail_1071_;
                                                                            state = 0;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_x_1068_ = v_tail_1071_;
                                                                        state = 0;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    v_x_1068_ = v_tail_1071_;
                                                                    state = 0;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_x_1068_ = v_tail_1071_;
                                                                state = 0;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_x_1068_ = v_tail_1071_;
                                                            state = 0;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_x_1068_ = v_tail_1071_;
                                                        state = 0;
                                                        continue;
                                                    }
                                                } else {
                                                    v_x_1068_ = v_tail_1071_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                v_x_1068_ = v_tail_1071_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            v_x_1068_ = v_tail_1071_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        v_x_1068_ = v_tail_1071_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    v_x_1068_ = v_tail_1071_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v_x_1068_ = v_tail_1071_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_1068_ = v_tail_1071_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_1068_ = v_tail_1071_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1073_ == 0 {
                    return v___y_1073_;
                } else {
                    v_x_1068_ = v_tail_1071_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1076_ = 97;
                v___x_1077_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                v___x_1078_ = lean_uint32_dec_le(v___x_1076_, v___x_1077_);
                if v___x_1078_ == 0 {
                    v___y_1073_ = v___x_1078_;
                    state = 1;
                    continue;
                } else {
                    v___x_1079_ = 122;
                    v___x_1080_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                    v___x_1081_ = lean_uint32_dec_le(v___x_1080_, v___x_1079_);
                    v___y_1073_ = v___x_1081_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1083_ == 0 {
                    v___x_1084_ = 65;
                    v___x_1085_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                    v___x_1086_ = lean_uint32_dec_le(v___x_1084_, v___x_1085_);
                    if v___x_1086_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1087_ = 90;
                        v___x_1088_ = crate::leanh::lean_unbox_uint32(v_head_1070_);
                        v___x_1089_ = lean_uint32_dec_le(v___x_1088_, v___x_1087_);
                        if v___x_1089_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_x_1068_ = v_tail_1071_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v_x_1068_ = v_tail_1071_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_Internal_isToken_spec__0___boxed(
    mut v_x_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1159_: u8 = 0;
    let mut v_r_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_x_1158_);
    crate::leanh::lean_dec(v_x_1158_);
    v_r_1160_ = crate::leanh::lean_box((v_res_1159_) as usize);
    return v_r_1160_;
}
pub unsafe fn l_Std_Http_Internal_isToken(mut v_s_1161_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_s_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    v_s_1162_ = lean_string_data(v_s_1161_);
    v___x_1163_ = l_List_isEmpty___redArg(v_s_1162_);
    if v___x_1163_ == 0 {
        let mut v___x_1164_: u8 = 0;
        v___x_1164_ = l_List_all___at___00Std_Http_Internal_isToken_spec__0(v_s_1162_);
        crate::leanh::lean_dec(v_s_1162_);
        return v___x_1164_;
    } else {
        let mut v___x_1165_: u8 = 0;
        crate::leanh::lean_dec(v_s_1162_);
        v___x_1165_ = 0;
        return v___x_1165_;
    }
}
pub unsafe fn l_Std_Http_Internal_isToken___boxed(
    mut v_s_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1167_: u8 = 0;
    let mut v_r_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1167_ = l_Std_Http_Internal_isToken(v_s_1166_);
    v_r_1168_ = crate::leanh::lean_box((v_res_1167_) as usize);
    return v_r_1168_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_String(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_String(
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
pub unsafe fn initialize_Std_Http_Internal_String(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_String(builtin);
}
