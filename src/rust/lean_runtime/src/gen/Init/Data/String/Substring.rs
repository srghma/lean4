// Lean compiler output
// Module: Init.Data.String.Substring
// Imports: Init.Data.String.Slice Init.Data.Option.BasicAux
use crate::r#gen::Init::Data::Char::Basic::l_Char_isWhitespace___boxed;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Pos_Raw_substrEq;
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Iterate::{
    l_String_Slice_positions, l_String_Slice_revPositions,
};
use crate::r#gen::Init::Data::String::Pattern::Basic::{
    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2,
    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed,
};
use crate::r#gen::Init::Data::String::Pattern::Pred::l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool;
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, l_String_Slice_Pos_skipWhile___redArg,
    l_String_Slice_contains___redArg, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_is_valid_pos, lean_string_utf8_at_end, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_next,
    lean_string_utf8_next_fast, lean_string_utf8_prev,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_nat,
};
pub static l_Substring_Raw_extract___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Substring_Raw_extract___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_extract___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Substring_Raw_extract___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Substring_Raw_extract___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Substring_Raw_extract___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_extract___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Substring_Raw_foldl___redArg___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Substring_Raw_foldl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Substring_Raw_foldl___redArg___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Substring_Raw_foldl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Substring_Raw_foldl___redArg___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Substring_Raw_foldl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Substring_Raw_foldl___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Substring_Raw_foldl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Substring_Raw_trimLeft___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Substring_Raw_trimLeft___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_trimLeft___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Substring_Raw_hasBeq___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Substring_Raw_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Substring_Raw_hasBeq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_hasBeq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Substring_Raw_hasBeq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Substring_Raw_hasBeq___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Substring_Raw_ofSlice(
    mut v_s_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1590_ = crate::leanh::lean_ctor_get(v_s_1589_, 0);
                v_startInclusive_1591_ = crate::leanh::lean_ctor_get(v_s_1589_, 1);
                v_endExclusive_1592_ = crate::leanh::lean_ctor_get(v_s_1589_, 2);
                v_isSharedCheck_1599_ = (!crate::leanh::lean_is_exclusive(v_s_1589_)) as u8;
                if v_isSharedCheck_1599_ == 0 {
                    v___x_1594_ = v_s_1589_;
                    v_isShared_1595_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_1592_);
                    crate::leanh::lean_inc(v_startInclusive_1591_);
                    crate::leanh::lean_inc(v_str_1590_);
                    crate::leanh::lean_dec(v_s_1589_);
                    v___x_1594_ = crate::leanh::lean_box(0);
                    v_isShared_1595_ = v_isSharedCheck_1599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1595_ == 0 {
                    v___x_1597_ = v___x_1594_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1598_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_str_1590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_startInclusive_1591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_endExclusive_1592_);
                    v___x_1597_ = v_reuseFailAlloc_1598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_toSlice_x3f(
    mut v_s_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1606_: u8 = 0;
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1601_ = crate::leanh::lean_ctor_get(v_s_1600_, 0);
                v_startPos_1602_ = crate::leanh::lean_ctor_get(v_s_1600_, 1);
                v_stopPos_1603_ = crate::leanh::lean_ctor_get(v_s_1600_, 2);
                v_isSharedCheck_1617_ = (!crate::leanh::lean_is_exclusive(v_s_1600_)) as u8;
                if v_isSharedCheck_1617_ == 0 {
                    v___x_1605_ = v_s_1600_;
                    v_isShared_1606_ = v_isSharedCheck_1617_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_1603_);
                    crate::leanh::lean_inc(v_startPos_1602_);
                    crate::leanh::lean_inc(v_str_1601_);
                    crate::leanh::lean_dec(v_s_1600_);
                    v___x_1605_ = crate::leanh::lean_box(0);
                    v_isShared_1606_ = v_isSharedCheck_1617_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1607_ = lean_string_is_valid_pos(v_str_1601_, v_startPos_1602_);
                if v___x_1607_ == 0 {
                    crate::leanh::lean_del_object(v___x_1605_);
                    crate::leanh::lean_dec(v_stopPos_1603_);
                    crate::leanh::lean_dec(v_startPos_1602_);
                    crate::leanh::lean_dec_ref(v_str_1601_);
                    v___x_1608_ = crate::leanh::lean_box(0);
                    return v___x_1608_;
                } else {
                    v___x_1609_ = lean_string_is_valid_pos(v_str_1601_, v_stopPos_1603_);
                    if v___x_1609_ == 0 {
                        crate::leanh::lean_del_object(v___x_1605_);
                        crate::leanh::lean_dec(v_stopPos_1603_);
                        crate::leanh::lean_dec(v_startPos_1602_);
                        crate::leanh::lean_dec_ref(v_str_1601_);
                        v___x_1610_ = crate::leanh::lean_box(0);
                        return v___x_1610_;
                    } else {
                        v___x_1611_ = lean_nat_dec_le(v_startPos_1602_, v_stopPos_1603_);
                        if v___x_1611_ == 0 {
                            crate::leanh::lean_del_object(v___x_1605_);
                            crate::leanh::lean_dec(v_stopPos_1603_);
                            crate::leanh::lean_dec(v_startPos_1602_);
                            crate::leanh::lean_dec_ref(v_str_1601_);
                            v___x_1612_ = crate::leanh::lean_box(0);
                            return v___x_1612_;
                        } else {
                            if v_isShared_1606_ == 0 {
                                v___x_1614_ = v___x_1605_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_1616_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_str_1601_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1616_,
                                    1,
                                    v_startPos_1602_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1616_,
                                    2,
                                    v_stopPos_1603_,
                                );
                                v___x_1614_ = v_reuseFailAlloc_1616_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1615_, 0, v___x_1614_);
                return v___x_1615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_isEmpty(mut v_ss_1618_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_startPos_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    v_startPos_1619_ = crate::leanh::lean_ctor_get(v_ss_1618_, 1);
    v_stopPos_1620_ = crate::leanh::lean_ctor_get(v_ss_1618_, 2);
    v___x_1621_ = lean_nat_sub(v_stopPos_1620_, v_startPos_1619_);
    v___x_1622_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1623_ = lean_nat_dec_eq(v___x_1621_, v___x_1622_);
    crate::leanh::lean_dec(v___x_1621_);
    return v___x_1623_;
}
pub unsafe fn l_Substring_Raw_isEmpty___boxed(
    mut v_ss_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: u8 = 0;
    let mut v_r_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Substring_Raw_isEmpty(v_ss_1624_);
    crate::leanh::lean_dec_ref(v_ss_1624_);
    v_r_1626_ = crate::leanh::lean_box((v_res_1625_) as usize);
    return v_r_1626_;
}
pub unsafe fn lean_substring_isempty(mut v_ss_1627_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_startPos_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    v_startPos_1628_ = crate::leanh::lean_ctor_get(v_ss_1627_, 1);
    crate::leanh::lean_inc(v_startPos_1628_);
    v_stopPos_1629_ = crate::leanh::lean_ctor_get(v_ss_1627_, 2);
    crate::leanh::lean_inc(v_stopPos_1629_);
    crate::leanh::lean_dec_ref(v_ss_1627_);
    v___x_1630_ = lean_nat_sub(v_stopPos_1629_, v_startPos_1628_);
    crate::leanh::lean_dec(v_startPos_1628_);
    crate::leanh::lean_dec(v_stopPos_1629_);
    v___x_1631_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1632_ = lean_nat_dec_eq(v___x_1630_, v___x_1631_);
    crate::leanh::lean_dec(v___x_1630_);
    return v___x_1632_;
}
pub unsafe fn l_Substring_Raw_Internal_isEmptyImpl___boxed(
    mut v_ss_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1634_: u8 = 0;
    let mut v_r_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = lean_substring_isempty(v_ss_1633_);
    v_r_1635_ = crate::leanh::lean_box((v_res_1634_) as usize);
    return v_r_1635_;
}
pub unsafe fn l_Substring_Raw_toString(
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1637_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
    v_startPos_1638_ = crate::leanh::lean_ctor_get(v_x_1636_, 1);
    v_stopPos_1639_ = crate::leanh::lean_ctor_get(v_x_1636_, 2);
    v___x_1640_ = lean_string_utf8_extract(v_str_1637_, v_startPos_1638_, v_stopPos_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Substring_Raw_toString___boxed(
    mut v_x_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Substring_Raw_toString(v_x_1641_);
    crate::leanh::lean_dec_ref(v_x_1641_);
    return v_res_1642_;
}
pub unsafe fn lean_substring_tostring(
    mut v_a_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1644_ = crate::leanh::lean_ctor_get(v_a_1643_, 0);
    crate::leanh::lean_inc_ref(v_str_1644_);
    v_startPos_1645_ = crate::leanh::lean_ctor_get(v_a_1643_, 1);
    crate::leanh::lean_inc(v_startPos_1645_);
    v_stopPos_1646_ = crate::leanh::lean_ctor_get(v_a_1643_, 2);
    crate::leanh::lean_inc(v_stopPos_1646_);
    crate::leanh::lean_dec_ref(v_a_1643_);
    v___x_1647_ = lean_string_utf8_extract(v_str_1644_, v_startPos_1645_, v_stopPos_1646_);
    crate::leanh::lean_dec(v_stopPos_1646_);
    crate::leanh::lean_dec(v_startPos_1645_);
    crate::leanh::lean_dec_ref(v_str_1644_);
    return v___x_1647_;
}
pub unsafe fn l_Substring_Raw_get(
    mut v_x_1648_: *mut crate::leanh::LeanObject,
    mut v_x_1649_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_str_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: u32 = 0;
    v_str_1650_ = crate::leanh::lean_ctor_get(v_x_1648_, 0);
    v_startPos_1651_ = crate::leanh::lean_ctor_get(v_x_1648_, 1);
    v___x_1652_ = lean_nat_add(v_startPos_1651_, v_x_1649_);
    v___x_1653_ = lean_string_utf8_get(v_str_1650_, v___x_1652_);
    crate::leanh::lean_dec(v___x_1652_);
    return v___x_1653_;
}
pub unsafe fn l_Substring_Raw_get___boxed(
    mut v_x_1654_: *mut crate::leanh::LeanObject,
    mut v_x_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1656_: u32 = 0;
    let mut v_r_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1656_ = l_Substring_Raw_get(v_x_1654_, v_x_1655_);
    crate::leanh::lean_dec(v_x_1655_);
    crate::leanh::lean_dec_ref(v_x_1654_);
    v_r_1657_ = crate::leanh::lean_box_uint32(v_res_1656_);
    return v_r_1657_;
}
pub unsafe fn lean_substring_get(
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_str_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u32 = 0;
    v_str_1660_ = crate::leanh::lean_ctor_get(v_a_1658_, 0);
    crate::leanh::lean_inc_ref(v_str_1660_);
    v_startPos_1661_ = crate::leanh::lean_ctor_get(v_a_1658_, 1);
    crate::leanh::lean_inc(v_startPos_1661_);
    crate::leanh::lean_dec_ref(v_a_1658_);
    v___x_1662_ = lean_nat_add(v_startPos_1661_, v_a_1659_);
    crate::leanh::lean_dec(v_a_1659_);
    crate::leanh::lean_dec(v_startPos_1661_);
    v___x_1663_ = lean_string_utf8_get(v_str_1660_, v___x_1662_);
    crate::leanh::lean_dec(v___x_1662_);
    crate::leanh::lean_dec_ref(v_str_1660_);
    return v___x_1663_;
}
pub unsafe fn l_Substring_Raw_Internal_getImpl___boxed(
    mut v_a_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: u32 = 0;
    let mut v_r_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = lean_substring_get(v_a_1664_, v_a_1665_);
    v_r_1667_ = crate::leanh::lean_box_uint32(v_res_1666_);
    return v_r_1667_;
}
pub unsafe fn l_Substring_Raw_next(
    mut v_x_1668_: *mut crate::leanh::LeanObject,
    mut v_x_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    v_str_1670_ = crate::leanh::lean_ctor_get(v_x_1668_, 0);
    v_startPos_1671_ = crate::leanh::lean_ctor_get(v_x_1668_, 1);
    v_stopPos_1672_ = crate::leanh::lean_ctor_get(v_x_1668_, 2);
    v_absP_1673_ = lean_nat_add(v_startPos_1671_, v_x_1669_);
    v___x_1674_ = lean_nat_dec_eq(v_absP_1673_, v_stopPos_1672_);
    if v___x_1674_ == 0 {
        let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1675_ = lean_string_utf8_next(v_str_1670_, v_absP_1673_);
        crate::leanh::lean_dec(v_absP_1673_);
        v___x_1676_ = lean_nat_sub(v___x_1675_, v_startPos_1671_);
        crate::leanh::lean_dec(v___x_1675_);
        return v___x_1676_;
    } else {
        crate::leanh::lean_dec(v_absP_1673_);
        crate::leanh::lean_inc(v_x_1669_);
        return v_x_1669_;
    }
}
pub unsafe fn l_Substring_Raw_next___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
    mut v_x_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Substring_Raw_next(v_x_1677_, v_x_1678_);
    crate::leanh::lean_dec(v_x_1678_);
    crate::leanh::lean_dec_ref(v_x_1677_);
    return v_res_1679_;
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(
    mut v_x_1680_: *mut crate::leanh::LeanObject,
    mut v_x_1681_: *mut crate::leanh::LeanObject,
    mut v_h__1_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1683_ = crate::leanh::lean_ctor_get(v_x_1680_, 0);
    crate::leanh::lean_inc_ref(v_str_1683_);
    v_startPos_1684_ = crate::leanh::lean_ctor_get(v_x_1680_, 1);
    crate::leanh::lean_inc(v_startPos_1684_);
    v_stopPos_1685_ = crate::leanh::lean_ctor_get(v_x_1680_, 2);
    crate::leanh::lean_inc(v_stopPos_1685_);
    crate::leanh::lean_dec_ref(v_x_1680_);
    v___x_1686_ = crate::leanh::lean_apply_4(
        v_h__1_1682_,
        v_str_1683_,
        v_startPos_1684_,
        v_stopPos_1685_,
        v_x_1681_,
    );
    return v___x_1686_;
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(
    mut v_motive_1687_: *mut crate::leanh::LeanObject,
    mut v_x_1688_: *mut crate::leanh::LeanObject,
    mut v_x_1689_: *mut crate::leanh::LeanObject,
    mut v_h__1_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1691_ = crate::leanh::lean_ctor_get(v_x_1688_, 0);
    crate::leanh::lean_inc_ref(v_str_1691_);
    v_startPos_1692_ = crate::leanh::lean_ctor_get(v_x_1688_, 1);
    crate::leanh::lean_inc(v_startPos_1692_);
    v_stopPos_1693_ = crate::leanh::lean_ctor_get(v_x_1688_, 2);
    crate::leanh::lean_inc(v_stopPos_1693_);
    crate::leanh::lean_dec_ref(v_x_1688_);
    v___x_1694_ = crate::leanh::lean_apply_4(
        v_h__1_1690_,
        v_str_1691_,
        v_startPos_1692_,
        v_stopPos_1693_,
        v_x_1689_,
    );
    return v___x_1694_;
}
pub unsafe fn l_Substring_Raw_prev(
    mut v_x_1695_: *mut crate::leanh::LeanObject,
    mut v_x_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    v_str_1697_ = crate::leanh::lean_ctor_get(v_x_1695_, 0);
    v_startPos_1698_ = crate::leanh::lean_ctor_get(v_x_1695_, 1);
    v_absP_1699_ = lean_nat_add(v_startPos_1698_, v_x_1696_);
    v___x_1700_ = lean_nat_dec_eq(v_absP_1699_, v_startPos_1698_);
    if v___x_1700_ == 0 {
        let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1701_ = lean_string_utf8_prev(v_str_1697_, v_absP_1699_);
        crate::leanh::lean_dec(v_absP_1699_);
        v___x_1702_ = lean_nat_sub(v___x_1701_, v_startPos_1698_);
        crate::leanh::lean_dec(v___x_1701_);
        return v___x_1702_;
    } else {
        crate::leanh::lean_dec(v_absP_1699_);
        crate::leanh::lean_inc(v_x_1696_);
        return v_x_1696_;
    }
}
pub unsafe fn l_Substring_Raw_prev___boxed(
    mut v_x_1703_: *mut crate::leanh::LeanObject,
    mut v_x_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1705_ = l_Substring_Raw_prev(v_x_1703_, v_x_1704_);
    crate::leanh::lean_dec(v_x_1704_);
    crate::leanh::lean_dec_ref(v_x_1703_);
    return v_res_1705_;
}
pub unsafe fn lean_substring_prev(
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    v_str_1708_ = crate::leanh::lean_ctor_get(v_a_1706_, 0);
    crate::leanh::lean_inc_ref(v_str_1708_);
    v_startPos_1709_ = crate::leanh::lean_ctor_get(v_a_1706_, 1);
    crate::leanh::lean_inc(v_startPos_1709_);
    crate::leanh::lean_dec_ref(v_a_1706_);
    v_absP_1710_ = lean_nat_add(v_startPos_1709_, v_a_1707_);
    v___x_1711_ = lean_nat_dec_eq(v_absP_1710_, v_startPos_1709_);
    if v___x_1711_ == 0 {
        let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1707_);
        v___x_1712_ = lean_string_utf8_prev(v_str_1708_, v_absP_1710_);
        crate::leanh::lean_dec(v_absP_1710_);
        crate::leanh::lean_dec_ref(v_str_1708_);
        v___x_1713_ = lean_nat_sub(v___x_1712_, v_startPos_1709_);
        crate::leanh::lean_dec(v_startPos_1709_);
        crate::leanh::lean_dec(v___x_1712_);
        return v___x_1713_;
    } else {
        crate::leanh::lean_dec(v_absP_1710_);
        crate::leanh::lean_dec(v_startPos_1709_);
        crate::leanh::lean_dec_ref(v_str_1708_);
        return v_a_1707_;
    }
}
pub unsafe fn l_Substring_Raw_nextn(
    mut v_x_1714_: *mut crate::leanh::LeanObject,
    mut v_x_1715_: *mut crate::leanh::LeanObject,
    mut v_x_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1718_: u8 = 0;
    let mut v_str_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1717_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1718_ = lean_nat_dec_eq(v_x_1715_, v_zero_1717_);
                if v_isZero_1718_ == 1 {
                    crate::leanh::lean_dec(v_x_1715_);
                    return v_x_1716_;
                } else {
                    v_str_1719_ = crate::leanh::lean_ctor_get(v_x_1714_, 0);
                    v_startPos_1720_ = crate::leanh::lean_ctor_get(v_x_1714_, 1);
                    v_stopPos_1721_ = crate::leanh::lean_ctor_get(v_x_1714_, 2);
                    v_one_1722_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1723_ = lean_nat_sub(v_x_1715_, v_one_1722_);
                    crate::leanh::lean_dec(v_x_1715_);
                    v_absP_1724_ = lean_nat_add(v_startPos_1720_, v_x_1716_);
                    v___x_1725_ = lean_nat_dec_eq(v_absP_1724_, v_stopPos_1721_);
                    if v___x_1725_ == 0 {
                        crate::leanh::lean_dec(v_x_1716_);
                        v___x_1726_ = lean_string_utf8_next(v_str_1719_, v_absP_1724_);
                        crate::leanh::lean_dec(v_absP_1724_);
                        v___x_1727_ = lean_nat_sub(v___x_1726_, v_startPos_1720_);
                        crate::leanh::lean_dec(v___x_1726_);
                        v_x_1715_ = v_n_1723_;
                        v_x_1716_ = v___x_1727_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_absP_1724_);
                        v_x_1715_ = v_n_1723_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_nextn___boxed(
    mut v_x_1730_: *mut crate::leanh::LeanObject,
    mut v_x_1731_: *mut crate::leanh::LeanObject,
    mut v_x_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Substring_Raw_nextn(v_x_1730_, v_x_1731_, v_x_1732_);
    crate::leanh::lean_dec_ref(v_x_1730_);
    return v_res_1733_;
}
pub unsafe fn l_Substring_Raw_prevn(
    mut v_x_1734_: *mut crate::leanh::LeanObject,
    mut v_x_1735_: *mut crate::leanh::LeanObject,
    mut v_x_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1738_: u8 = 0;
    let mut v_str_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1737_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1738_ = lean_nat_dec_eq(v_x_1735_, v_zero_1737_);
                if v_isZero_1738_ == 1 {
                    crate::leanh::lean_dec(v_x_1735_);
                    return v_x_1736_;
                } else {
                    v_str_1739_ = crate::leanh::lean_ctor_get(v_x_1734_, 0);
                    v_startPos_1740_ = crate::leanh::lean_ctor_get(v_x_1734_, 1);
                    v_one_1741_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1742_ = lean_nat_sub(v_x_1735_, v_one_1741_);
                    crate::leanh::lean_dec(v_x_1735_);
                    v_absP_1743_ = lean_nat_add(v_startPos_1740_, v_x_1736_);
                    v___x_1744_ = lean_nat_dec_eq(v_absP_1743_, v_startPos_1740_);
                    if v___x_1744_ == 0 {
                        crate::leanh::lean_dec(v_x_1736_);
                        v___x_1745_ = lean_string_utf8_prev(v_str_1739_, v_absP_1743_);
                        crate::leanh::lean_dec(v_absP_1743_);
                        v___x_1746_ = lean_nat_sub(v___x_1745_, v_startPos_1740_);
                        crate::leanh::lean_dec(v___x_1745_);
                        v_x_1735_ = v_n_1742_;
                        v_x_1736_ = v___x_1746_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_absP_1743_);
                        v_x_1735_ = v_n_1742_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_prevn___boxed(
    mut v_x_1749_: *mut crate::leanh::LeanObject,
    mut v_x_1750_: *mut crate::leanh::LeanObject,
    mut v_x_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Substring_Raw_prevn(v_x_1749_, v_x_1750_, v_x_1751_);
    crate::leanh::lean_dec_ref(v_x_1749_);
    return v_res_1752_;
}
pub unsafe fn l_Substring_Raw_front(mut v_s_1753_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_str_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: u32 = 0;
    v_str_1754_ = crate::leanh::lean_ctor_get(v_s_1753_, 0);
    v_startPos_1755_ = crate::leanh::lean_ctor_get(v_s_1753_, 1);
    v___x_1756_ = lean_string_utf8_get(v_str_1754_, v_startPos_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Substring_Raw_front___boxed(
    mut v_s_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1758_: u32 = 0;
    let mut v_r_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l_Substring_Raw_front(v_s_1757_);
    crate::leanh::lean_dec_ref(v_s_1757_);
    v_r_1759_ = crate::leanh::lean_box_uint32(v_res_1758_);
    return v_r_1759_;
}
pub unsafe fn lean_substring_front(mut v_s_1760_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_str_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u32 = 0;
    v_str_1761_ = crate::leanh::lean_ctor_get(v_s_1760_, 0);
    crate::leanh::lean_inc_ref(v_str_1761_);
    v_startPos_1762_ = crate::leanh::lean_ctor_get(v_s_1760_, 1);
    crate::leanh::lean_inc(v_startPos_1762_);
    crate::leanh::lean_dec_ref(v_s_1760_);
    v___x_1763_ = lean_string_utf8_get(v_str_1761_, v_startPos_1762_);
    crate::leanh::lean_dec(v_startPos_1762_);
    crate::leanh::lean_dec_ref(v_str_1761_);
    return v___x_1763_;
}
pub unsafe fn l_Substring_Raw_Internal_frontImpl___boxed(
    mut v_s_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1765_: u32 = 0;
    let mut v_r_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1765_ = lean_substring_front(v_s_1764_);
    v_r_1766_ = crate::leanh::lean_box_uint32(v_res_1765_);
    return v_r_1766_;
}
pub unsafe fn l_Substring_Raw_posOf___lam__0(
    mut v_stopPos_1767_: *mut crate::leanh::LeanObject,
    mut v_startPos_1768_: *mut crate::leanh::LeanObject,
    mut v_str_1769_: *mut crate::leanh::LeanObject,
    mut v_c_1770_: u32,
    mut v___x_1771_: *mut crate::leanh::LeanObject,
    mut v_it_1772_: *mut crate::leanh::LeanObject,
    mut v_acc_1773_: *mut crate::leanh::LeanObject,
    mut v_hP_1774_: *mut crate::leanh::LeanObject,
    mut v_recur_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    v___x_1776_ = lean_nat_sub(v_stopPos_1767_, v_startPos_1768_);
    v___x_1777_ = lean_nat_dec_eq(v_it_1772_, v___x_1776_);
    crate::leanh::lean_dec(v___x_1776_);
    if v___x_1777_ == 0 {
        let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: u32 = 0;
        let mut v___x_1780_: u8 = 0;
        v___x_1778_ = lean_nat_add(v_startPos_1768_, v_it_1772_);
        v___x_1779_ = lean_string_utf8_get_fast(v_str_1769_, v___x_1778_);
        v___x_1780_ = lean_uint32_dec_eq(v___x_1779_, v_c_1770_);
        if v___x_1780_ == 0 {
            let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_it_1772_);
            v___x_1781_ = lean_string_utf8_next_fast(v_str_1769_, v___x_1778_);
            crate::leanh::lean_dec(v___x_1778_);
            v___x_1782_ = lean_nat_sub(v___x_1781_, v_startPos_1768_);
            v___x_1783_ = crate::leanh::lean_apply_4(
                v_recur_1775_,
                v___x_1782_,
                v___x_1771_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1783_;
        } else {
            let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1778_);
            crate::leanh::lean_dec_ref(v_recur_1775_);
            crate::leanh::lean_dec(v___x_1771_);
            v___x_1784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1784_, 0, v_it_1772_);
            return v___x_1784_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_recur_1775_);
        crate::leanh::lean_dec(v_it_1772_);
        crate::leanh::lean_dec(v___x_1771_);
        crate::leanh::lean_inc(v_acc_1773_);
        return v_acc_1773_;
    }
}
pub unsafe fn l_Substring_Raw_posOf___lam__0___boxed(
    mut v_stopPos_1785_: *mut crate::leanh::LeanObject,
    mut v_startPos_1786_: *mut crate::leanh::LeanObject,
    mut v_str_1787_: *mut crate::leanh::LeanObject,
    mut v_c_1788_: *mut crate::leanh::LeanObject,
    mut v___x_1789_: *mut crate::leanh::LeanObject,
    mut v_it_1790_: *mut crate::leanh::LeanObject,
    mut v_acc_1791_: *mut crate::leanh::LeanObject,
    mut v_hP_1792_: *mut crate::leanh::LeanObject,
    mut v_recur_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1794_: u32 = 0;
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1794_ = crate::leanh::lean_unbox_uint32(v_c_1788_);
    crate::leanh::lean_dec(v_c_1788_);
    v_res_1795_ = l_Substring_Raw_posOf___lam__0(
        v_stopPos_1785_,
        v_startPos_1786_,
        v_str_1787_,
        v_c_boxed_1794_,
        v___x_1789_,
        v_it_1790_,
        v_acc_1791_,
        v_hP_1792_,
        v_recur_1793_,
    );
    crate::leanh::lean_dec(v_acc_1791_);
    crate::leanh::lean_dec_ref(v_str_1787_);
    crate::leanh::lean_dec(v_startPos_1786_);
    crate::leanh::lean_dec(v_stopPos_1785_);
    return v_res_1795_;
}
pub unsafe fn l_Substring_Raw_posOf(
    mut v_s_1796_: *mut crate::leanh::LeanObject,
    mut v_c_1797_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    v_str_1798_ = crate::leanh::lean_ctor_get(v_s_1796_, 0);
    crate::leanh::lean_inc_ref(v_str_1798_);
    v_startPos_1799_ = crate::leanh::lean_ctor_get(v_s_1796_, 1);
    crate::leanh::lean_inc(v_startPos_1799_);
    v_stopPos_1800_ = crate::leanh::lean_ctor_get(v_s_1796_, 2);
    crate::leanh::lean_inc(v_stopPos_1800_);
    crate::leanh::lean_dec_ref(v_s_1796_);
    v___x_1801_ = lean_string_is_valid_pos(v_str_1798_, v_startPos_1799_);
    if v___x_1801_ == 0 {
        let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_str_1798_);
        v___x_1802_ = lean_nat_sub(v_stopPos_1800_, v_startPos_1799_);
        crate::leanh::lean_dec(v_startPos_1799_);
        crate::leanh::lean_dec(v_stopPos_1800_);
        return v___x_1802_;
    } else {
        let mut v___x_1803_: u8 = 0;
        v___x_1803_ = lean_string_is_valid_pos(v_str_1798_, v_stopPos_1800_);
        if v___x_1803_ == 0 {
            let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_str_1798_);
            v___x_1804_ = lean_nat_sub(v_stopPos_1800_, v_startPos_1799_);
            crate::leanh::lean_dec(v_startPos_1799_);
            crate::leanh::lean_dec(v_stopPos_1800_);
            return v___x_1804_;
        } else {
            let mut v___x_1805_: u8 = 0;
            v___x_1805_ = lean_nat_dec_le(v_startPos_1799_, v_stopPos_1800_);
            if v___x_1805_ == 0 {
                let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_str_1798_);
                v___x_1806_ = lean_nat_sub(v_stopPos_1800_, v_startPos_1799_);
                crate::leanh::lean_dec(v_startPos_1799_);
                crate::leanh::lean_dec(v_stopPos_1800_);
                return v___x_1806_;
            } else {
                let mut v_searcher_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_searcher_1807_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1808_ = crate::leanh::lean_box(0);
                v___x_1809_ = crate::leanh::lean_box_uint32(v_c_1797_);
                crate::leanh::lean_inc(v_startPos_1799_);
                crate::leanh::lean_inc(v_stopPos_1800_);
                v___f_1810_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_posOf___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1810_, 0, v_stopPos_1800_);
                crate::leanh::lean_closure_set(v___f_1810_, 1, v_startPos_1799_);
                crate::leanh::lean_closure_set(v___f_1810_, 2, v_str_1798_);
                crate::leanh::lean_closure_set(v___f_1810_, 3, v___x_1809_);
                crate::leanh::lean_closure_set(v___f_1810_, 4, v___x_1808_);
                v___x_1811_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1810_,
                    v_searcher_1807_,
                    v___x_1808_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1811_) == 0 {
                    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1812_ = lean_nat_sub(v_stopPos_1800_, v_startPos_1799_);
                    crate::leanh::lean_dec(v_startPos_1799_);
                    crate::leanh::lean_dec(v_stopPos_1800_);
                    return v___x_1812_;
                } else {
                    let mut v_val_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_stopPos_1800_);
                    crate::leanh::lean_dec(v_startPos_1799_);
                    v_val_1813_ = crate::leanh::lean_ctor_get(v___x_1811_, 0);
                    crate::leanh::lean_inc(v_val_1813_);
                    crate::leanh::lean_dec_ref_known(v___x_1811_, 1);
                    return v_val_1813_;
                }
            }
        }
    }
}
pub unsafe fn l_Substring_Raw_posOf___boxed(
    mut v_s_1814_: *mut crate::leanh::LeanObject,
    mut v_c_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1816_: u32 = 0;
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1816_ = crate::leanh::lean_unbox_uint32(v_c_1815_);
    crate::leanh::lean_dec(v_c_1815_);
    v_res_1817_ = l_Substring_Raw_posOf(v_s_1814_, v_c_boxed_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Substring_Raw_drop(
    mut v_x_1818_: *mut crate::leanh::LeanObject,
    mut v_x_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut v_unused_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1820_ = crate::leanh::lean_ctor_get(v_x_1818_, 0);
                crate::leanh::lean_inc_ref(v_str_1820_);
                v_startPos_1821_ = crate::leanh::lean_ctor_get(v_x_1818_, 1);
                crate::leanh::lean_inc(v_startPos_1821_);
                v_stopPos_1822_ = crate::leanh::lean_ctor_get(v_x_1818_, 2);
                crate::leanh::lean_inc(v_stopPos_1822_);
                v___x_1823_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1824_ = l_Substring_Raw_nextn(v_x_1818_, v_x_1819_, v___x_1823_);
                v_isSharedCheck_1832_ = (!crate::leanh::lean_is_exclusive(v_x_1818_)) as u8;
                if v_isSharedCheck_1832_ == 0 {
                    v_unused_1833_ = crate::leanh::lean_ctor_get(v_x_1818_, 2);
                    crate::leanh::lean_dec(v_unused_1833_);
                    v_unused_1834_ = crate::leanh::lean_ctor_get(v_x_1818_, 1);
                    crate::leanh::lean_dec(v_unused_1834_);
                    v_unused_1835_ = crate::leanh::lean_ctor_get(v_x_1818_, 0);
                    crate::leanh::lean_dec(v_unused_1835_);
                    v___x_1826_ = v_x_1818_;
                    v_isShared_1827_ = v_isSharedCheck_1832_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1818_);
                    v___x_1826_ = crate::leanh::lean_box(0);
                    v_isShared_1827_ = v_isSharedCheck_1832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1828_ = lean_nat_add(v_startPos_1821_, v___x_1824_);
                crate::leanh::lean_dec(v___x_1824_);
                crate::leanh::lean_dec(v_startPos_1821_);
                if v_isShared_1827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1826_, 1, v___x_1828_);
                    v___x_1830_ = v___x_1826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_str_1820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_stopPos_1822_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_substring_drop(
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v_unused_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1838_ = crate::leanh::lean_ctor_get(v_a_1836_, 0);
                crate::leanh::lean_inc_ref(v_str_1838_);
                v_startPos_1839_ = crate::leanh::lean_ctor_get(v_a_1836_, 1);
                crate::leanh::lean_inc(v_startPos_1839_);
                v_stopPos_1840_ = crate::leanh::lean_ctor_get(v_a_1836_, 2);
                crate::leanh::lean_inc(v_stopPos_1840_);
                v___x_1841_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1842_ = l_Substring_Raw_nextn(v_a_1836_, v_a_1837_, v___x_1841_);
                v_isSharedCheck_1850_ = (!crate::leanh::lean_is_exclusive(v_a_1836_)) as u8;
                if v_isSharedCheck_1850_ == 0 {
                    v_unused_1851_ = crate::leanh::lean_ctor_get(v_a_1836_, 2);
                    crate::leanh::lean_dec(v_unused_1851_);
                    v_unused_1852_ = crate::leanh::lean_ctor_get(v_a_1836_, 1);
                    crate::leanh::lean_dec(v_unused_1852_);
                    v_unused_1853_ = crate::leanh::lean_ctor_get(v_a_1836_, 0);
                    crate::leanh::lean_dec(v_unused_1853_);
                    v___x_1844_ = v_a_1836_;
                    v_isShared_1845_ = v_isSharedCheck_1850_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1836_);
                    v___x_1844_ = crate::leanh::lean_box(0);
                    v_isShared_1845_ = v_isSharedCheck_1850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1846_ = lean_nat_add(v_startPos_1839_, v___x_1842_);
                crate::leanh::lean_dec(v___x_1842_);
                crate::leanh::lean_dec(v_startPos_1839_);
                if v_isShared_1845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1844_, 1, v___x_1846_);
                    v___x_1848_ = v___x_1844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1849_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_str_1838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_stopPos_1840_);
                    v___x_1848_ = v_reuseFailAlloc_1849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_dropRight(
    mut v_x_1854_: *mut crate::leanh::LeanObject,
    mut v_x_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v_unused_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1856_ = crate::leanh::lean_ctor_get(v_x_1854_, 0);
                crate::leanh::lean_inc_ref(v_str_1856_);
                v_startPos_1857_ = crate::leanh::lean_ctor_get(v_x_1854_, 1);
                crate::leanh::lean_inc(v_startPos_1857_);
                v_stopPos_1858_ = crate::leanh::lean_ctor_get(v_x_1854_, 2);
                v___x_1859_ = lean_nat_sub(v_stopPos_1858_, v_startPos_1857_);
                v___x_1860_ = l_Substring_Raw_prevn(v_x_1854_, v_x_1855_, v___x_1859_);
                v_isSharedCheck_1868_ = (!crate::leanh::lean_is_exclusive(v_x_1854_)) as u8;
                if v_isSharedCheck_1868_ == 0 {
                    v_unused_1869_ = crate::leanh::lean_ctor_get(v_x_1854_, 2);
                    crate::leanh::lean_dec(v_unused_1869_);
                    v_unused_1870_ = crate::leanh::lean_ctor_get(v_x_1854_, 1);
                    crate::leanh::lean_dec(v_unused_1870_);
                    v_unused_1871_ = crate::leanh::lean_ctor_get(v_x_1854_, 0);
                    crate::leanh::lean_dec(v_unused_1871_);
                    v___x_1862_ = v_x_1854_;
                    v_isShared_1863_ = v_isSharedCheck_1868_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1854_);
                    v___x_1862_ = crate::leanh::lean_box(0);
                    v_isShared_1863_ = v_isSharedCheck_1868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1864_ = lean_nat_add(v_startPos_1857_, v___x_1860_);
                crate::leanh::lean_dec(v___x_1860_);
                if v_isShared_1863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1862_, 2, v___x_1864_);
                    v___x_1866_ = v___x_1862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_str_1856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_startPos_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 2, v___x_1864_);
                    v___x_1866_ = v_reuseFailAlloc_1867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_take(
    mut v_x_1872_: *mut crate::leanh::LeanObject,
    mut v_x_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_unused_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1874_ = crate::leanh::lean_ctor_get(v_x_1872_, 0);
                crate::leanh::lean_inc_ref(v_str_1874_);
                v_startPos_1875_ = crate::leanh::lean_ctor_get(v_x_1872_, 1);
                crate::leanh::lean_inc(v_startPos_1875_);
                v___x_1876_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1877_ = l_Substring_Raw_nextn(v_x_1872_, v_x_1873_, v___x_1876_);
                v_isSharedCheck_1885_ = (!crate::leanh::lean_is_exclusive(v_x_1872_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v_unused_1886_ = crate::leanh::lean_ctor_get(v_x_1872_, 2);
                    crate::leanh::lean_dec(v_unused_1886_);
                    v_unused_1887_ = crate::leanh::lean_ctor_get(v_x_1872_, 1);
                    crate::leanh::lean_dec(v_unused_1887_);
                    v_unused_1888_ = crate::leanh::lean_ctor_get(v_x_1872_, 0);
                    crate::leanh::lean_dec(v_unused_1888_);
                    v___x_1879_ = v_x_1872_;
                    v_isShared_1880_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1872_);
                    v___x_1879_ = crate::leanh::lean_box(0);
                    v_isShared_1880_ = v_isSharedCheck_1885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1881_ = lean_nat_add(v_startPos_1875_, v___x_1877_);
                crate::leanh::lean_dec(v___x_1877_);
                if v_isShared_1880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1879_, 2, v___x_1881_);
                    v___x_1883_ = v___x_1879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_str_1874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_startPos_1875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 2, v___x_1881_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeRight(
    mut v_x_1889_: *mut crate::leanh::LeanObject,
    mut v_x_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_unused_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1891_ = crate::leanh::lean_ctor_get(v_x_1889_, 0);
                crate::leanh::lean_inc_ref(v_str_1891_);
                v_startPos_1892_ = crate::leanh::lean_ctor_get(v_x_1889_, 1);
                crate::leanh::lean_inc(v_startPos_1892_);
                v_stopPos_1893_ = crate::leanh::lean_ctor_get(v_x_1889_, 2);
                crate::leanh::lean_inc(v_stopPos_1893_);
                v___x_1894_ = lean_nat_sub(v_stopPos_1893_, v_startPos_1892_);
                v___x_1895_ = l_Substring_Raw_prevn(v_x_1889_, v_x_1890_, v___x_1894_);
                v_isSharedCheck_1903_ = (!crate::leanh::lean_is_exclusive(v_x_1889_)) as u8;
                if v_isSharedCheck_1903_ == 0 {
                    v_unused_1904_ = crate::leanh::lean_ctor_get(v_x_1889_, 2);
                    crate::leanh::lean_dec(v_unused_1904_);
                    v_unused_1905_ = crate::leanh::lean_ctor_get(v_x_1889_, 1);
                    crate::leanh::lean_dec(v_unused_1905_);
                    v_unused_1906_ = crate::leanh::lean_ctor_get(v_x_1889_, 0);
                    crate::leanh::lean_dec(v_unused_1906_);
                    v___x_1897_ = v_x_1889_;
                    v_isShared_1898_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1889_);
                    v___x_1897_ = crate::leanh::lean_box(0);
                    v_isShared_1898_ = v_isSharedCheck_1903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1899_ = lean_nat_add(v_startPos_1892_, v___x_1895_);
                crate::leanh::lean_dec(v___x_1895_);
                crate::leanh::lean_dec(v_startPos_1892_);
                if v_isShared_1898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1897_, 1, v___x_1899_);
                    v___x_1901_ = v___x_1897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_str_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_stopPos_1893_);
                    v___x_1901_ = v_reuseFailAlloc_1902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_atEnd(
    mut v_x_1907_: *mut crate::leanh::LeanObject,
    mut v_x_1908_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startPos_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    v_startPos_1909_ = crate::leanh::lean_ctor_get(v_x_1907_, 1);
    v_stopPos_1910_ = crate::leanh::lean_ctor_get(v_x_1907_, 2);
    v___x_1911_ = lean_nat_add(v_startPos_1909_, v_x_1908_);
    v___x_1912_ = lean_nat_dec_eq(v___x_1911_, v_stopPos_1910_);
    crate::leanh::lean_dec(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn l_Substring_Raw_atEnd___boxed(
    mut v_x_1913_: *mut crate::leanh::LeanObject,
    mut v_x_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1915_: u8 = 0;
    let mut v_r_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Substring_Raw_atEnd(v_x_1913_, v_x_1914_);
    crate::leanh::lean_dec(v_x_1914_);
    crate::leanh::lean_dec_ref(v_x_1913_);
    v_r_1916_ = crate::leanh::lean_box((v_res_1915_) as usize);
    return v_r_1916_;
}
pub unsafe fn l_Substring_Raw_extract(
    mut v_x_1921_: *mut crate::leanh::LeanObject,
    mut v_x_1922_: *mut crate::leanh::LeanObject,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1929_: u8 = 0;
    let mut v___y_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1924_ = crate::leanh::lean_ctor_get(v_x_1921_, 0);
                v_startPos_1925_ = crate::leanh::lean_ctor_get(v_x_1921_, 1);
                v_stopPos_1926_ = crate::leanh::lean_ctor_get(v_x_1921_, 2);
                v_isSharedCheck_1944_ = (!crate::leanh::lean_is_exclusive(v_x_1921_)) as u8;
                if v_isSharedCheck_1944_ == 0 {
                    v___x_1928_ = v_x_1921_;
                    v_isShared_1929_ = v_isSharedCheck_1944_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_1926_);
                    crate::leanh::lean_inc(v_startPos_1925_);
                    crate::leanh::lean_inc(v_str_1924_);
                    crate::leanh::lean_dec(v_x_1921_);
                    v___x_1928_ = crate::leanh::lean_box(0);
                    v_isShared_1929_ = v_isSharedCheck_1944_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1940_ = lean_nat_dec_le(v_x_1923_, v_x_1922_);
                if v___x_1940_ == 0 {
                    v___x_1941_ = lean_nat_add(v_startPos_1925_, v_x_1922_);
                    v___x_1942_ = lean_nat_dec_le(v_stopPos_1926_, v___x_1941_);
                    if v___x_1942_ == 0 {
                        v___y_1931_ = v___x_1941_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1941_);
                        crate::leanh::lean_inc(v_stopPos_1926_);
                        v___y_1931_ = v_stopPos_1926_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1928_);
                    crate::leanh::lean_dec(v_stopPos_1926_);
                    crate::leanh::lean_dec(v_startPos_1925_);
                    crate::leanh::lean_dec_ref(v_str_1924_);
                    v___x_1943_ = l_Substring_Raw_extract___closed__1;
                    return v___x_1943_;
                }
            }
            2 => {
                v___x_1932_ = lean_nat_add(v_startPos_1925_, v_x_1923_);
                crate::leanh::lean_dec(v_startPos_1925_);
                v___x_1933_ = lean_nat_dec_le(v_stopPos_1926_, v___x_1932_);
                if v___x_1933_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_1926_);
                    if v_isShared_1929_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1928_, 2, v___x_1932_);
                        crate::leanh::lean_ctor_set(v___x_1928_, 1, v___y_1931_);
                        v___x_1935_ = v___x_1928_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1936_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_str_1924_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___y_1931_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1936_, 2, v___x_1932_);
                        v___x_1935_ = v_reuseFailAlloc_1936_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1932_);
                    if v_isShared_1929_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1928_, 1, v___y_1931_);
                        v___x_1938_ = v___x_1928_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_str_1924_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___y_1931_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_stopPos_1926_);
                        v___x_1938_ = v_reuseFailAlloc_1939_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1935_;
            }
            4 => {
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_extract___boxed(
    mut v_x_1945_: *mut crate::leanh::LeanObject,
    mut v_x_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Substring_Raw_extract(v_x_1945_, v_x_1946_, v_x_1947_);
    crate::leanh::lean_dec(v_x_1947_);
    crate::leanh::lean_dec(v_x_1946_);
    return v_res_1948_;
}
pub unsafe fn lean_substring_extract(
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1957_: u8 = 0;
    let mut v___y_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1952_ = crate::leanh::lean_ctor_get(v_a_1949_, 0);
                v_startPos_1953_ = crate::leanh::lean_ctor_get(v_a_1949_, 1);
                v_stopPos_1954_ = crate::leanh::lean_ctor_get(v_a_1949_, 2);
                v_isSharedCheck_1972_ = (!crate::leanh::lean_is_exclusive(v_a_1949_)) as u8;
                if v_isSharedCheck_1972_ == 0 {
                    v___x_1956_ = v_a_1949_;
                    v_isShared_1957_ = v_isSharedCheck_1972_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_1954_);
                    crate::leanh::lean_inc(v_startPos_1953_);
                    crate::leanh::lean_inc(v_str_1952_);
                    crate::leanh::lean_dec(v_a_1949_);
                    v___x_1956_ = crate::leanh::lean_box(0);
                    v_isShared_1957_ = v_isSharedCheck_1972_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1968_ = lean_nat_dec_le(v_a_1951_, v_a_1950_);
                if v___x_1968_ == 0 {
                    v___x_1969_ = lean_nat_add(v_startPos_1953_, v_a_1950_);
                    crate::leanh::lean_dec(v_a_1950_);
                    v___x_1970_ = lean_nat_dec_le(v_stopPos_1954_, v___x_1969_);
                    if v___x_1970_ == 0 {
                        v___y_1959_ = v___x_1969_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1969_);
                        crate::leanh::lean_inc(v_stopPos_1954_);
                        v___y_1959_ = v_stopPos_1954_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1956_);
                    crate::leanh::lean_dec(v_stopPos_1954_);
                    crate::leanh::lean_dec(v_startPos_1953_);
                    crate::leanh::lean_dec_ref(v_str_1952_);
                    crate::leanh::lean_dec(v_a_1951_);
                    crate::leanh::lean_dec(v_a_1950_);
                    v___x_1971_ = l_Substring_Raw_extract___closed__1;
                    return v___x_1971_;
                }
            }
            2 => {
                v___x_1960_ = lean_nat_add(v_startPos_1953_, v_a_1951_);
                crate::leanh::lean_dec(v_a_1951_);
                crate::leanh::lean_dec(v_startPos_1953_);
                v___x_1961_ = lean_nat_dec_le(v_stopPos_1954_, v___x_1960_);
                if v___x_1961_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_1954_);
                    if v_isShared_1957_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1956_, 2, v___x_1960_);
                        crate::leanh::lean_ctor_set(v___x_1956_, 1, v___y_1959_);
                        v___x_1963_ = v___x_1956_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_str_1952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___y_1959_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 2, v___x_1960_);
                        v___x_1963_ = v_reuseFailAlloc_1964_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1960_);
                    if v_isShared_1957_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1956_, 1, v___y_1959_);
                        v___x_1966_ = v___x_1956_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1967_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_str_1952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___y_1959_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_stopPos_1954_);
                        v___x_1966_ = v_reuseFailAlloc_1967_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1963_;
            }
            4 => {
                return v___x_1966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Substring_Raw_extract___closed__0;
    v___x_1974_ = lean_string_utf8_byte_size(v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once
        ),
        _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0,
    );
    v___x_1976_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1977_ = l_Substring_Raw_extract___closed__0;
    v___x_1978_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1978_, 0, v___x_1977_);
    crate::leanh::lean_ctor_set(v___x_1978_, 1, v___x_1976_);
    crate::leanh::lean_ctor_set(v___x_1978_, 2, v___x_1975_);
    return v___x_1978_;
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(
    mut v_s_1979_: *mut crate::leanh::LeanObject,
    mut v_sep_1980_: *mut crate::leanh::LeanObject,
    mut v_b_1981_: *mut crate::leanh::LeanObject,
    mut v_i_1982_: *mut crate::leanh::LeanObject,
    mut v_j_1983_: *mut crate::leanh::LeanObject,
    mut v_r_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2059_: u8 = 0;
    let mut v_unused_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u32 = 0;
    let mut v___x_2065_: u32 = 0;
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1999_ = crate::leanh::lean_ctor_get(v_s_1979_, 0);
                v_startPos_2000_ = crate::leanh::lean_ctor_get(v_s_1979_, 1);
                v_stopPos_2001_ = crate::leanh::lean_ctor_get(v_s_1979_, 2);
                v___x_2028_ = lean_nat_sub(v_stopPos_2001_, v_startPos_2000_);
                v___x_2029_ = lean_nat_dec_lt(v_i_1982_, v___x_2028_);
                crate::leanh::lean_dec(v___x_2028_);
                if v___x_2029_ == 0 {
                    crate::leanh::lean_inc(v_stopPos_2001_);
                    crate::leanh::lean_inc(v_startPos_2000_);
                    crate::leanh::lean_inc_ref(v_str_1999_);
                    v_isSharedCheck_2059_ = (!crate::leanh::lean_is_exclusive(v_s_1979_)) as u8;
                    if v_isSharedCheck_2059_ == 0 {
                        v_unused_2060_ = crate::leanh::lean_ctor_get(v_s_1979_, 2);
                        crate::leanh::lean_dec(v_unused_2060_);
                        v_unused_2061_ = crate::leanh::lean_ctor_get(v_s_1979_, 1);
                        crate::leanh::lean_dec(v_unused_2061_);
                        v_unused_2062_ = crate::leanh::lean_ctor_get(v_s_1979_, 0);
                        crate::leanh::lean_dec(v_unused_2062_);
                        v___x_2031_ = v_s_1979_;
                        v_isShared_2032_ = v_isSharedCheck_2059_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_1979_);
                        v___x_2031_ = crate::leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2059_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_2063_ = lean_nat_add(v_startPos_2000_, v_i_1982_);
                    v___x_2064_ = lean_string_utf8_get(v_str_1999_, v___x_2063_);
                    v___x_2065_ = lean_string_utf8_get(v_sep_1980_, v_j_1983_);
                    v___x_2066_ = lean_uint32_dec_eq(v___x_2064_, v___x_2065_);
                    if v___x_2066_ == 0 {
                        crate::leanh::lean_dec(v_j_1983_);
                        v___x_2067_ = lean_nat_dec_eq(v___x_2063_, v_stopPos_2001_);
                        if v___x_2067_ == 0 {
                            crate::leanh::lean_dec(v_i_1982_);
                            v___x_2068_ = lean_string_utf8_next(v_str_1999_, v___x_2063_);
                            crate::leanh::lean_dec(v___x_2063_);
                            v___x_2069_ = lean_nat_sub(v___x_2068_, v_startPos_2000_);
                            crate::leanh::lean_dec(v___x_2068_);
                            v___y_1990_ = v___x_2069_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2063_);
                            v___y_1990_ = v_i_1982_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2070_ = lean_nat_dec_eq(v___x_2063_, v_stopPos_2001_);
                        if v___x_2070_ == 0 {
                            crate::leanh::lean_dec(v_i_1982_);
                            v___x_2071_ = lean_string_utf8_next(v_str_1999_, v___x_2063_);
                            crate::leanh::lean_dec(v___x_2063_);
                            v___x_2072_ = lean_nat_sub(v___x_2071_, v_startPos_2000_);
                            crate::leanh::lean_dec(v___x_2071_);
                            v___y_2012_ = v___x_2072_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2063_);
                            v___y_2012_ = v_i_1982_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1987_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1987_, 0, v___y_1986_);
                crate::leanh::lean_ctor_set(v___x_1987_, 1, v_r_1984_);
                v___x_1988_ = l_List_reverse___redArg(v___x_1987_);
                return v___x_1988_;
            }
            2 => {
                v___x_1991_ = crate::leanh::lean_unsigned_to_nat(0);
                v_i_1982_ = v___y_1990_;
                v_j_1983_ = v___x_1991_;
                state = 0;
                continue;
            }
            3 => {
                v___x_1997_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1997_, 0, v___y_1996_);
                crate::leanh::lean_ctor_set(v___x_1997_, 1, v_r_1984_);
                crate::leanh::lean_inc(v___y_1995_);
                v_b_1981_ = v___y_1995_;
                v_i_1982_ = v___y_1995_;
                v_j_1983_ = v___y_1994_;
                v_r_1984_ = v___x_1997_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2007_ = lean_nat_add(v_startPos_2000_, v___y_2004_);
                crate::leanh::lean_dec(v___y_2004_);
                v___x_2008_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2007_);
                if v___x_2008_ == 0 {
                    crate::leanh::lean_inc_ref(v_str_1999_);
                    v___x_2009_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v_str_1999_);
                    crate::leanh::lean_ctor_set(v___x_2009_, 1, v___y_2006_);
                    crate::leanh::lean_ctor_set(v___x_2009_, 2, v___x_2007_);
                    v___y_1994_ = v___y_2003_;
                    v___y_1995_ = v___y_2005_;
                    v___y_1996_ = v___x_2009_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2007_);
                    crate::leanh::lean_inc(v_stopPos_2001_);
                    crate::leanh::lean_inc_ref(v_str_1999_);
                    v___x_2010_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2010_, 0, v_str_1999_);
                    crate::leanh::lean_ctor_set(v___x_2010_, 1, v___y_2006_);
                    crate::leanh::lean_ctor_set(v___x_2010_, 2, v_stopPos_2001_);
                    v___y_1994_ = v___y_2003_;
                    v___y_1995_ = v___y_2005_;
                    v___y_1996_ = v___x_2010_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v_j_2013_ = lean_string_utf8_next(v_sep_1980_, v_j_1983_);
                crate::leanh::lean_dec(v_j_1983_);
                v___x_2014_ = lean_string_utf8_at_end(v_sep_1980_, v_j_2013_);
                if v___x_2014_ == 0 {
                    v_i_1982_ = v___y_2012_;
                    v_j_1983_ = v_j_2013_;
                    state = 0;
                    continue;
                } else {
                    v___x_2016_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2017_ = lean_nat_sub(v___y_2012_, v_j_2013_);
                    crate::leanh::lean_dec(v_j_2013_);
                    v___x_2018_ = lean_nat_dec_le(v___x_2017_, v_b_1981_);
                    if v___x_2018_ == 0 {
                        v___x_2019_ = lean_nat_add(v_startPos_2000_, v_b_1981_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2020_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2019_);
                        if v___x_2020_ == 0 {
                            v___y_2003_ = v___x_2016_;
                            v___y_2004_ = v___x_2017_;
                            v___y_2005_ = v___y_2012_;
                            v___y_2006_ = v___x_2019_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2019_);
                            crate::leanh::lean_inc(v_stopPos_2001_);
                            v___y_2003_ = v___x_2016_;
                            v___y_2004_ = v___x_2017_;
                            v___y_2005_ = v___y_2012_;
                            v___y_2006_ = v_stopPos_2001_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2017_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2021_ = l_Substring_Raw_extract___closed__1;
                        v___y_1994_ = v___x_2016_;
                        v___y_1995_ = v___y_2012_;
                        v___y_1996_ = v___x_2021_;
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2024_ = lean_nat_add(v_startPos_2000_, v_i_1982_);
                crate::leanh::lean_dec(v_i_1982_);
                crate::leanh::lean_dec(v_startPos_2000_);
                v___x_2025_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2024_);
                if v___x_2025_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_2001_);
                    v___x_2026_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2026_, 0, v_str_1999_);
                    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___y_2023_);
                    crate::leanh::lean_ctor_set(v___x_2026_, 2, v___x_2024_);
                    v___y_1986_ = v___x_2026_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2024_);
                    v___x_2027_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2027_, 0, v_str_1999_);
                    crate::leanh::lean_ctor_set(v___x_2027_, 1, v___y_2023_);
                    crate::leanh::lean_ctor_set(v___x_2027_, 2, v_stopPos_2001_);
                    v___y_1986_ = v___x_2027_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2033_ = lean_string_utf8_at_end(v_sep_1980_, v_j_1983_);
                if v___x_2033_ == 0 {
                    crate::leanh::lean_del_object(v___x_2031_);
                    crate::leanh::lean_dec(v_j_1983_);
                    v___x_2034_ = lean_nat_dec_le(v_i_1982_, v_b_1981_);
                    if v___x_2034_ == 0 {
                        v___x_2035_ = lean_nat_add(v_startPos_2000_, v_b_1981_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2036_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2035_);
                        if v___x_2036_ == 0 {
                            v___y_2023_ = v___x_2035_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2035_);
                            crate::leanh::lean_inc(v_stopPos_2001_);
                            v___y_2023_ = v_stopPos_2001_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_stopPos_2001_);
                        crate::leanh::lean_dec(v_startPos_2000_);
                        crate::leanh::lean_dec_ref(v_str_1999_);
                        crate::leanh::lean_dec(v_i_1982_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2037_ = l_Substring_Raw_extract___closed__1;
                        v___y_1986_ = v___x_2037_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2038_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once), _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1);
                    v___x_2044_ = lean_nat_sub(v_i_1982_, v_j_1983_);
                    crate::leanh::lean_dec(v_j_1983_);
                    crate::leanh::lean_dec(v_i_1982_);
                    v___x_2055_ = lean_nat_dec_le(v___x_2044_, v_b_1981_);
                    if v___x_2055_ == 0 {
                        v___x_2056_ = lean_nat_add(v_startPos_2000_, v_b_1981_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2057_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2056_);
                        if v___x_2057_ == 0 {
                            v___y_2046_ = v___x_2056_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2056_);
                            crate::leanh::lean_inc(v_stopPos_2001_);
                            v___y_2046_ = v_stopPos_2001_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2044_);
                        crate::leanh::lean_del_object(v___x_2031_);
                        crate::leanh::lean_dec(v_stopPos_2001_);
                        crate::leanh::lean_dec(v_startPos_2000_);
                        crate::leanh::lean_dec_ref(v_str_1999_);
                        crate::leanh::lean_dec(v_b_1981_);
                        v___x_2058_ = l_Substring_Raw_extract___closed__1;
                        v___y_2040_ = v___x_2058_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2041_, 0, v___y_2040_);
                crate::leanh::lean_ctor_set(v___x_2041_, 1, v_r_1984_);
                v___x_2042_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2038_);
                crate::leanh::lean_ctor_set(v___x_2042_, 1, v___x_2041_);
                v___x_2043_ = l_List_reverse___redArg(v___x_2042_);
                return v___x_2043_;
            }
            9 => {
                v___x_2047_ = lean_nat_add(v_startPos_2000_, v___x_2044_);
                crate::leanh::lean_dec(v___x_2044_);
                crate::leanh::lean_dec(v_startPos_2000_);
                v___x_2048_ = lean_nat_dec_le(v_stopPos_2001_, v___x_2047_);
                if v___x_2048_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_2001_);
                    if v_isShared_2032_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2031_, 2, v___x_2047_);
                        crate::leanh::lean_ctor_set(v___x_2031_, 1, v___y_2046_);
                        v___x_2050_ = v___x_2031_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_str_1999_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___y_2046_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___x_2047_);
                        v___x_2050_ = v_reuseFailAlloc_2051_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2047_);
                    if v_isShared_2032_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2031_, 1, v___y_2046_);
                        v___x_2053_ = v___x_2031_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_str_1999_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___y_2046_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_stopPos_2001_);
                        v___x_2053_ = v_reuseFailAlloc_2054_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                v___y_2040_ = v___x_2050_;
                state = 8;
                continue;
            }
            11 => {
                v___y_2040_ = v___x_2053_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(
    mut v_s_2073_: *mut crate::leanh::LeanObject,
    mut v_sep_2074_: *mut crate::leanh::LeanObject,
    mut v_b_2075_: *mut crate::leanh::LeanObject,
    mut v_i_2076_: *mut crate::leanh::LeanObject,
    mut v_j_2077_: *mut crate::leanh::LeanObject,
    mut v_r_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(
        v_s_2073_,
        v_sep_2074_,
        v_b_2075_,
        v_i_2076_,
        v_j_2077_,
        v_r_2078_,
    );
    crate::leanh::lean_dec_ref(v_sep_2074_);
    return v_res_2079_;
}
pub unsafe fn l_Substring_Raw_splitOn(
    mut v_s_2080_: *mut crate::leanh::LeanObject,
    mut v_sep_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    v___x_2082_ = l_Substring_Raw_extract___closed__0;
    v___x_2083_ = lean_string_dec_eq(v_sep_2081_, v___x_2082_);
    if v___x_2083_ == 0 {
        let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2084_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2085_ = crate::leanh::lean_box(0);
        v___x_2086_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(
            v_s_2080_,
            v_sep_2081_,
            v___x_2084_,
            v___x_2084_,
            v___x_2084_,
            v___x_2085_,
        );
        return v___x_2086_;
    } else {
        let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2087_ = crate::leanh::lean_box(0);
        v___x_2088_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2088_, 0, v_s_2080_);
        crate::leanh::lean_ctor_set(v___x_2088_, 1, v___x_2087_);
        return v___x_2088_;
    }
}
pub unsafe fn l_Substring_Raw_splitOn___boxed(
    mut v_s_2089_: *mut crate::leanh::LeanObject,
    mut v_sep_2090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_Substring_Raw_splitOn(v_s_2089_, v_sep_2090_);
    crate::leanh::lean_dec_ref(v_sep_2090_);
    return v_res_2091_;
}
pub unsafe fn l_Substring_Raw_foldl___redArg___lam__0(
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v_f_2093_: *mut crate::leanh::LeanObject,
    mut v_it_2094_: *mut crate::leanh::LeanObject,
    mut v_acc_2095_: *mut crate::leanh::LeanObject,
    mut v_hP_2096_: *mut crate::leanh::LeanObject,
    mut v_recur_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: u8 = 0;
    v_str_2098_ = crate::leanh::lean_ctor_get(v___y_2092_, 0);
    v_startInclusive_2099_ = crate::leanh::lean_ctor_get(v___y_2092_, 1);
    v_endExclusive_2100_ = crate::leanh::lean_ctor_get(v___y_2092_, 2);
    v___x_2101_ = lean_nat_sub(v_endExclusive_2100_, v_startInclusive_2099_);
    v___x_2102_ = lean_nat_dec_eq(v_it_2094_, v___x_2101_);
    crate::leanh::lean_dec(v___x_2101_);
    if v___x_2102_ == 0 {
        let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: u32 = 0;
        let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2103_ = lean_nat_add(v_startInclusive_2099_, v_it_2094_);
        v___x_2104_ = lean_string_utf8_next_fast(v_str_2098_, v___x_2103_);
        v___x_2105_ = lean_nat_sub(v___x_2104_, v_startInclusive_2099_);
        v___x_2106_ = lean_string_utf8_get_fast(v_str_2098_, v___x_2103_);
        crate::leanh::lean_dec(v___x_2103_);
        v___x_2107_ = crate::leanh::lean_box_uint32(v___x_2106_);
        v___x_2108_ = crate::leanh::lean_apply_2(v_f_2093_, v_acc_2095_, v___x_2107_);
        v___x_2109_ = crate::leanh::lean_apply_4(
            v_recur_2097_,
            v___x_2105_,
            v___x_2108_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_2109_;
    } else {
        crate::leanh::lean_dec(v_recur_2097_);
        crate::leanh::lean_dec(v_f_2093_);
        return v_acc_2095_;
    }
}
pub unsafe fn l_Substring_Raw_foldl___redArg___lam__0___boxed(
    mut v___y_2110_: *mut crate::leanh::LeanObject,
    mut v_f_2111_: *mut crate::leanh::LeanObject,
    mut v_it_2112_: *mut crate::leanh::LeanObject,
    mut v_acc_2113_: *mut crate::leanh::LeanObject,
    mut v_hP_2114_: *mut crate::leanh::LeanObject,
    mut v_recur_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Substring_Raw_foldl___redArg___lam__0(
        v___y_2110_,
        v_f_2111_,
        v_it_2112_,
        v_acc_2113_,
        v_hP_2114_,
        v_recur_2115_,
    );
    crate::leanh::lean_dec(v_it_2112_);
    crate::leanh::lean_dec_ref(v___y_2110_);
    return v_res_2116_;
}
pub unsafe fn _init_l_Substring_Raw_foldl___redArg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l_Substring_Raw_foldl___redArg___closed__2;
    v___x_2121_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2122_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_2123_ = l_Substring_Raw_foldl___redArg___closed__1;
    v___x_2124_ = l_Substring_Raw_foldl___redArg___closed__0;
    v___x_2125_ = l_mkPanicMessageWithDecl(
        v___x_2124_,
        v___x_2123_,
        v___x_2122_,
        v___x_2121_,
        v___x_2120_,
    );
    return v___x_2125_;
}
pub unsafe fn l_Substring_Raw_foldl___redArg(
    mut v_f_2126_: *mut crate::leanh::LeanObject,
    mut v_init_2127_: *mut crate::leanh::LeanObject,
    mut v_s_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2134_ = crate::leanh::lean_ctor_get(v_s_2128_, 0);
                v_startPos_2135_ = crate::leanh::lean_ctor_get(v_s_2128_, 1);
                v_stopPos_2136_ = crate::leanh::lean_ctor_get(v_s_2128_, 2);
                v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v_s_2128_)) as u8;
                if v_isSharedCheck_2150_ == 0 {
                    v___x_2138_ = v_s_2128_;
                    v_isShared_2139_ = v_isSharedCheck_2150_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2136_);
                    crate::leanh::lean_inc(v_startPos_2135_);
                    crate::leanh::lean_inc(v_str_2134_);
                    crate::leanh::lean_dec(v_s_2128_);
                    v___x_2138_ = crate::leanh::lean_box(0);
                    v_isShared_2139_ = v_isSharedCheck_2150_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2130_);
                v___f_2131_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2131_, 0, v___y_2130_);
                crate::leanh::lean_closure_set(v___f_2131_, 1, v_f_2126_);
                v___x_2132_ = l_String_Slice_positions(v___y_2130_);
                crate::leanh::lean_dec_ref(v___y_2130_);
                v___x_2133_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2131_,
                    v___x_2132_,
                    v_init_2127_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2133_;
            }
            2 => {
                v___x_2140_ = l_String_instInhabitedSlice;
                v___x_2144_ = lean_string_is_valid_pos(v_str_2134_, v_startPos_2135_);
                if v___x_2144_ == 0 {
                    crate::leanh::lean_del_object(v___x_2138_);
                    crate::leanh::lean_dec(v_stopPos_2136_);
                    crate::leanh::lean_dec(v_startPos_2135_);
                    crate::leanh::lean_dec_ref(v_str_2134_);
                    state = 3;
                    continue;
                } else {
                    v___x_2145_ = lean_string_is_valid_pos(v_str_2134_, v_stopPos_2136_);
                    if v___x_2145_ == 0 {
                        crate::leanh::lean_del_object(v___x_2138_);
                        crate::leanh::lean_dec(v_stopPos_2136_);
                        crate::leanh::lean_dec(v_startPos_2135_);
                        crate::leanh::lean_dec_ref(v_str_2134_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2146_ = lean_nat_dec_le(v_startPos_2135_, v_stopPos_2136_);
                        if v___x_2146_ == 0 {
                            crate::leanh::lean_del_object(v___x_2138_);
                            crate::leanh::lean_dec(v_stopPos_2136_);
                            crate::leanh::lean_dec(v_startPos_2135_);
                            crate::leanh::lean_dec_ref(v_str_2134_);
                            state = 3;
                            continue;
                        } else {
                            if v_isShared_2139_ == 0 {
                                v___x_2148_ = v___x_2138_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2149_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_str_2134_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2149_,
                                    1,
                                    v_startPos_2135_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2149_,
                                    2,
                                    v_stopPos_2136_,
                                );
                                v___x_2148_ = v_reuseFailAlloc_2149_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2142_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2143_ = l_panic___redArg(v___x_2140_, v___x_2142_);
                v___y_2130_ = v___x_2143_;
                state = 1;
                continue;
            }
            4 => {
                v___y_2130_ = v___x_2148_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_foldl(
    mut v_00_u03b1_2151_: *mut crate::leanh::LeanObject,
    mut v_f_2152_: *mut crate::leanh::LeanObject,
    mut v_init_2153_: *mut crate::leanh::LeanObject,
    mut v_s_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u8 = 0;
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2160_ = crate::leanh::lean_ctor_get(v_s_2154_, 0);
                v_startPos_2161_ = crate::leanh::lean_ctor_get(v_s_2154_, 1);
                v_stopPos_2162_ = crate::leanh::lean_ctor_get(v_s_2154_, 2);
                v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v_s_2154_)) as u8;
                if v_isSharedCheck_2176_ == 0 {
                    v___x_2164_ = v_s_2154_;
                    v_isShared_2165_ = v_isSharedCheck_2176_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2162_);
                    crate::leanh::lean_inc(v_startPos_2161_);
                    crate::leanh::lean_inc(v_str_2160_);
                    crate::leanh::lean_dec(v_s_2154_);
                    v___x_2164_ = crate::leanh::lean_box(0);
                    v_isShared_2165_ = v_isSharedCheck_2176_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2156_);
                v___f_2157_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2157_, 0, v___y_2156_);
                crate::leanh::lean_closure_set(v___f_2157_, 1, v_f_2152_);
                v___x_2158_ = l_String_Slice_positions(v___y_2156_);
                crate::leanh::lean_dec_ref(v___y_2156_);
                v___x_2159_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2157_,
                    v___x_2158_,
                    v_init_2153_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2159_;
            }
            2 => {
                v___x_2166_ = l_String_instInhabitedSlice;
                v___x_2170_ = lean_string_is_valid_pos(v_str_2160_, v_startPos_2161_);
                if v___x_2170_ == 0 {
                    crate::leanh::lean_del_object(v___x_2164_);
                    crate::leanh::lean_dec(v_stopPos_2162_);
                    crate::leanh::lean_dec(v_startPos_2161_);
                    crate::leanh::lean_dec_ref(v_str_2160_);
                    state = 3;
                    continue;
                } else {
                    v___x_2171_ = lean_string_is_valid_pos(v_str_2160_, v_stopPos_2162_);
                    if v___x_2171_ == 0 {
                        crate::leanh::lean_del_object(v___x_2164_);
                        crate::leanh::lean_dec(v_stopPos_2162_);
                        crate::leanh::lean_dec(v_startPos_2161_);
                        crate::leanh::lean_dec_ref(v_str_2160_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2172_ = lean_nat_dec_le(v_startPos_2161_, v_stopPos_2162_);
                        if v___x_2172_ == 0 {
                            crate::leanh::lean_del_object(v___x_2164_);
                            crate::leanh::lean_dec(v_stopPos_2162_);
                            crate::leanh::lean_dec(v_startPos_2161_);
                            crate::leanh::lean_dec_ref(v_str_2160_);
                            state = 3;
                            continue;
                        } else {
                            if v_isShared_2165_ == 0 {
                                v___x_2174_ = v___x_2164_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2175_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_str_2160_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2175_,
                                    1,
                                    v_startPos_2161_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2175_,
                                    2,
                                    v_stopPos_2162_,
                                );
                                v___x_2174_ = v_reuseFailAlloc_2175_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2168_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2169_ = l_panic___redArg(v___x_2166_, v___x_2168_);
                v___y_2156_ = v___x_2169_;
                state = 1;
                continue;
            }
            4 => {
                v___y_2156_ = v___x_2174_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_foldr___redArg___lam__0(
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v_f_2178_: *mut crate::leanh::LeanObject,
    mut v_it_2179_: *mut crate::leanh::LeanObject,
    mut v_acc_2180_: *mut crate::leanh::LeanObject,
    mut v_hP_2181_: *mut crate::leanh::LeanObject,
    mut v_recur_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    v___x_2183_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2184_ = lean_nat_dec_eq(v_it_2179_, v___x_2183_);
    if v___x_2184_ == 0 {
        let mut v_str_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_prevPos_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: u32 = 0;
        let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_str_2185_ = crate::leanh::lean_ctor_get(v___y_2177_, 0);
        v_startInclusive_2186_ = crate::leanh::lean_ctor_get(v___y_2177_, 1);
        v___x_2187_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2188_ = lean_nat_sub(v_it_2179_, v___x_2187_);
        v_prevPos_2189_ = l_String_Slice_posLE(v___y_2177_, v___x_2188_);
        v___x_2190_ = lean_nat_add(v_startInclusive_2186_, v_prevPos_2189_);
        v___x_2191_ = lean_string_utf8_get_fast(v_str_2185_, v___x_2190_);
        crate::leanh::lean_dec(v___x_2190_);
        v___x_2192_ = crate::leanh::lean_box_uint32(v___x_2191_);
        v___x_2193_ = crate::leanh::lean_apply_2(v_f_2178_, v___x_2192_, v_acc_2180_);
        v___x_2194_ = crate::leanh::lean_apply_4(
            v_recur_2182_,
            v_prevPos_2189_,
            v___x_2193_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_2194_;
    } else {
        crate::leanh::lean_dec(v_recur_2182_);
        crate::leanh::lean_dec(v_f_2178_);
        return v_acc_2180_;
    }
}
pub unsafe fn l_Substring_Raw_foldr___redArg___lam__0___boxed(
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v_f_2196_: *mut crate::leanh::LeanObject,
    mut v_it_2197_: *mut crate::leanh::LeanObject,
    mut v_acc_2198_: *mut crate::leanh::LeanObject,
    mut v_hP_2199_: *mut crate::leanh::LeanObject,
    mut v_recur_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Substring_Raw_foldr___redArg___lam__0(
        v___y_2195_,
        v_f_2196_,
        v_it_2197_,
        v_acc_2198_,
        v_hP_2199_,
        v_recur_2200_,
    );
    crate::leanh::lean_dec(v_it_2197_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    return v_res_2201_;
}
pub unsafe fn l_Substring_Raw_foldr___redArg(
    mut v_f_2202_: *mut crate::leanh::LeanObject,
    mut v_init_2203_: *mut crate::leanh::LeanObject,
    mut v_s_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2210_ = crate::leanh::lean_ctor_get(v_s_2204_, 0);
                v_startPos_2211_ = crate::leanh::lean_ctor_get(v_s_2204_, 1);
                v_stopPos_2212_ = crate::leanh::lean_ctor_get(v_s_2204_, 2);
                v_isSharedCheck_2226_ = (!crate::leanh::lean_is_exclusive(v_s_2204_)) as u8;
                if v_isSharedCheck_2226_ == 0 {
                    v___x_2214_ = v_s_2204_;
                    v_isShared_2215_ = v_isSharedCheck_2226_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2212_);
                    crate::leanh::lean_inc(v_startPos_2211_);
                    crate::leanh::lean_inc(v_str_2210_);
                    crate::leanh::lean_dec(v_s_2204_);
                    v___x_2214_ = crate::leanh::lean_box(0);
                    v_isShared_2215_ = v_isSharedCheck_2226_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2206_);
                v___f_2207_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2207_, 0, v___y_2206_);
                crate::leanh::lean_closure_set(v___f_2207_, 1, v_f_2202_);
                v___x_2208_ = l_String_Slice_revPositions(v___y_2206_);
                crate::leanh::lean_dec_ref(v___y_2206_);
                v___x_2209_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2207_,
                    v___x_2208_,
                    v_init_2203_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2209_;
            }
            2 => {
                v___x_2216_ = l_String_instInhabitedSlice;
                v___x_2220_ = lean_string_is_valid_pos(v_str_2210_, v_startPos_2211_);
                if v___x_2220_ == 0 {
                    crate::leanh::lean_del_object(v___x_2214_);
                    crate::leanh::lean_dec(v_stopPos_2212_);
                    crate::leanh::lean_dec(v_startPos_2211_);
                    crate::leanh::lean_dec_ref(v_str_2210_);
                    state = 3;
                    continue;
                } else {
                    v___x_2221_ = lean_string_is_valid_pos(v_str_2210_, v_stopPos_2212_);
                    if v___x_2221_ == 0 {
                        crate::leanh::lean_del_object(v___x_2214_);
                        crate::leanh::lean_dec(v_stopPos_2212_);
                        crate::leanh::lean_dec(v_startPos_2211_);
                        crate::leanh::lean_dec_ref(v_str_2210_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2222_ = lean_nat_dec_le(v_startPos_2211_, v_stopPos_2212_);
                        if v___x_2222_ == 0 {
                            crate::leanh::lean_del_object(v___x_2214_);
                            crate::leanh::lean_dec(v_stopPos_2212_);
                            crate::leanh::lean_dec(v_startPos_2211_);
                            crate::leanh::lean_dec_ref(v_str_2210_);
                            state = 3;
                            continue;
                        } else {
                            if v_isShared_2215_ == 0 {
                                v___x_2224_ = v___x_2214_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2225_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_str_2210_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2225_,
                                    1,
                                    v_startPos_2211_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2225_,
                                    2,
                                    v_stopPos_2212_,
                                );
                                v___x_2224_ = v_reuseFailAlloc_2225_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2218_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2219_ = l_panic___redArg(v___x_2216_, v___x_2218_);
                v___y_2206_ = v___x_2219_;
                state = 1;
                continue;
            }
            4 => {
                v___y_2206_ = v___x_2224_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_foldr(
    mut v_00_u03b1_2227_: *mut crate::leanh::LeanObject,
    mut v_f_2228_: *mut crate::leanh::LeanObject,
    mut v_init_2229_: *mut crate::leanh::LeanObject,
    mut v_s_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2236_ = crate::leanh::lean_ctor_get(v_s_2230_, 0);
                v_startPos_2237_ = crate::leanh::lean_ctor_get(v_s_2230_, 1);
                v_stopPos_2238_ = crate::leanh::lean_ctor_get(v_s_2230_, 2);
                v_isSharedCheck_2252_ = (!crate::leanh::lean_is_exclusive(v_s_2230_)) as u8;
                if v_isSharedCheck_2252_ == 0 {
                    v___x_2240_ = v_s_2230_;
                    v_isShared_2241_ = v_isSharedCheck_2252_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2238_);
                    crate::leanh::lean_inc(v_startPos_2237_);
                    crate::leanh::lean_inc(v_str_2236_);
                    crate::leanh::lean_dec(v_s_2230_);
                    v___x_2240_ = crate::leanh::lean_box(0);
                    v_isShared_2241_ = v_isSharedCheck_2252_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2232_);
                v___f_2233_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2233_, 0, v___y_2232_);
                crate::leanh::lean_closure_set(v___f_2233_, 1, v_f_2228_);
                v___x_2234_ = l_String_Slice_revPositions(v___y_2232_);
                crate::leanh::lean_dec_ref(v___y_2232_);
                v___x_2235_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2233_,
                    v___x_2234_,
                    v_init_2229_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2235_;
            }
            2 => {
                v___x_2242_ = l_String_instInhabitedSlice;
                v___x_2246_ = lean_string_is_valid_pos(v_str_2236_, v_startPos_2237_);
                if v___x_2246_ == 0 {
                    crate::leanh::lean_del_object(v___x_2240_);
                    crate::leanh::lean_dec(v_stopPos_2238_);
                    crate::leanh::lean_dec(v_startPos_2237_);
                    crate::leanh::lean_dec_ref(v_str_2236_);
                    state = 3;
                    continue;
                } else {
                    v___x_2247_ = lean_string_is_valid_pos(v_str_2236_, v_stopPos_2238_);
                    if v___x_2247_ == 0 {
                        crate::leanh::lean_del_object(v___x_2240_);
                        crate::leanh::lean_dec(v_stopPos_2238_);
                        crate::leanh::lean_dec(v_startPos_2237_);
                        crate::leanh::lean_dec_ref(v_str_2236_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2248_ = lean_nat_dec_le(v_startPos_2237_, v_stopPos_2238_);
                        if v___x_2248_ == 0 {
                            crate::leanh::lean_del_object(v___x_2240_);
                            crate::leanh::lean_dec(v_stopPos_2238_);
                            crate::leanh::lean_dec(v_startPos_2237_);
                            crate::leanh::lean_dec_ref(v_str_2236_);
                            state = 3;
                            continue;
                        } else {
                            if v_isShared_2241_ == 0 {
                                v___x_2250_ = v___x_2240_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2251_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_str_2236_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2251_,
                                    1,
                                    v_startPos_2237_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2251_,
                                    2,
                                    v_stopPos_2238_,
                                );
                                v___x_2250_ = v_reuseFailAlloc_2251_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2244_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2245_ = l_panic___redArg(v___x_2242_, v___x_2244_);
                v___y_2232_ = v___x_2245_;
                state = 1;
                continue;
            }
            4 => {
                v___y_2232_ = v___x_2250_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_any___lam__0(
    mut v___x_2253_: *mut crate::leanh::LeanObject,
    mut v_s_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_2254_, v___x_2253_, v___y_2255_, crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___y_2258_, v___y_2259_, v___y_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Substring_Raw_any(
    mut v_s_2262_: *mut crate::leanh::LeanObject,
    mut v_p_2263_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: u8 = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u8 = 0;
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_2263_);
                v___x_2264_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_2263_);
                v_str_2265_ = crate::leanh::lean_ctor_get(v_s_2262_, 0);
                v_startPos_2266_ = crate::leanh::lean_ctor_get(v_s_2262_, 1);
                v_stopPos_2267_ = crate::leanh::lean_ctor_get(v_s_2262_, 2);
                v_isSharedCheck_2285_ = (!crate::leanh::lean_is_exclusive(v_s_2262_)) as u8;
                if v_isSharedCheck_2285_ == 0 {
                    v___x_2269_ = v_s_2262_;
                    v_isShared_2270_ = v_isSharedCheck_2285_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2267_);
                    crate::leanh::lean_inc(v_startPos_2266_);
                    crate::leanh::lean_inc(v_str_2265_);
                    crate::leanh::lean_dec(v_s_2262_);
                    v___x_2269_ = crate::leanh::lean_box(0);
                    v_isShared_2270_ = v_isSharedCheck_2285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2271_ = l_String_instInhabitedSlice;
                v___f_2272_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_any___lam__0 as *mut core::ffi::c_void,
                    8,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2272_, 0, v___x_2264_);
                v___x_2273_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_2273_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2273_, 1, v_p_2263_);
                v___x_2278_ = lean_string_is_valid_pos(v_str_2265_, v_startPos_2266_);
                if v___x_2278_ == 0 {
                    crate::leanh::lean_del_object(v___x_2269_);
                    crate::leanh::lean_dec(v_stopPos_2267_);
                    crate::leanh::lean_dec(v_startPos_2266_);
                    crate::leanh::lean_dec_ref(v_str_2265_);
                    state = 2;
                    continue;
                } else {
                    v___x_2279_ = lean_string_is_valid_pos(v_str_2265_, v_stopPos_2267_);
                    if v___x_2279_ == 0 {
                        crate::leanh::lean_del_object(v___x_2269_);
                        crate::leanh::lean_dec(v_stopPos_2267_);
                        crate::leanh::lean_dec(v_startPos_2266_);
                        crate::leanh::lean_dec_ref(v_str_2265_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2280_ = lean_nat_dec_le(v_startPos_2266_, v_stopPos_2267_);
                        if v___x_2280_ == 0 {
                            crate::leanh::lean_del_object(v___x_2269_);
                            crate::leanh::lean_dec(v_stopPos_2267_);
                            crate::leanh::lean_dec(v_startPos_2266_);
                            crate::leanh::lean_dec_ref(v_str_2265_);
                            state = 2;
                            continue;
                        } else {
                            if v_isShared_2270_ == 0 {
                                v___x_2282_ = v___x_2269_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2284_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_str_2265_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2284_,
                                    1,
                                    v_startPos_2266_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2284_,
                                    2,
                                    v_stopPos_2267_,
                                );
                                v___x_2282_ = v_reuseFailAlloc_2284_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2275_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2276_ = l_panic___redArg(v___x_2271_, v___x_2275_);
                v___x_2277_ =
                    l_String_Slice_contains___redArg(v___f_2272_, v___x_2276_, v___x_2273_);
                return v___x_2277_;
            }
            3 => {
                v___x_2283_ =
                    l_String_Slice_contains___redArg(v___f_2272_, v___x_2282_, v___x_2273_);
                return v___x_2283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_any___boxed(
    mut v_s_2286_: *mut crate::leanh::LeanObject,
    mut v_p_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Substring_Raw_any(v_s_2286_, v_p_2287_);
    v_r_2289_ = crate::leanh::lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l_Substring_Raw_all(
    mut v_s_2290_: *mut crate::leanh::LeanObject,
    mut v_p_2291_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v_str_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2301_ = crate::leanh::lean_ctor_get(v_s_2290_, 0);
                v_startPos_2302_ = crate::leanh::lean_ctor_get(v_s_2290_, 1);
                v_stopPos_2303_ = crate::leanh::lean_ctor_get(v_s_2290_, 2);
                v_isSharedCheck_2319_ = (!crate::leanh::lean_is_exclusive(v_s_2290_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v___x_2305_ = v_s_2290_;
                    v_isShared_2306_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2303_);
                    crate::leanh::lean_inc(v_startPos_2302_);
                    crate::leanh::lean_inc(v_str_2301_);
                    crate::leanh::lean_dec(v_s_2290_);
                    v___x_2305_ = crate::leanh::lean_box(0);
                    v_isShared_2306_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2296_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_2291_);
                v___x_2297_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2298_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___y_2293_, v___x_2297_, v___x_2296_);
                crate::leanh::lean_dec_ref(v___y_2293_);
                v___x_2299_ = lean_nat_sub(v_endExclusive_2295_, v_startInclusive_2294_);
                crate::leanh::lean_dec(v_startInclusive_2294_);
                crate::leanh::lean_dec(v_endExclusive_2295_);
                v___x_2300_ = lean_nat_dec_eq(v___x_2298_, v___x_2299_);
                crate::leanh::lean_dec(v___x_2299_);
                crate::leanh::lean_dec(v___x_2298_);
                return v___x_2300_;
            }
            2 => {
                v___x_2307_ = l_String_instInhabitedSlice;
                v___x_2313_ = lean_string_is_valid_pos(v_str_2301_, v_startPos_2302_);
                if v___x_2313_ == 0 {
                    crate::leanh::lean_del_object(v___x_2305_);
                    crate::leanh::lean_dec(v_stopPos_2303_);
                    crate::leanh::lean_dec(v_startPos_2302_);
                    crate::leanh::lean_dec_ref(v_str_2301_);
                    state = 3;
                    continue;
                } else {
                    v___x_2314_ = lean_string_is_valid_pos(v_str_2301_, v_stopPos_2303_);
                    if v___x_2314_ == 0 {
                        crate::leanh::lean_del_object(v___x_2305_);
                        crate::leanh::lean_dec(v_stopPos_2303_);
                        crate::leanh::lean_dec(v_startPos_2302_);
                        crate::leanh::lean_dec_ref(v_str_2301_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2315_ = lean_nat_dec_le(v_startPos_2302_, v_stopPos_2303_);
                        if v___x_2315_ == 0 {
                            crate::leanh::lean_del_object(v___x_2305_);
                            crate::leanh::lean_dec(v_stopPos_2303_);
                            crate::leanh::lean_dec(v_startPos_2302_);
                            crate::leanh::lean_dec_ref(v_str_2301_);
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_stopPos_2303_);
                            crate::leanh::lean_inc(v_startPos_2302_);
                            if v_isShared_2306_ == 0 {
                                v___x_2317_ = v___x_2305_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2318_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_str_2301_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2318_,
                                    1,
                                    v_startPos_2302_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2318_,
                                    2,
                                    v_stopPos_2303_,
                                );
                                v___x_2317_ = v_reuseFailAlloc_2318_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2309_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2310_ = l_panic___redArg(v___x_2307_, v___x_2309_);
                v_startInclusive_2311_ = crate::leanh::lean_ctor_get(v___x_2310_, 1);
                crate::leanh::lean_inc(v_startInclusive_2311_);
                v_endExclusive_2312_ = crate::leanh::lean_ctor_get(v___x_2310_, 2);
                crate::leanh::lean_inc(v_endExclusive_2312_);
                v___y_2293_ = v___x_2310_;
                v_startInclusive_2294_ = v_startInclusive_2311_;
                v_endExclusive_2295_ = v_endExclusive_2312_;
                state = 1;
                continue;
            }
            4 => {
                v___y_2293_ = v___x_2317_;
                v_startInclusive_2294_ = v_startPos_2302_;
                v_endExclusive_2295_ = v_stopPos_2303_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_all___boxed(
    mut v_s_2320_: *mut crate::leanh::LeanObject,
    mut v_p_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2322_: u8 = 0;
    let mut v_r_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Substring_Raw_all(v_s_2320_, v_p_2321_);
    v_r_2323_ = crate::leanh::lean_box((v_res_2322_) as usize);
    return v_r_2323_;
}
pub unsafe fn l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(
    mut v_msg_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_String_instInhabitedSlice;
    v___x_2326_ = lean_panic_fn_borrowed(v___x_2325_, v_msg_2324_);
    return v___x_2326_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(
    mut v_p_2327_: *mut crate::leanh::LeanObject,
    mut v_s_2328_: *mut crate::leanh::LeanObject,
    mut v_pos_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: u32 = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2330_ = crate::leanh::lean_ctor_get(v_s_2328_, 0);
                v_startInclusive_2331_ = crate::leanh::lean_ctor_get(v_s_2328_, 1);
                v_endExclusive_2332_ = crate::leanh::lean_ctor_get(v_s_2328_, 2);
                v___x_2333_ = lean_nat_add(v_startInclusive_2331_, v_pos_2329_);
                v___x_2334_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2335_ = lean_nat_sub(v_endExclusive_2332_, v___x_2333_);
                v___x_2336_ = lean_nat_dec_eq(v___x_2334_, v___x_2335_);
                crate::leanh::lean_dec(v___x_2335_);
                if v___x_2336_ == 0 {
                    v___x_2337_ = lean_string_utf8_get_fast(v_str_2330_, v___x_2333_);
                    v___x_2338_ = crate::leanh::lean_box_uint32(v___x_2337_);
                    crate::leanh::lean_inc_ref(v_p_2327_);
                    v___x_2339_ = crate::leanh::lean_apply_1(v_p_2327_, v___x_2338_);
                    v___x_2340_ = (crate::leanh::lean_unbox(v___x_2339_) as u8);
                    if v___x_2340_ == 0 {
                        crate::leanh::lean_dec(v___x_2333_);
                        crate::leanh::lean_dec_ref(v_p_2327_);
                        return v_pos_2329_;
                    } else {
                        v___x_2341_ = lean_string_utf8_next_fast(v_str_2330_, v___x_2333_);
                        v___x_2342_ = lean_nat_sub(v___x_2341_, v___x_2333_);
                        crate::leanh::lean_dec(v___x_2333_);
                        v___x_2343_ = lean_nat_add(v_pos_2329_, v___x_2342_);
                        crate::leanh::lean_dec(v___x_2342_);
                        v___x_2344_ = lean_nat_dec_lt(v_pos_2329_, v___x_2343_);
                        if v___x_2344_ == 0 {
                            crate::leanh::lean_dec(v___x_2343_);
                            crate::leanh::lean_dec_ref(v_p_2327_);
                            return v_pos_2329_;
                        } else {
                            crate::leanh::lean_dec(v_pos_2329_);
                            v_pos_2329_ = v___x_2343_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2333_);
                    crate::leanh::lean_dec_ref(v_p_2327_);
                    return v_pos_2329_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(
    mut v_p_2346_: *mut crate::leanh::LeanObject,
    mut v_s_2347_: *mut crate::leanh::LeanObject,
    mut v_pos_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(
        v_p_2346_,
        v_s_2347_,
        v_pos_2348_,
    );
    crate::leanh::lean_dec_ref(v_s_2347_);
    return v_res_2349_;
}
pub unsafe fn lean_substring_all(
    mut v_s_2350_: *mut crate::leanh::LeanObject,
    mut v_p_2351_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: u8 = 0;
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2365_ = crate::leanh::lean_ctor_get(v_s_2350_, 0);
                v_startPos_2366_ = crate::leanh::lean_ctor_get(v_s_2350_, 1);
                v_stopPos_2367_ = crate::leanh::lean_ctor_get(v_s_2350_, 2);
                v_isSharedCheck_2377_ = (!crate::leanh::lean_is_exclusive(v_s_2350_)) as u8;
                if v_isSharedCheck_2377_ == 0 {
                    v___x_2369_ = v_s_2350_;
                    v_isShared_2370_ = v_isSharedCheck_2377_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2367_);
                    crate::leanh::lean_inc(v_startPos_2366_);
                    crate::leanh::lean_inc(v_str_2365_);
                    crate::leanh::lean_dec(v_s_2350_);
                    v___x_2369_ = crate::leanh::lean_box(0);
                    v_isShared_2370_ = v_isSharedCheck_2377_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_2356_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2357_ =
                    l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(
                        v_p_2351_,
                        v___y_2353_,
                        v___x_2356_,
                    );
                crate::leanh::lean_dec_ref(v___y_2353_);
                v___x_2358_ = lean_nat_sub(v_endExclusive_2355_, v_startInclusive_2354_);
                crate::leanh::lean_dec(v_startInclusive_2354_);
                crate::leanh::lean_dec(v_endExclusive_2355_);
                v___x_2359_ = lean_nat_dec_eq(v___x_2357_, v___x_2358_);
                crate::leanh::lean_dec(v___x_2358_);
                crate::leanh::lean_dec(v___x_2357_);
                return v___x_2359_;
            }
            2 => {
                v___x_2361_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2362_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_2361_);
                v_startInclusive_2363_ = crate::leanh::lean_ctor_get(v___x_2362_, 1);
                crate::leanh::lean_inc(v_startInclusive_2363_);
                v_endExclusive_2364_ = crate::leanh::lean_ctor_get(v___x_2362_, 2);
                crate::leanh::lean_inc(v_endExclusive_2364_);
                v___y_2353_ = v___x_2362_;
                v_startInclusive_2354_ = v_startInclusive_2363_;
                v_endExclusive_2355_ = v_endExclusive_2364_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2371_ = lean_string_is_valid_pos(v_str_2365_, v_startPos_2366_);
                if v___x_2371_ == 0 {
                    crate::leanh::lean_del_object(v___x_2369_);
                    crate::leanh::lean_dec(v_stopPos_2367_);
                    crate::leanh::lean_dec(v_startPos_2366_);
                    crate::leanh::lean_dec_ref(v_str_2365_);
                    state = 2;
                    continue;
                } else {
                    v___x_2372_ = lean_string_is_valid_pos(v_str_2365_, v_stopPos_2367_);
                    if v___x_2372_ == 0 {
                        crate::leanh::lean_del_object(v___x_2369_);
                        crate::leanh::lean_dec(v_stopPos_2367_);
                        crate::leanh::lean_dec(v_startPos_2366_);
                        crate::leanh::lean_dec_ref(v_str_2365_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2373_ = lean_nat_dec_le(v_startPos_2366_, v_stopPos_2367_);
                        if v___x_2373_ == 0 {
                            crate::leanh::lean_del_object(v___x_2369_);
                            crate::leanh::lean_dec(v_stopPos_2367_);
                            crate::leanh::lean_dec(v_startPos_2366_);
                            crate::leanh::lean_dec_ref(v_str_2365_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_stopPos_2367_);
                            crate::leanh::lean_inc(v_startPos_2366_);
                            if v_isShared_2370_ == 0 {
                                v___x_2375_ = v___x_2369_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2376_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_str_2365_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2376_,
                                    1,
                                    v_startPos_2366_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2376_,
                                    2,
                                    v_stopPos_2367_,
                                );
                                v___x_2375_ = v_reuseFailAlloc_2376_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___y_2353_ = v___x_2375_;
                v_startInclusive_2354_ = v_startPos_2366_;
                v_endExclusive_2355_ = v_stopPos_2367_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_Internal_allImpl___boxed(
    mut v_s_2378_: *mut crate::leanh::LeanObject,
    mut v_p_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2380_: u8 = 0;
    let mut v_r_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = lean_substring_all(v_s_2378_, v_p_2379_);
    v_r_2381_ = crate::leanh::lean_box((v_res_2380_) as usize);
    return v_r_2381_;
}
pub unsafe fn l_Substring_Raw_contains___lam__0(mut v_c_2382_: u32, mut v_a_2383_: u32) -> u8 {
    let mut v___x_2384_: u8 = 0;
    v___x_2384_ = lean_uint32_dec_eq(v_a_2383_, v_c_2382_);
    return v___x_2384_;
}
pub unsafe fn l_Substring_Raw_contains___lam__0___boxed(
    mut v_c_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2387_: u32 = 0;
    let mut v_a_boxed_2388_: u32 = 0;
    let mut v_res_2389_: u8 = 0;
    let mut v_r_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2387_ = crate::leanh::lean_unbox_uint32(v_c_2385_);
    crate::leanh::lean_dec(v_c_2385_);
    v_a_boxed_2388_ = crate::leanh::lean_unbox_uint32(v_a_2386_);
    crate::leanh::lean_dec(v_a_2386_);
    v_res_2389_ = l_Substring_Raw_contains___lam__0(v_c_boxed_2387_, v_a_boxed_2388_);
    v_r_2390_ = crate::leanh::lean_box((v_res_2389_) as usize);
    return v_r_2390_;
}
pub unsafe fn l_Substring_Raw_contains(
    mut v_s_2391_: *mut crate::leanh::LeanObject,
    mut v_c_2392_: u32,
) -> u8 {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: u8 = 0;
    let mut v_reuseFailAlloc_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2393_ = crate::leanh::lean_box_uint32(v_c_2392_);
                v___f_2394_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_contains___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2394_, 0, v___x_2393_);
                crate::leanh::lean_inc_ref(v___f_2394_);
                v___x_2395_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_2394_);
                v_str_2396_ = crate::leanh::lean_ctor_get(v_s_2391_, 0);
                v_startPos_2397_ = crate::leanh::lean_ctor_get(v_s_2391_, 1);
                v_stopPos_2398_ = crate::leanh::lean_ctor_get(v_s_2391_, 2);
                v_isSharedCheck_2416_ = (!crate::leanh::lean_is_exclusive(v_s_2391_)) as u8;
                if v_isSharedCheck_2416_ == 0 {
                    v___x_2400_ = v_s_2391_;
                    v_isShared_2401_ = v_isSharedCheck_2416_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2398_);
                    crate::leanh::lean_inc(v_startPos_2397_);
                    crate::leanh::lean_inc(v_str_2396_);
                    crate::leanh::lean_dec(v_s_2391_);
                    v___x_2400_ = crate::leanh::lean_box(0);
                    v_isShared_2401_ = v_isSharedCheck_2416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2402_ = l_String_instInhabitedSlice;
                v___f_2403_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_any___lam__0 as *mut core::ffi::c_void,
                    8,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2403_, 0, v___x_2395_);
                v___x_2404_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_2404_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2404_, 1, v___f_2394_);
                v___x_2409_ = lean_string_is_valid_pos(v_str_2396_, v_startPos_2397_);
                if v___x_2409_ == 0 {
                    crate::leanh::lean_del_object(v___x_2400_);
                    crate::leanh::lean_dec(v_stopPos_2398_);
                    crate::leanh::lean_dec(v_startPos_2397_);
                    crate::leanh::lean_dec_ref(v_str_2396_);
                    state = 2;
                    continue;
                } else {
                    v___x_2410_ = lean_string_is_valid_pos(v_str_2396_, v_stopPos_2398_);
                    if v___x_2410_ == 0 {
                        crate::leanh::lean_del_object(v___x_2400_);
                        crate::leanh::lean_dec(v_stopPos_2398_);
                        crate::leanh::lean_dec(v_startPos_2397_);
                        crate::leanh::lean_dec_ref(v_str_2396_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2411_ = lean_nat_dec_le(v_startPos_2397_, v_stopPos_2398_);
                        if v___x_2411_ == 0 {
                            crate::leanh::lean_del_object(v___x_2400_);
                            crate::leanh::lean_dec(v_stopPos_2398_);
                            crate::leanh::lean_dec(v_startPos_2397_);
                            crate::leanh::lean_dec_ref(v_str_2396_);
                            state = 2;
                            continue;
                        } else {
                            if v_isShared_2401_ == 0 {
                                v___x_2413_ = v___x_2400_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2415_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_str_2396_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2415_,
                                    1,
                                    v_startPos_2397_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2415_,
                                    2,
                                    v_stopPos_2398_,
                                );
                                v___x_2413_ = v_reuseFailAlloc_2415_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2406_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2407_ = l_panic___redArg(v___x_2402_, v___x_2406_);
                v___x_2408_ =
                    l_String_Slice_contains___redArg(v___f_2403_, v___x_2407_, v___x_2404_);
                return v___x_2408_;
            }
            3 => {
                v___x_2414_ =
                    l_String_Slice_contains___redArg(v___f_2403_, v___x_2413_, v___x_2404_);
                return v___x_2414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_contains___boxed(
    mut v_s_2417_: *mut crate::leanh::LeanObject,
    mut v_c_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2419_: u32 = 0;
    let mut v_res_2420_: u8 = 0;
    let mut v_r_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2419_ = crate::leanh::lean_unbox_uint32(v_c_2418_);
    crate::leanh::lean_dec(v_c_2418_);
    v_res_2420_ = l_Substring_Raw_contains(v_s_2417_, v_c_boxed_2419_);
    v_r_2421_ = crate::leanh::lean_box((v_res_2420_) as usize);
    return v_r_2421_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux(
    mut v_s_2422_: *mut crate::leanh::LeanObject,
    mut v_stopPos_2423_: *mut crate::leanh::LeanObject,
    mut v_p_2424_: *mut crate::leanh::LeanObject,
    mut v_i_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: u32 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ = lean_nat_dec_lt(v_i_2425_, v_stopPos_2423_);
                if v___x_2426_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_2424_);
                    return v_i_2425_;
                } else {
                    v___x_2427_ = lean_string_utf8_get(v_s_2422_, v_i_2425_);
                    v___x_2428_ = crate::leanh::lean_box_uint32(v___x_2427_);
                    crate::leanh::lean_inc_ref(v_p_2424_);
                    v___x_2429_ = crate::leanh::lean_apply_1(v_p_2424_, v___x_2428_);
                    v___x_2430_ = (crate::leanh::lean_unbox(v___x_2429_) as u8);
                    if v___x_2430_ == 0 {
                        crate::leanh::lean_dec_ref(v_p_2424_);
                        return v_i_2425_;
                    } else {
                        v___x_2431_ = lean_string_utf8_next(v_s_2422_, v_i_2425_);
                        crate::leanh::lean_dec(v_i_2425_);
                        v_i_2425_ = v___x_2431_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___boxed(
    mut v_s_2433_: *mut crate::leanh::LeanObject,
    mut v_stopPos_2434_: *mut crate::leanh::LeanObject,
    mut v_p_2435_: *mut crate::leanh::LeanObject,
    mut v_i_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Substring_Raw_takeWhileAux(v_s_2433_, v_stopPos_2434_, v_p_2435_, v_i_2436_);
    crate::leanh::lean_dec(v_stopPos_2434_);
    crate::leanh::lean_dec_ref(v_s_2433_);
    return v_res_2437_;
}
pub unsafe fn l_Substring_Raw_takeWhile(
    mut v_x_2438_: *mut crate::leanh::LeanObject,
    mut v_x_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v_e_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2440_ = crate::leanh::lean_ctor_get(v_x_2438_, 0);
                v_startPos_2441_ = crate::leanh::lean_ctor_get(v_x_2438_, 1);
                v_stopPos_2442_ = crate::leanh::lean_ctor_get(v_x_2438_, 2);
                v_isSharedCheck_2450_ = (!crate::leanh::lean_is_exclusive(v_x_2438_)) as u8;
                if v_isSharedCheck_2450_ == 0 {
                    v___x_2444_ = v_x_2438_;
                    v_isShared_2445_ = v_isSharedCheck_2450_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2442_);
                    crate::leanh::lean_inc(v_startPos_2441_);
                    crate::leanh::lean_inc(v_str_2440_);
                    crate::leanh::lean_dec(v_x_2438_);
                    v___x_2444_ = crate::leanh::lean_box(0);
                    v_isShared_2445_ = v_isSharedCheck_2450_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_startPos_2441_);
                v_e_2446_ = l_Substring_Raw_takeWhileAux(
                    v_str_2440_,
                    v_stopPos_2442_,
                    v_x_2439_,
                    v_startPos_2441_,
                );
                crate::leanh::lean_dec(v_stopPos_2442_);
                if v_isShared_2445_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2444_, 2, v_e_2446_);
                    v___x_2448_ = v___x_2444_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_str_2440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_startPos_2441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_e_2446_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_s_2452_: *mut crate::leanh::LeanObject,
    mut v_stopPos_2453_: *mut crate::leanh::LeanObject,
    mut v_i_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: u32 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2455_ = lean_nat_dec_lt(v_i_2454_, v_stopPos_2453_);
                if v___x_2455_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_2451_);
                    return v_i_2454_;
                } else {
                    v___x_2456_ = lean_string_utf8_get(v_s_2452_, v_i_2454_);
                    v___x_2457_ = crate::leanh::lean_box_uint32(v___x_2456_);
                    crate::leanh::lean_inc_ref(v_a_2451_);
                    v___x_2458_ = crate::leanh::lean_apply_1(v_a_2451_, v___x_2457_);
                    v___x_2459_ = (crate::leanh::lean_unbox(v___x_2458_) as u8);
                    if v___x_2459_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_2451_);
                        return v_i_2454_;
                    } else {
                        v___x_2460_ = lean_string_utf8_next(v_s_2452_, v_i_2454_);
                        crate::leanh::lean_dec(v_i_2454_);
                        v_i_2454_ = v___x_2460_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_s_2463_: *mut crate::leanh::LeanObject,
    mut v_stopPos_2464_: *mut crate::leanh::LeanObject,
    mut v_i_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ =
        l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(
            v_a_2462_,
            v_s_2463_,
            v_stopPos_2464_,
            v_i_2465_,
        );
    crate::leanh::lean_dec(v_stopPos_2464_);
    crate::leanh::lean_dec_ref(v_s_2463_);
    return v_res_2466_;
}
pub unsafe fn lean_substring_takewhile(
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v_e_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2469_ = crate::leanh::lean_ctor_get(v_a_2467_, 0);
                v_startPos_2470_ = crate::leanh::lean_ctor_get(v_a_2467_, 1);
                v_stopPos_2471_ = crate::leanh::lean_ctor_get(v_a_2467_, 2);
                v_isSharedCheck_2479_ = (!crate::leanh::lean_is_exclusive(v_a_2467_)) as u8;
                if v_isSharedCheck_2479_ == 0 {
                    v___x_2473_ = v_a_2467_;
                    v_isShared_2474_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2471_);
                    crate::leanh::lean_inc(v_startPos_2470_);
                    crate::leanh::lean_inc(v_str_2469_);
                    crate::leanh::lean_dec(v_a_2467_);
                    v___x_2473_ = crate::leanh::lean_box(0);
                    v_isShared_2474_ = v_isSharedCheck_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_startPos_2470_);
                v_e_2475_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_2468_, v_str_2469_, v_stopPos_2471_, v_startPos_2470_);
                crate::leanh::lean_dec(v_stopPos_2471_);
                if v_isShared_2474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2473_, 2, v_e_2475_);
                    v___x_2477_ = v___x_2473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_str_2469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_startPos_2470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_e_2475_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_dropWhile(
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v_x_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_b_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2482_ = crate::leanh::lean_ctor_get(v_x_2480_, 0);
                v_startPos_2483_ = crate::leanh::lean_ctor_get(v_x_2480_, 1);
                v_stopPos_2484_ = crate::leanh::lean_ctor_get(v_x_2480_, 2);
                v_isSharedCheck_2492_ = (!crate::leanh::lean_is_exclusive(v_x_2480_)) as u8;
                if v_isSharedCheck_2492_ == 0 {
                    v___x_2486_ = v_x_2480_;
                    v_isShared_2487_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2484_);
                    crate::leanh::lean_inc(v_startPos_2483_);
                    crate::leanh::lean_inc(v_str_2482_);
                    crate::leanh::lean_dec(v_x_2480_);
                    v___x_2486_ = crate::leanh::lean_box(0);
                    v_isShared_2487_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_b_2488_ = l_Substring_Raw_takeWhileAux(
                    v_str_2482_,
                    v_stopPos_2484_,
                    v_x_2481_,
                    v_startPos_2483_,
                );
                if v_isShared_2487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2486_, 1, v_b_2488_);
                    v___x_2490_ = v___x_2486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_str_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_b_2488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_stopPos_2484_);
                    v___x_2490_ = v_reuseFailAlloc_2491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeRightWhileAux(
    mut v_s_2493_: *mut crate::leanh::LeanObject,
    mut v_begPos_2494_: *mut crate::leanh::LeanObject,
    mut v_p_2495_: *mut crate::leanh::LeanObject,
    mut v_i_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: u8 = 0;
    let mut v_i_x27_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2499_: u32 = 0;
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2497_ = lean_nat_dec_lt(v_begPos_2494_, v_i_2496_);
                if v___x_2497_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_2495_);
                    return v_i_2496_;
                } else {
                    v_i_x27_2498_ = lean_string_utf8_prev(v_s_2493_, v_i_2496_);
                    v_c_2499_ = lean_string_utf8_get(v_s_2493_, v_i_x27_2498_);
                    v___x_2500_ = crate::leanh::lean_box_uint32(v_c_2499_);
                    crate::leanh::lean_inc_ref(v_p_2495_);
                    v___x_2501_ = crate::leanh::lean_apply_1(v_p_2495_, v___x_2500_);
                    v___x_2502_ = (crate::leanh::lean_unbox(v___x_2501_) as u8);
                    if v___x_2502_ == 0 {
                        crate::leanh::lean_dec(v_i_x27_2498_);
                        crate::leanh::lean_dec_ref(v_p_2495_);
                        return v_i_2496_;
                    } else {
                        crate::leanh::lean_dec(v_i_2496_);
                        v_i_2496_ = v_i_x27_2498_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeRightWhileAux___boxed(
    mut v_s_2504_: *mut crate::leanh::LeanObject,
    mut v_begPos_2505_: *mut crate::leanh::LeanObject,
    mut v_p_2506_: *mut crate::leanh::LeanObject,
    mut v_i_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ =
        l_Substring_Raw_takeRightWhileAux(v_s_2504_, v_begPos_2505_, v_p_2506_, v_i_2507_);
    crate::leanh::lean_dec(v_begPos_2505_);
    crate::leanh::lean_dec_ref(v_s_2504_);
    return v_res_2508_;
}
pub unsafe fn l_Substring_Raw_takeRightWhile(
    mut v_x_2509_: *mut crate::leanh::LeanObject,
    mut v_x_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_b_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2511_ = crate::leanh::lean_ctor_get(v_x_2509_, 0);
                v_startPos_2512_ = crate::leanh::lean_ctor_get(v_x_2509_, 1);
                v_stopPos_2513_ = crate::leanh::lean_ctor_get(v_x_2509_, 2);
                v_isSharedCheck_2521_ = (!crate::leanh::lean_is_exclusive(v_x_2509_)) as u8;
                if v_isSharedCheck_2521_ == 0 {
                    v___x_2515_ = v_x_2509_;
                    v_isShared_2516_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2513_);
                    crate::leanh::lean_inc(v_startPos_2512_);
                    crate::leanh::lean_inc(v_str_2511_);
                    crate::leanh::lean_dec(v_x_2509_);
                    v___x_2515_ = crate::leanh::lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_stopPos_2513_);
                v_b_2517_ = l_Substring_Raw_takeRightWhileAux(
                    v_str_2511_,
                    v_startPos_2512_,
                    v_x_2510_,
                    v_stopPos_2513_,
                );
                crate::leanh::lean_dec(v_startPos_2512_);
                if v_isShared_2516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2515_, 1, v_b_2517_);
                    v___x_2519_ = v___x_2515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_str_2511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_b_2517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_stopPos_2513_);
                    v___x_2519_ = v_reuseFailAlloc_2520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_dropRightWhile(
    mut v_x_2522_: *mut crate::leanh::LeanObject,
    mut v_x_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2529_: u8 = 0;
    let mut v_e_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2524_ = crate::leanh::lean_ctor_get(v_x_2522_, 0);
                v_startPos_2525_ = crate::leanh::lean_ctor_get(v_x_2522_, 1);
                v_stopPos_2526_ = crate::leanh::lean_ctor_get(v_x_2522_, 2);
                v_isSharedCheck_2534_ = (!crate::leanh::lean_is_exclusive(v_x_2522_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v___x_2528_ = v_x_2522_;
                    v_isShared_2529_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2526_);
                    crate::leanh::lean_inc(v_startPos_2525_);
                    crate::leanh::lean_inc(v_str_2524_);
                    crate::leanh::lean_dec(v_x_2522_);
                    v___x_2528_ = crate::leanh::lean_box(0);
                    v_isShared_2529_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_e_2530_ = l_Substring_Raw_takeRightWhileAux(
                    v_str_2524_,
                    v_startPos_2525_,
                    v_x_2523_,
                    v_stopPos_2526_,
                );
                if v_isShared_2529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2528_, 2, v_e_2530_);
                    v___x_2532_ = v___x_2528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_str_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_startPos_2525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_e_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_trimLeft(
    mut v_s_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2537_ = crate::leanh::lean_ctor_get(v_s_2536_, 0);
                v_startPos_2538_ = crate::leanh::lean_ctor_get(v_s_2536_, 1);
                v_stopPos_2539_ = crate::leanh::lean_ctor_get(v_s_2536_, 2);
                v_isSharedCheck_2548_ = (!crate::leanh::lean_is_exclusive(v_s_2536_)) as u8;
                if v_isSharedCheck_2548_ == 0 {
                    v___x_2541_ = v_s_2536_;
                    v_isShared_2542_ = v_isSharedCheck_2548_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2539_);
                    crate::leanh::lean_inc(v_startPos_2538_);
                    crate::leanh::lean_inc(v_str_2537_);
                    crate::leanh::lean_dec(v_s_2536_);
                    v___x_2541_ = crate::leanh::lean_box(0);
                    v_isShared_2542_ = v_isSharedCheck_2548_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2543_ = l_Substring_Raw_trimLeft___closed__0;
                v_b_2544_ = l_Substring_Raw_takeWhileAux(
                    v_str_2537_,
                    v_stopPos_2539_,
                    v___x_2543_,
                    v_startPos_2538_,
                );
                if v_isShared_2542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2541_, 1, v_b_2544_);
                    v___x_2546_ = v___x_2541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2547_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_str_2537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_b_2544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_stopPos_2539_);
                    v___x_2546_ = v_reuseFailAlloc_2547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_trimRight(
    mut v_s_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2550_ = crate::leanh::lean_ctor_get(v_s_2549_, 0);
                v_startPos_2551_ = crate::leanh::lean_ctor_get(v_s_2549_, 1);
                v_stopPos_2552_ = crate::leanh::lean_ctor_get(v_s_2549_, 2);
                v_isSharedCheck_2561_ = (!crate::leanh::lean_is_exclusive(v_s_2549_)) as u8;
                if v_isSharedCheck_2561_ == 0 {
                    v___x_2554_ = v_s_2549_;
                    v_isShared_2555_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2552_);
                    crate::leanh::lean_inc(v_startPos_2551_);
                    crate::leanh::lean_inc(v_str_2550_);
                    crate::leanh::lean_dec(v_s_2549_);
                    v___x_2554_ = crate::leanh::lean_box(0);
                    v_isShared_2555_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2556_ = l_Substring_Raw_trimLeft___closed__0;
                v_e_2557_ = l_Substring_Raw_takeRightWhileAux(
                    v_str_2550_,
                    v_startPos_2551_,
                    v___x_2556_,
                    v_stopPos_2552_,
                );
                if v_isShared_2555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2554_, 2, v_e_2557_);
                    v___x_2559_ = v___x_2554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_str_2550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_startPos_2551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_e_2557_);
                    v___x_2559_ = v_reuseFailAlloc_2560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_trim(
    mut v_x_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2568_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2563_ = crate::leanh::lean_ctor_get(v_x_2562_, 0);
                v_startPos_2564_ = crate::leanh::lean_ctor_get(v_x_2562_, 1);
                v_stopPos_2565_ = crate::leanh::lean_ctor_get(v_x_2562_, 2);
                v_isSharedCheck_2575_ = (!crate::leanh::lean_is_exclusive(v_x_2562_)) as u8;
                if v_isSharedCheck_2575_ == 0 {
                    v___x_2567_ = v_x_2562_;
                    v_isShared_2568_ = v_isSharedCheck_2575_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2565_);
                    crate::leanh::lean_inc(v_startPos_2564_);
                    crate::leanh::lean_inc(v_str_2563_);
                    crate::leanh::lean_dec(v_x_2562_);
                    v___x_2567_ = crate::leanh::lean_box(0);
                    v_isShared_2568_ = v_isSharedCheck_2575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2569_ = l_Substring_Raw_trimLeft___closed__0;
                v_b_2570_ = l_Substring_Raw_takeWhileAux(
                    v_str_2563_,
                    v_stopPos_2565_,
                    v___x_2569_,
                    v_startPos_2564_,
                );
                v_e_2571_ = l_Substring_Raw_takeRightWhileAux(
                    v_str_2563_,
                    v_b_2570_,
                    v___x_2569_,
                    v_stopPos_2565_,
                );
                if v_isShared_2568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2567_, 2, v_e_2571_);
                    crate::leanh::lean_ctor_set(v___x_2567_, 1, v_b_2570_);
                    v___x_2573_ = v___x_2567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_str_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_b_2570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_e_2571_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_isNat___lam__0(
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___x_2577_: u8,
    mut v___x_2578_: u8,
    mut v_it_2579_: *mut crate::leanh::LeanObject,
    mut v_acc_2580_: *mut crate::leanh::LeanObject,
    mut v_hP_2581_: *mut crate::leanh::LeanObject,
    mut v_recur_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u8 = 0;
    let mut v_snd_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v_fst_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v_snd_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: u32 = 0;
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: u8 = 0;
    let mut v___y_2608_: u8 = 0;
    let mut v___x_2609_: u32 = 0;
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: u8 = 0;
    let mut v___y_2627_: u8 = 0;
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: u32 = 0;
    let mut v___x_2630_: u8 = 0;
    let mut v___y_2632_: u8 = 0;
    let mut v___y_2633_: u8 = 0;
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: u32 = 0;
    let mut v___x_2636_: u8 = 0;
    let mut v___y_2638_: u8 = 0;
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: u32 = 0;
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: u32 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: u32 = 0;
    let mut v___x_2646_: u8 = 0;
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v_unused_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2649_: u8 = 0;
    let mut v_unused_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut v_unused_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2583_ = crate::leanh::lean_ctor_get(v___y_2576_, 0);
                v_startInclusive_2584_ = crate::leanh::lean_ctor_get(v___y_2576_, 1);
                v_endExclusive_2585_ = crate::leanh::lean_ctor_get(v___y_2576_, 2);
                v___x_2586_ = lean_nat_sub(v_endExclusive_2585_, v_startInclusive_2584_);
                v___x_2587_ = lean_nat_dec_eq(v_it_2579_, v___x_2586_);
                crate::leanh::lean_dec(v___x_2586_);
                if v___x_2587_ == 0 {
                    v_snd_2588_ = crate::leanh::lean_ctor_get(v_acc_2580_, 1);
                    crate::leanh::lean_inc(v_snd_2588_);
                    v_snd_2589_ = crate::leanh::lean_ctor_get(v_snd_2588_, 1);
                    crate::leanh::lean_inc(v_snd_2589_);
                    v_fst_2590_ = crate::leanh::lean_ctor_get(v_acc_2580_, 0);
                    v_isSharedCheck_2651_ = (!crate::leanh::lean_is_exclusive(v_acc_2580_)) as u8;
                    if v_isSharedCheck_2651_ == 0 {
                        v_unused_2652_ = crate::leanh::lean_ctor_get(v_acc_2580_, 1);
                        crate::leanh::lean_dec(v_unused_2652_);
                        v___x_2592_ = v_acc_2580_;
                        v_isShared_2593_ = v_isSharedCheck_2651_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2590_);
                        crate::leanh::lean_dec(v_acc_2580_);
                        v___x_2592_ = crate::leanh::lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2651_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recur_2582_);
                    return v_acc_2580_;
                }
            }
            1 => {
                v_fst_2594_ = crate::leanh::lean_ctor_get(v_snd_2588_, 0);
                v_isSharedCheck_2649_ = (!crate::leanh::lean_is_exclusive(v_snd_2588_)) as u8;
                if v_isSharedCheck_2649_ == 0 {
                    v_unused_2650_ = crate::leanh::lean_ctor_get(v_snd_2588_, 1);
                    crate::leanh::lean_dec(v_unused_2650_);
                    v___x_2596_ = v_snd_2588_;
                    v_isShared_2597_ = v_isSharedCheck_2649_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2594_);
                    crate::leanh::lean_dec(v_snd_2588_);
                    v___x_2596_ = crate::leanh::lean_box(0);
                    v_isShared_2597_ = v_isSharedCheck_2649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_2598_ = crate::leanh::lean_ctor_get(v_snd_2589_, 1);
                v_isSharedCheck_2647_ = (!crate::leanh::lean_is_exclusive(v_snd_2589_)) as u8;
                if v_isSharedCheck_2647_ == 0 {
                    v_unused_2648_ = crate::leanh::lean_ctor_get(v_snd_2589_, 0);
                    crate::leanh::lean_dec(v_unused_2648_);
                    v___x_2600_ = v_snd_2589_;
                    v_isShared_2601_ = v_isSharedCheck_2647_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2598_);
                    crate::leanh::lean_dec(v_snd_2589_);
                    v___x_2600_ = crate::leanh::lean_box(0);
                    v_isShared_2601_ = v_isSharedCheck_2647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2602_ = lean_nat_add(v_startInclusive_2584_, v_it_2579_);
                v___x_2603_ = lean_string_utf8_get_fast(v_str_2583_, v___x_2602_);
                v___x_2604_ = lean_string_utf8_next_fast(v_str_2583_, v___x_2602_);
                crate::leanh::lean_dec(v___x_2602_);
                v___x_2605_ = lean_nat_sub(v___x_2604_, v_startInclusive_2584_);
                v___x_2643_ = 48;
                v___x_2644_ = lean_uint32_dec_le(v___x_2643_, v___x_2603_);
                if v___x_2644_ == 0 {
                    v___y_2638_ = v___x_2644_;
                    state = 10;
                    continue;
                } else {
                    v___x_2645_ = 57;
                    v___x_2646_ = lean_uint32_dec_le(v___x_2603_, v___x_2645_);
                    v___y_2638_ = v___x_2646_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                v___x_2609_ = 95;
                v___x_2610_ = lean_uint32_dec_eq(v___x_2603_, v___x_2609_);
                v___x_2611_ = crate::leanh::lean_box((v___y_2607_) as usize);
                v___x_2612_ = crate::leanh::lean_box((v___y_2608_) as usize);
                if v_isShared_2601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2600_, 1, v___x_2612_);
                    crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2611_);
                    v___x_2614_ = v___x_2600_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2612_);
                    v___x_2614_ = v_reuseFailAlloc_2624_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2615_ = crate::leanh::lean_box((v___x_2610_) as usize);
                if v_isShared_2597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2596_, 1, v___x_2614_);
                    crate::leanh::lean_ctor_set(v___x_2596_, 0, v___x_2615_);
                    v___x_2617_ = v___x_2596_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2614_);
                    v___x_2617_ = v_reuseFailAlloc_2623_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2618_ = crate::leanh::lean_box((v___x_2577_) as usize);
                if v_isShared_2593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2592_, 1, v___x_2617_);
                    crate::leanh::lean_ctor_set(v___x_2592_, 0, v___x_2618_);
                    v___x_2620_ = v___x_2592_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2617_);
                    v___x_2620_ = v_reuseFailAlloc_2622_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2621_ = crate::leanh::lean_apply_4(
                    v_recur_2582_,
                    v___x_2605_,
                    v___x_2620_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_2621_;
            }
            8 => {
                v___x_2628_ = (crate::leanh::lean_unbox(v_fst_2594_) as u8);
                crate::leanh::lean_dec(v_fst_2594_);
                if v___x_2628_ == 0 {
                    v___y_2607_ = v___y_2626_;
                    v___y_2608_ = v___y_2627_;
                    state = 4;
                    continue;
                } else {
                    v___x_2629_ = 95;
                    v___x_2630_ = lean_uint32_dec_eq(v___x_2603_, v___x_2629_);
                    if v___x_2630_ == 0 {
                        v___y_2607_ = v___y_2626_;
                        v___y_2608_ = v___y_2627_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2607_ = v___y_2626_;
                        v___y_2608_ = v___x_2577_;
                        state = 4;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2634_ = (crate::leanh::lean_unbox(v_fst_2590_) as u8);
                crate::leanh::lean_dec(v_fst_2590_);
                if v___x_2634_ == 0 {
                    v___y_2626_ = v___y_2632_;
                    v___y_2627_ = v___y_2633_;
                    state = 8;
                    continue;
                } else {
                    v___x_2635_ = 95;
                    v___x_2636_ = lean_uint32_dec_eq(v___x_2603_, v___x_2635_);
                    if v___x_2636_ == 0 {
                        v___y_2626_ = v___y_2632_;
                        v___y_2627_ = v___y_2633_;
                        state = 8;
                        continue;
                    } else {
                        if v___x_2577_ == 0 {
                            crate::leanh::lean_dec(v_fst_2594_);
                            v___y_2607_ = v___y_2632_;
                            v___y_2608_ = v___x_2577_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2626_ = v___y_2632_;
                            v___y_2627_ = v___x_2577_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            10 => {
                v___x_2639_ = (crate::leanh::lean_unbox(v_snd_2598_) as u8);
                if v___x_2639_ == 0 {
                    crate::leanh::lean_dec(v_fst_2594_);
                    crate::leanh::lean_dec(v_fst_2590_);
                    v___x_2640_ = (crate::leanh::lean_unbox(v_snd_2598_) as u8);
                    crate::leanh::lean_dec(v_snd_2598_);
                    v___y_2607_ = v___y_2638_;
                    v___y_2608_ = v___x_2640_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2598_);
                    if v___y_2638_ == 0 {
                        v___x_2641_ = 95;
                        v___x_2642_ = lean_uint32_dec_eq(v___x_2603_, v___x_2641_);
                        if v___x_2642_ == 0 {
                            crate::leanh::lean_dec(v_fst_2594_);
                            crate::leanh::lean_dec(v_fst_2590_);
                            v___y_2607_ = v___y_2638_;
                            v___y_2608_ = v___x_2642_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2632_ = v___y_2638_;
                            v___y_2633_ = v___x_2642_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_2632_ = v___y_2638_;
                        v___y_2633_ = v___x_2578_;
                        state = 9;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_isNat___lam__0___boxed(
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___x_2654_: *mut crate::leanh::LeanObject,
    mut v___x_2655_: *mut crate::leanh::LeanObject,
    mut v_it_2656_: *mut crate::leanh::LeanObject,
    mut v_acc_2657_: *mut crate::leanh::LeanObject,
    mut v_hP_2658_: *mut crate::leanh::LeanObject,
    mut v_recur_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1077__boxed_2660_: u8 = 0;
    let mut v___x_1078__boxed_2661_: u8 = 0;
    let mut v_res_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1077__boxed_2660_ = (crate::leanh::lean_unbox(v___x_2654_) as u8);
    v___x_1078__boxed_2661_ = (crate::leanh::lean_unbox(v___x_2655_) as u8);
    v_res_2662_ = l_Substring_Raw_isNat___lam__0(
        v___y_2653_,
        v___x_1077__boxed_2660_,
        v___x_1078__boxed_2661_,
        v_it_2656_,
        v_acc_2657_,
        v_hP_2658_,
        v_recur_2659_,
    );
    crate::leanh::lean_dec(v_it_2656_);
    crate::leanh::lean_dec_ref(v___y_2653_);
    return v_res_2662_;
}
pub unsafe fn l_Substring_Raw_isNat(mut v_s_2663_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_str_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v_fst_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: u8 = 0;
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2664_ = crate::leanh::lean_ctor_get(v_s_2663_, 0);
                v_startPos_2665_ = crate::leanh::lean_ctor_get(v_s_2663_, 1);
                v_stopPos_2666_ = crate::leanh::lean_ctor_get(v_s_2663_, 2);
                v_isSharedCheck_2705_ = (!crate::leanh::lean_is_exclusive(v_s_2663_)) as u8;
                if v_isSharedCheck_2705_ == 0 {
                    v___x_2668_ = v_s_2663_;
                    v_isShared_2669_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2666_);
                    crate::leanh::lean_inc(v_startPos_2665_);
                    crate::leanh::lean_inc(v_str_2664_);
                    crate::leanh::lean_dec(v_s_2663_);
                    v___x_2668_ = crate::leanh::lean_box(0);
                    v_isShared_2669_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2670_ = lean_nat_sub(v_stopPos_2666_, v_startPos_2665_);
                v___x_2671_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2672_ = lean_nat_dec_eq(v___x_2670_, v___x_2671_);
                crate::leanh::lean_dec(v___x_2670_);
                if v___x_2672_ == 0 {
                    v___x_2673_ = 1;
                    v___x_2674_ = crate::leanh::lean_box((v___x_2672_) as usize);
                    v___x_2675_ = crate::leanh::lean_box((v___x_2673_) as usize);
                    v___x_2676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
                    crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
                    v___x_2677_ = crate::leanh::lean_box((v___x_2672_) as usize);
                    v___x_2678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2678_, 0, v___x_2677_);
                    crate::leanh::lean_ctor_set(v___x_2678_, 1, v___x_2676_);
                    v___x_2679_ = crate::leanh::lean_box((v___x_2673_) as usize);
                    v___x_2680_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2680_, 0, v___x_2679_);
                    crate::leanh::lean_ctor_set(v___x_2680_, 1, v___x_2678_);
                    v___x_2694_ = l_String_instInhabitedSlice;
                    v___x_2698_ = lean_string_is_valid_pos(v_str_2664_, v_startPos_2665_);
                    if v___x_2698_ == 0 {
                        crate::leanh::lean_del_object(v___x_2668_);
                        crate::leanh::lean_dec(v_stopPos_2666_);
                        crate::leanh::lean_dec(v_startPos_2665_);
                        crate::leanh::lean_dec_ref(v_str_2664_);
                        state = 3;
                        continue;
                    } else {
                        v___x_2699_ = lean_string_is_valid_pos(v_str_2664_, v_stopPos_2666_);
                        if v___x_2699_ == 0 {
                            crate::leanh::lean_del_object(v___x_2668_);
                            crate::leanh::lean_dec(v_stopPos_2666_);
                            crate::leanh::lean_dec(v_startPos_2665_);
                            crate::leanh::lean_dec_ref(v_str_2664_);
                            state = 3;
                            continue;
                        } else {
                            v___x_2700_ = lean_nat_dec_le(v_startPos_2665_, v_stopPos_2666_);
                            if v___x_2700_ == 0 {
                                crate::leanh::lean_del_object(v___x_2668_);
                                crate::leanh::lean_dec(v_stopPos_2666_);
                                crate::leanh::lean_dec(v_startPos_2665_);
                                crate::leanh::lean_dec_ref(v_str_2664_);
                                state = 3;
                                continue;
                            } else {
                                if v_isShared_2669_ == 0 {
                                    v___x_2702_ = v___x_2668_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2703_ =
                                        crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2703_,
                                        0,
                                        v_str_2664_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2703_,
                                        1,
                                        v_startPos_2665_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2703_,
                                        2,
                                        v_stopPos_2666_,
                                    );
                                    v___x_2702_ = v_reuseFailAlloc_2703_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2668_);
                    crate::leanh::lean_dec(v_stopPos_2666_);
                    crate::leanh::lean_dec(v_startPos_2665_);
                    crate::leanh::lean_dec_ref(v_str_2664_);
                    v___x_2704_ = 0;
                    return v___x_2704_;
                }
            }
            2 => {
                v___x_2683_ = crate::leanh::lean_box((v___x_2672_) as usize);
                v___x_2684_ = crate::leanh::lean_box((v___x_2673_) as usize);
                crate::leanh::lean_inc_ref(v___y_2682_);
                v___f_2685_ = crate::leanh::lean_alloc_closure(
                    l_Substring_Raw_isNat___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2685_, 0, v___y_2682_);
                crate::leanh::lean_closure_set(v___f_2685_, 1, v___x_2683_);
                crate::leanh::lean_closure_set(v___f_2685_, 2, v___x_2684_);
                v___x_2686_ = l_String_Slice_positions(v___y_2682_);
                crate::leanh::lean_dec_ref(v___y_2682_);
                v___x_2687_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2685_,
                    v___x_2686_,
                    v___x_2680_,
                    crate::leanh::lean_box(0),
                );
                v_snd_2688_ = crate::leanh::lean_ctor_get(v___x_2687_, 1);
                crate::leanh::lean_inc(v_snd_2688_);
                crate::leanh::lean_dec(v___x_2687_);
                v_snd_2689_ = crate::leanh::lean_ctor_get(v_snd_2688_, 1);
                crate::leanh::lean_inc(v_snd_2689_);
                crate::leanh::lean_dec(v_snd_2688_);
                v_snd_2690_ = crate::leanh::lean_ctor_get(v_snd_2689_, 1);
                v___x_2691_ = (crate::leanh::lean_unbox(v_snd_2690_) as u8);
                if v___x_2691_ == 0 {
                    crate::leanh::lean_dec(v_snd_2689_);
                    return v___x_2672_;
                } else {
                    v_fst_2692_ = crate::leanh::lean_ctor_get(v_snd_2689_, 0);
                    crate::leanh::lean_inc(v_fst_2692_);
                    crate::leanh::lean_dec(v_snd_2689_);
                    v___x_2693_ = (crate::leanh::lean_unbox(v_fst_2692_) as u8);
                    crate::leanh::lean_dec(v_fst_2692_);
                    return v___x_2693_;
                }
            }
            3 => {
                v___x_2696_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2697_ = l_panic___redArg(v___x_2694_, v___x_2696_);
                v___y_2682_ = v___x_2697_;
                state = 2;
                continue;
            }
            4 => {
                v___y_2682_ = v___x_2702_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_isNat___boxed(
    mut v_s_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2707_: u8 = 0;
    let mut v_r_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_Substring_Raw_isNat(v_s_2706_);
    v_r_2708_ = crate::leanh::lean_box((v_res_2707_) as usize);
    return v_r_2708_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(
    mut v___x_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_b_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v_snd_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v_fst_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v_snd_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2731_: u8 = 0;
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: u8 = 0;
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: u32 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: u8 = 0;
    let mut v___y_2741_: u8 = 0;
    let mut v___x_2742_: u32 = 0;
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: u8 = 0;
    let mut v___y_2760_: u8 = 0;
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: u32 = 0;
    let mut v___x_2763_: u8 = 0;
    let mut v___y_2765_: u8 = 0;
    let mut v___y_2766_: u8 = 0;
    let mut v___x_2767_: u8 = 0;
    let mut v___x_2768_: u32 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___y_2771_: u8 = 0;
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2774_: u32 = 0;
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2776_: u32 = 0;
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2778_: u32 = 0;
    let mut v___x_2779_: u8 = 0;
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_unused_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_unused_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_unused_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2713_ = crate::leanh::lean_ctor_get(v___y_2710_, 0);
                v_startInclusive_2714_ = crate::leanh::lean_ctor_get(v___y_2710_, 1);
                v_endExclusive_2715_ = crate::leanh::lean_ctor_get(v___y_2710_, 2);
                v___x_2716_ = lean_nat_sub(v_endExclusive_2715_, v_startInclusive_2714_);
                v___x_2717_ = lean_nat_dec_eq(v_a_2711_, v___x_2716_);
                crate::leanh::lean_dec(v___x_2716_);
                if v___x_2717_ == 0 {
                    v_snd_2718_ = crate::leanh::lean_ctor_get(v_b_2712_, 1);
                    crate::leanh::lean_inc(v_snd_2718_);
                    v_snd_2719_ = crate::leanh::lean_ctor_get(v_snd_2718_, 1);
                    crate::leanh::lean_inc(v_snd_2719_);
                    v_fst_2720_ = crate::leanh::lean_ctor_get(v_b_2712_, 0);
                    v_isSharedCheck_2784_ = (!crate::leanh::lean_is_exclusive(v_b_2712_)) as u8;
                    if v_isSharedCheck_2784_ == 0 {
                        v_unused_2785_ = crate::leanh::lean_ctor_get(v_b_2712_, 1);
                        crate::leanh::lean_dec(v_unused_2785_);
                        v___x_2722_ = v_b_2712_;
                        v_isShared_2723_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2720_);
                        crate::leanh::lean_dec(v_b_2712_);
                        v___x_2722_ = crate::leanh::lean_box(0);
                        v_isShared_2723_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2711_);
                    return v_b_2712_;
                }
            }
            1 => {
                v_fst_2724_ = crate::leanh::lean_ctor_get(v_snd_2718_, 0);
                v_isSharedCheck_2782_ = (!crate::leanh::lean_is_exclusive(v_snd_2718_)) as u8;
                if v_isSharedCheck_2782_ == 0 {
                    v_unused_2783_ = crate::leanh::lean_ctor_get(v_snd_2718_, 1);
                    crate::leanh::lean_dec(v_unused_2783_);
                    v___x_2726_ = v_snd_2718_;
                    v_isShared_2727_ = v_isSharedCheck_2782_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2724_);
                    crate::leanh::lean_dec(v_snd_2718_);
                    v___x_2726_ = crate::leanh::lean_box(0);
                    v_isShared_2727_ = v_isSharedCheck_2782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_2728_ = crate::leanh::lean_ctor_get(v_snd_2719_, 1);
                v_isSharedCheck_2780_ = (!crate::leanh::lean_is_exclusive(v_snd_2719_)) as u8;
                if v_isSharedCheck_2780_ == 0 {
                    v_unused_2781_ = crate::leanh::lean_ctor_get(v_snd_2719_, 0);
                    crate::leanh::lean_dec(v_unused_2781_);
                    v___x_2730_ = v_snd_2719_;
                    v_isShared_2731_ = v_isSharedCheck_2780_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2728_);
                    crate::leanh::lean_dec(v_snd_2719_);
                    v___x_2730_ = crate::leanh::lean_box(0);
                    v_isShared_2731_ = v_isSharedCheck_2780_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2732_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2733_ = lean_nat_dec_eq(v___x_2709_, v___x_2732_);
                v___x_2734_ = 1;
                v___x_2735_ = lean_nat_add(v_startInclusive_2714_, v_a_2711_);
                crate::leanh::lean_dec(v_a_2711_);
                v___x_2736_ = lean_string_utf8_get_fast(v_str_2713_, v___x_2735_);
                v___x_2737_ = lean_string_utf8_next_fast(v_str_2713_, v___x_2735_);
                crate::leanh::lean_dec(v___x_2735_);
                v___x_2738_ = lean_nat_sub(v___x_2737_, v_startInclusive_2714_);
                v___x_2776_ = 48;
                v___x_2777_ = lean_uint32_dec_le(v___x_2776_, v___x_2736_);
                if v___x_2777_ == 0 {
                    v___y_2771_ = v___x_2777_;
                    state = 10;
                    continue;
                } else {
                    v___x_2778_ = 57;
                    v___x_2779_ = lean_uint32_dec_le(v___x_2736_, v___x_2778_);
                    v___y_2771_ = v___x_2779_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                v___x_2742_ = 95;
                v___x_2743_ = lean_uint32_dec_eq(v___x_2736_, v___x_2742_);
                v___x_2744_ = crate::leanh::lean_box((v___y_2740_) as usize);
                v___x_2745_ = crate::leanh::lean_box((v___y_2741_) as usize);
                if v_isShared_2731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2730_, 1, v___x_2745_);
                    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2744_);
                    v___x_2747_ = v___x_2730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2757_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2748_ = crate::leanh::lean_box((v___x_2743_) as usize);
                if v_isShared_2727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2726_, 1, v___x_2747_);
                    crate::leanh::lean_ctor_set(v___x_2726_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2726_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2747_);
                    v___x_2750_ = v_reuseFailAlloc_2756_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2751_ = crate::leanh::lean_box((v___x_2733_) as usize);
                if v_isShared_2723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2722_, 1, v___x_2750_);
                    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2751_);
                    v___x_2753_ = v___x_2722_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2750_);
                    v___x_2753_ = v_reuseFailAlloc_2755_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_2711_ = v___x_2738_;
                v_b_2712_ = v___x_2753_;
                state = 0;
                continue;
            }
            8 => {
                v___x_2761_ = (crate::leanh::lean_unbox(v_fst_2724_) as u8);
                crate::leanh::lean_dec(v_fst_2724_);
                if v___x_2761_ == 0 {
                    v___y_2740_ = v___y_2759_;
                    v___y_2741_ = v___y_2760_;
                    state = 4;
                    continue;
                } else {
                    v___x_2762_ = 95;
                    v___x_2763_ = lean_uint32_dec_eq(v___x_2736_, v___x_2762_);
                    if v___x_2763_ == 0 {
                        v___y_2740_ = v___y_2759_;
                        v___y_2741_ = v___y_2760_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2740_ = v___y_2759_;
                        v___y_2741_ = v___x_2733_;
                        state = 4;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2767_ = (crate::leanh::lean_unbox(v_fst_2720_) as u8);
                crate::leanh::lean_dec(v_fst_2720_);
                if v___x_2767_ == 0 {
                    v___y_2759_ = v___y_2765_;
                    v___y_2760_ = v___y_2766_;
                    state = 8;
                    continue;
                } else {
                    v___x_2768_ = 95;
                    v___x_2769_ = lean_uint32_dec_eq(v___x_2736_, v___x_2768_);
                    if v___x_2769_ == 0 {
                        v___y_2759_ = v___y_2765_;
                        v___y_2760_ = v___y_2766_;
                        state = 8;
                        continue;
                    } else {
                        if v___x_2733_ == 0 {
                            crate::leanh::lean_dec(v_fst_2724_);
                            v___y_2740_ = v___y_2765_;
                            v___y_2741_ = v___x_2733_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2759_ = v___y_2765_;
                            v___y_2760_ = v___x_2733_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            10 => {
                v___x_2772_ = (crate::leanh::lean_unbox(v_snd_2728_) as u8);
                if v___x_2772_ == 0 {
                    crate::leanh::lean_dec(v_fst_2724_);
                    crate::leanh::lean_dec(v_fst_2720_);
                    v___x_2773_ = (crate::leanh::lean_unbox(v_snd_2728_) as u8);
                    crate::leanh::lean_dec(v_snd_2728_);
                    v___y_2740_ = v___y_2771_;
                    v___y_2741_ = v___x_2773_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2728_);
                    if v___y_2771_ == 0 {
                        v___x_2774_ = 95;
                        v___x_2775_ = lean_uint32_dec_eq(v___x_2736_, v___x_2774_);
                        if v___x_2775_ == 0 {
                            crate::leanh::lean_dec(v_fst_2724_);
                            crate::leanh::lean_dec(v_fst_2720_);
                            v___y_2740_ = v___y_2771_;
                            v___y_2741_ = v___x_2775_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2765_ = v___y_2771_;
                            v___y_2766_ = v___x_2775_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_2765_ = v___y_2771_;
                        v___y_2766_ = v___x_2734_;
                        state = 9;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(
    mut v___x_2786_: *mut crate::leanh::LeanObject,
    mut v___y_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_b_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2790_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(
        v___x_2786_,
        v___y_2787_,
        v_a_2788_,
        v_b_2789_,
    );
    crate::leanh::lean_dec_ref(v___y_2787_);
    crate::leanh::lean_dec(v___x_2786_);
    return v_res_2790_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(
    mut v___y_2791_: *mut crate::leanh::LeanObject,
    mut v_a_2792_: *mut crate::leanh::LeanObject,
    mut v_b_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u32 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u32 = 0;
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2794_ = crate::leanh::lean_ctor_get(v___y_2791_, 0);
                v_startInclusive_2795_ = crate::leanh::lean_ctor_get(v___y_2791_, 1);
                v_endExclusive_2796_ = crate::leanh::lean_ctor_get(v___y_2791_, 2);
                v___x_2797_ = lean_nat_sub(v_endExclusive_2796_, v_startInclusive_2795_);
                v___x_2798_ = lean_nat_dec_eq(v_a_2792_, v___x_2797_);
                crate::leanh::lean_dec(v___x_2797_);
                if v___x_2798_ == 0 {
                    v___x_2799_ = lean_nat_add(v_startInclusive_2795_, v_a_2792_);
                    crate::leanh::lean_dec(v_a_2792_);
                    v___x_2800_ = lean_string_utf8_get_fast(v_str_2794_, v___x_2799_);
                    v___x_2801_ = lean_string_utf8_next_fast(v_str_2794_, v___x_2799_);
                    crate::leanh::lean_dec(v___x_2799_);
                    v___x_2802_ = lean_nat_sub(v___x_2801_, v_startInclusive_2795_);
                    v___x_2803_ = 95;
                    v___x_2804_ = lean_uint32_dec_eq(v___x_2800_, v___x_2803_);
                    if v___x_2804_ == 0 {
                        v___x_2805_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_2806_ = lean_nat_mul(v_b_2793_, v___x_2805_);
                        crate::leanh::lean_dec(v_b_2793_);
                        v___x_2807_ = lean_uint32_to_nat(v___x_2800_);
                        v___x_2808_ = crate::leanh::lean_unsigned_to_nat(48);
                        v___x_2809_ = lean_nat_sub(v___x_2807_, v___x_2808_);
                        crate::leanh::lean_dec(v___x_2807_);
                        v___x_2810_ = lean_nat_add(v___x_2806_, v___x_2809_);
                        crate::leanh::lean_dec(v___x_2809_);
                        crate::leanh::lean_dec(v___x_2806_);
                        v_a_2792_ = v___x_2802_;
                        v_b_2793_ = v___x_2810_;
                        state = 0;
                        continue;
                    } else {
                        v_a_2792_ = v___x_2802_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2792_);
                    return v_b_2793_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(
    mut v___y_2813_: *mut crate::leanh::LeanObject,
    mut v_a_2814_: *mut crate::leanh::LeanObject,
    mut v_b_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2816_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(
        v___y_2813_,
        v_a_2814_,
        v_b_2815_,
    );
    crate::leanh::lean_dec_ref(v___y_2813_);
    return v_res_2816_;
}
pub unsafe fn l_Substring_Raw_toNat_x3f(
    mut v_s_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v___y_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v_fst_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: u8 = 0;
    let mut v___x_2870_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2828_ = crate::leanh::lean_ctor_get(v_s_2817_, 0);
                v_startPos_2829_ = crate::leanh::lean_ctor_get(v_s_2817_, 1);
                v_stopPos_2830_ = crate::leanh::lean_ctor_get(v_s_2817_, 2);
                v_isSharedCheck_2873_ = (!crate::leanh::lean_is_exclusive(v_s_2817_)) as u8;
                if v_isSharedCheck_2873_ == 0 {
                    v___x_2832_ = v_s_2817_;
                    v_isShared_2833_ = v_isSharedCheck_2873_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2830_);
                    crate::leanh::lean_inc(v_startPos_2829_);
                    crate::leanh::lean_inc(v_str_2828_);
                    crate::leanh::lean_dec(v_s_2817_);
                    v___x_2832_ = crate::leanh::lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_2873_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_2821_ = l_String_Slice_positions(v___y_2820_);
                v___x_2822_ =
                    l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(
                        v___y_2820_,
                        v___x_2821_,
                        v___y_2819_,
                    );
                crate::leanh::lean_dec_ref(v___y_2820_);
                v___x_2823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2822_);
                return v___x_2823_;
            }
            2 => {
                v___x_2826_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2827_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_2826_);
                v___y_2819_ = v___y_2825_;
                v___y_2820_ = v___x_2827_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2844_ = lean_nat_sub(v_stopPos_2830_, v_startPos_2829_);
                v___x_2845_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2846_ = lean_nat_dec_eq(v___x_2844_, v___x_2845_);
                if v___x_2846_ == 0 {
                    v___x_2847_ = 1;
                    v___x_2848_ = crate::leanh::lean_box((v___x_2846_) as usize);
                    v___x_2849_ = crate::leanh::lean_box((v___x_2847_) as usize);
                    v___x_2850_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2850_, 0, v___x_2848_);
                    crate::leanh::lean_ctor_set(v___x_2850_, 1, v___x_2849_);
                    v___x_2851_ = crate::leanh::lean_box((v___x_2846_) as usize);
                    v___x_2852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2852_, 0, v___x_2851_);
                    crate::leanh::lean_ctor_set(v___x_2852_, 1, v___x_2850_);
                    v___x_2853_ = crate::leanh::lean_box((v___x_2847_) as usize);
                    v___x_2854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2854_, 0, v___x_2853_);
                    crate::leanh::lean_ctor_set(v___x_2854_, 1, v___x_2852_);
                    v___x_2868_ = lean_string_is_valid_pos(v_str_2828_, v_startPos_2829_);
                    if v___x_2868_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___x_2869_ = lean_string_is_valid_pos(v_str_2828_, v_stopPos_2830_);
                        if v___x_2869_ == 0 {
                            state = 7;
                            continue;
                        } else {
                            v___x_2870_ = lean_nat_dec_le(v_startPos_2829_, v_stopPos_2830_);
                            if v___x_2870_ == 0 {
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_stopPos_2830_);
                                crate::leanh::lean_inc(v_startPos_2829_);
                                crate::leanh::lean_inc_ref(v_str_2828_);
                                v___x_2871_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2871_, 0, v_str_2828_);
                                crate::leanh::lean_ctor_set(v___x_2871_, 1, v_startPos_2829_);
                                crate::leanh::lean_ctor_set(v___x_2871_, 2, v_stopPos_2830_);
                                v___y_2856_ = v___x_2871_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2844_);
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_stopPos_2830_);
                    crate::leanh::lean_dec(v_startPos_2829_);
                    crate::leanh::lean_dec_ref(v_str_2828_);
                    v___x_2872_ = crate::leanh::lean_box(0);
                    return v___x_2872_;
                }
            }
            4 => {
                if v___y_2835_ == 0 {
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_stopPos_2830_);
                    crate::leanh::lean_dec(v_startPos_2829_);
                    crate::leanh::lean_dec_ref(v_str_2828_);
                    v___x_2836_ = crate::leanh::lean_box(0);
                    return v___x_2836_;
                } else {
                    v___x_2837_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2838_ = lean_string_is_valid_pos(v_str_2828_, v_startPos_2829_);
                    if v___x_2838_ == 0 {
                        crate::leanh::lean_del_object(v___x_2832_);
                        crate::leanh::lean_dec(v_stopPos_2830_);
                        crate::leanh::lean_dec(v_startPos_2829_);
                        crate::leanh::lean_dec_ref(v_str_2828_);
                        v___y_2825_ = v___x_2837_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2839_ = lean_string_is_valid_pos(v_str_2828_, v_stopPos_2830_);
                        if v___x_2839_ == 0 {
                            crate::leanh::lean_del_object(v___x_2832_);
                            crate::leanh::lean_dec(v_stopPos_2830_);
                            crate::leanh::lean_dec(v_startPos_2829_);
                            crate::leanh::lean_dec_ref(v_str_2828_);
                            v___y_2825_ = v___x_2837_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2840_ = lean_nat_dec_le(v_startPos_2829_, v_stopPos_2830_);
                            if v___x_2840_ == 0 {
                                crate::leanh::lean_del_object(v___x_2832_);
                                crate::leanh::lean_dec(v_stopPos_2830_);
                                crate::leanh::lean_dec(v_startPos_2829_);
                                crate::leanh::lean_dec_ref(v_str_2828_);
                                v___y_2825_ = v___x_2837_;
                                state = 2;
                                continue;
                            } else {
                                if v_isShared_2833_ == 0 {
                                    v___x_2842_ = v___x_2832_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2843_ =
                                        crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2843_,
                                        0,
                                        v_str_2828_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2843_,
                                        1,
                                        v_startPos_2829_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2843_,
                                        2,
                                        v_stopPos_2830_,
                                    );
                                    v___x_2842_ = v_reuseFailAlloc_2843_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            5 => {
                v___y_2819_ = v___x_2837_;
                v___y_2820_ = v___x_2842_;
                state = 1;
                continue;
            }
            6 => {
                v___x_2857_ = l_String_Slice_positions(v___y_2856_);
                v___x_2858_ =
                    l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(
                        v___x_2844_,
                        v___y_2856_,
                        v___x_2857_,
                        v___x_2854_,
                    );
                crate::leanh::lean_dec_ref(v___y_2856_);
                crate::leanh::lean_dec(v___x_2844_);
                v_snd_2859_ = crate::leanh::lean_ctor_get(v___x_2858_, 1);
                crate::leanh::lean_inc(v_snd_2859_);
                crate::leanh::lean_dec_ref(v___x_2858_);
                v_snd_2860_ = crate::leanh::lean_ctor_get(v_snd_2859_, 1);
                crate::leanh::lean_inc(v_snd_2860_);
                crate::leanh::lean_dec(v_snd_2859_);
                v_snd_2861_ = crate::leanh::lean_ctor_get(v_snd_2860_, 1);
                v___x_2862_ = (crate::leanh::lean_unbox(v_snd_2861_) as u8);
                if v___x_2862_ == 0 {
                    crate::leanh::lean_dec(v_snd_2860_);
                    v___y_2835_ = v___x_2846_;
                    state = 4;
                    continue;
                } else {
                    v_fst_2863_ = crate::leanh::lean_ctor_get(v_snd_2860_, 0);
                    crate::leanh::lean_inc(v_fst_2863_);
                    crate::leanh::lean_dec(v_snd_2860_);
                    v___x_2864_ = (crate::leanh::lean_unbox(v_fst_2863_) as u8);
                    crate::leanh::lean_dec(v_fst_2863_);
                    v___y_2835_ = v___x_2864_;
                    state = 4;
                    continue;
                }
            }
            7 => {
                v___x_2866_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Substring_Raw_foldl___redArg___closed__3_once),
                    _init_l_Substring_Raw_foldl___redArg___closed__3,
                );
                v___x_2867_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_2866_);
                v___y_2856_ = v___x_2867_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
    mut v_R_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_b_2878_: *mut crate::leanh::LeanObject,
    mut v_c_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(
        v___y_2874_,
        v_a_2877_,
        v_b_2878_,
    );
    return v___x_2880_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v_inst_2882_: *mut crate::leanh::LeanObject,
    mut v_R_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
    mut v_b_2885_: *mut crate::leanh::LeanObject,
    mut v_c_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2887_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(
        v___y_2881_,
        v_inst_2882_,
        v_R_2883_,
        v_a_2884_,
        v_b_2885_,
        v_c_2886_,
    );
    crate::leanh::lean_dec_ref(v___y_2881_);
    return v_res_2887_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(
    mut v___x_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v_inst_2890_: *mut crate::leanh::LeanObject,
    mut v_R_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_b_2893_: *mut crate::leanh::LeanObject,
    mut v_c_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2895_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(
        v___x_2888_,
        v___y_2889_,
        v_a_2892_,
        v_b_2893_,
    );
    return v___x_2895_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(
    mut v___x_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v_inst_2898_: *mut crate::leanh::LeanObject,
    mut v_R_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_b_2901_: *mut crate::leanh::LeanObject,
    mut v_c_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2903_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(
        v___x_2896_,
        v___y_2897_,
        v_inst_2898_,
        v_R_2899_,
        v_a_2900_,
        v_b_2901_,
        v_c_2902_,
    );
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___x_2896_);
    return v_res_2903_;
}
pub unsafe fn l_Substring_Raw_repair(
    mut v_x_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___y_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2905_ = crate::leanh::lean_ctor_get(v_x_2904_, 0);
                v_startPos_2906_ = crate::leanh::lean_ctor_get(v_x_2904_, 1);
                v_stopPos_2907_ = crate::leanh::lean_ctor_get(v_x_2904_, 2);
                v_isSharedCheck_2923_ = (!crate::leanh::lean_is_exclusive(v_x_2904_)) as u8;
                if v_isSharedCheck_2923_ == 0 {
                    v___x_2909_ = v_x_2904_;
                    v_isShared_2910_ = v_isSharedCheck_2923_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_2907_);
                    crate::leanh::lean_inc(v_startPos_2906_);
                    crate::leanh::lean_inc(v_str_2905_);
                    crate::leanh::lean_dec(v_x_2904_);
                    v___x_2909_ = crate::leanh::lean_box(0);
                    v_isShared_2910_ = v_isSharedCheck_2923_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2921_ = lean_string_is_valid_pos(v_str_2905_, v_startPos_2906_);
                if v___x_2921_ == 0 {
                    crate::leanh::lean_dec(v_startPos_2906_);
                    v___x_2922_ = lean_string_utf8_byte_size(v_str_2905_);
                    v___y_2912_ = v___x_2922_;
                    state = 2;
                    continue;
                } else {
                    v___y_2912_ = v_startPos_2906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2913_ = lean_string_is_valid_pos(v_str_2905_, v_stopPos_2907_);
                if v___x_2913_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_2907_);
                    v___x_2914_ = lean_string_utf8_byte_size(v_str_2905_);
                    if v_isShared_2910_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2909_, 2, v___x_2914_);
                        crate::leanh::lean_ctor_set(v___x_2909_, 1, v___y_2912_);
                        v___x_2916_ = v___x_2909_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2917_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_str_2905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 1, v___y_2912_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 2, v___x_2914_);
                        v___x_2916_ = v_reuseFailAlloc_2917_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2910_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2909_, 1, v___y_2912_);
                        v___x_2919_ = v___x_2909_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2920_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_str_2905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___y_2912_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_stopPos_2907_);
                        v___x_2919_ = v_reuseFailAlloc_2920_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2916_;
            }
            4 => {
                return v___x_2919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_beq(
    mut v_ss1_2924_: *mut crate::leanh::LeanObject,
    mut v_ss2_2925_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_ss1_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ss2_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    v_ss1_2926_ = l_Substring_Raw_repair(v_ss1_2924_);
    v_str_2927_ = crate::leanh::lean_ctor_get(v_ss1_2926_, 0);
    crate::leanh::lean_inc_ref(v_str_2927_);
    v_startPos_2928_ = crate::leanh::lean_ctor_get(v_ss1_2926_, 1);
    crate::leanh::lean_inc(v_startPos_2928_);
    v_stopPos_2929_ = crate::leanh::lean_ctor_get(v_ss1_2926_, 2);
    crate::leanh::lean_inc(v_stopPos_2929_);
    crate::leanh::lean_dec_ref(v_ss1_2926_);
    v_ss2_2930_ = l_Substring_Raw_repair(v_ss2_2925_);
    v_str_2931_ = crate::leanh::lean_ctor_get(v_ss2_2930_, 0);
    crate::leanh::lean_inc_ref(v_str_2931_);
    v_startPos_2932_ = crate::leanh::lean_ctor_get(v_ss2_2930_, 1);
    crate::leanh::lean_inc(v_startPos_2932_);
    v_stopPos_2933_ = crate::leanh::lean_ctor_get(v_ss2_2930_, 2);
    crate::leanh::lean_inc(v_stopPos_2933_);
    crate::leanh::lean_dec_ref(v_ss2_2930_);
    v___x_2934_ = lean_nat_sub(v_stopPos_2929_, v_startPos_2928_);
    crate::leanh::lean_dec(v_stopPos_2929_);
    v___x_2935_ = lean_nat_sub(v_stopPos_2933_, v_startPos_2932_);
    crate::leanh::lean_dec(v_stopPos_2933_);
    v___x_2936_ = lean_nat_dec_eq(v___x_2934_, v___x_2935_);
    crate::leanh::lean_dec(v___x_2935_);
    if v___x_2936_ == 0 {
        crate::leanh::lean_dec(v___x_2934_);
        crate::leanh::lean_dec(v_startPos_2932_);
        crate::leanh::lean_dec_ref(v_str_2931_);
        crate::leanh::lean_dec(v_startPos_2928_);
        crate::leanh::lean_dec_ref(v_str_2927_);
        return v___x_2936_;
    } else {
        let mut v___x_2937_: u8 = 0;
        v___x_2937_ = l_String_Pos_Raw_substrEq(
            v_str_2927_,
            v_startPos_2928_,
            v_str_2931_,
            v_startPos_2932_,
            v___x_2934_,
        );
        crate::leanh::lean_dec(v___x_2934_);
        crate::leanh::lean_dec_ref(v_str_2931_);
        crate::leanh::lean_dec_ref(v_str_2927_);
        return v___x_2937_;
    }
}
pub unsafe fn l_Substring_Raw_beq___boxed(
    mut v_ss1_2938_: *mut crate::leanh::LeanObject,
    mut v_ss2_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: u8 = 0;
    let mut v_r_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Substring_Raw_beq(v_ss1_2938_, v_ss2_2939_);
    v_r_2941_ = crate::leanh::lean_box((v_res_2940_) as usize);
    return v_r_2941_;
}
pub unsafe fn lean_substring_beq(
    mut v_ss1_2942_: *mut crate::leanh::LeanObject,
    mut v_ss2_2943_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2944_: u8 = 0;
    v___x_2944_ = l_Substring_Raw_beq(v_ss1_2942_, v_ss2_2943_);
    return v___x_2944_;
}
pub unsafe fn l_Substring_Raw_Internal_beqImpl___boxed(
    mut v_ss1_2945_: *mut crate::leanh::LeanObject,
    mut v_ss2_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2947_: u8 = 0;
    let mut v_r_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2947_ = lean_substring_beq(v_ss1_2945_, v_ss2_2946_);
    v_r_2948_ = crate::leanh::lean_box((v_res_2947_) as usize);
    return v_r_2948_;
}
pub unsafe fn l_Substring_Raw_sameAs(
    mut v_ss1_2951_: *mut crate::leanh::LeanObject,
    mut v_ss2_2952_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startPos_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    v_startPos_2953_ = crate::leanh::lean_ctor_get(v_ss1_2951_, 1);
    v_startPos_2954_ = crate::leanh::lean_ctor_get(v_ss2_2952_, 1);
    v___x_2955_ = lean_nat_dec_eq(v_startPos_2953_, v_startPos_2954_);
    if v___x_2955_ == 0 {
        crate::leanh::lean_dec_ref(v_ss2_2952_);
        crate::leanh::lean_dec_ref(v_ss1_2951_);
        return v___x_2955_;
    } else {
        let mut v___x_2956_: u8 = 0;
        v___x_2956_ = l_Substring_Raw_beq(v_ss1_2951_, v_ss2_2952_);
        return v___x_2956_;
    }
}
pub unsafe fn l_Substring_Raw_sameAs___boxed(
    mut v_ss1_2957_: *mut crate::leanh::LeanObject,
    mut v_ss2_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2959_: u8 = 0;
    let mut v_r_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2959_ = l_Substring_Raw_sameAs(v_ss1_2957_, v_ss2_2958_);
    v_r_2960_ = crate::leanh::lean_box((v_res_2959_) as usize);
    return v_r_2960_;
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(
    mut v_s_2961_: *mut crate::leanh::LeanObject,
    mut v_t_2962_: *mut crate::leanh::LeanObject,
    mut v_spos_2963_: *mut crate::leanh::LeanObject,
    mut v_tpos_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: u8 = 0;
    let mut v_str_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2971_: u32 = 0;
    let mut v___x_2972_: u32 = 0;
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2965_ = crate::leanh::lean_ctor_get(v_s_2961_, 0);
                v_stopPos_2966_ = crate::leanh::lean_ctor_get(v_s_2961_, 2);
                v___x_2967_ = lean_nat_dec_lt(v_spos_2963_, v_stopPos_2966_);
                if v___x_2967_ == 0 {
                    crate::leanh::lean_dec(v_tpos_2964_);
                    return v_spos_2963_;
                } else {
                    v_str_2968_ = crate::leanh::lean_ctor_get(v_t_2962_, 0);
                    v_stopPos_2969_ = crate::leanh::lean_ctor_get(v_t_2962_, 2);
                    v___x_2970_ = lean_nat_dec_lt(v_tpos_2964_, v_stopPos_2969_);
                    if v___x_2970_ == 0 {
                        crate::leanh::lean_dec(v_tpos_2964_);
                        return v_spos_2963_;
                    } else {
                        v___x_2971_ = lean_string_utf8_get(v_str_2965_, v_spos_2963_);
                        v___x_2972_ = lean_string_utf8_get(v_str_2968_, v_tpos_2964_);
                        v___x_2973_ = lean_uint32_dec_eq(v___x_2971_, v___x_2972_);
                        if v___x_2973_ == 0 {
                            crate::leanh::lean_dec(v_tpos_2964_);
                            return v_spos_2963_;
                        } else {
                            v___x_2974_ = lean_string_utf8_next(v_str_2965_, v_spos_2963_);
                            crate::leanh::lean_dec(v_spos_2963_);
                            v___x_2975_ = lean_string_utf8_next(v_str_2968_, v_tpos_2964_);
                            crate::leanh::lean_dec(v_tpos_2964_);
                            v_spos_2963_ = v___x_2974_;
                            v_tpos_2964_ = v___x_2975_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(
    mut v_s_2977_: *mut crate::leanh::LeanObject,
    mut v_t_2978_: *mut crate::leanh::LeanObject,
    mut v_spos_2979_: *mut crate::leanh::LeanObject,
    mut v_tpos_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2981_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(
        v_s_2977_,
        v_t_2978_,
        v_spos_2979_,
        v_tpos_2980_,
    );
    crate::leanh::lean_dec_ref(v_t_2978_);
    crate::leanh::lean_dec_ref(v_s_2977_);
    return v_res_2981_;
}
pub unsafe fn l_Substring_Raw_commonPrefix(
    mut v_s_2982_: *mut crate::leanh::LeanObject,
    mut v_t_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2990_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2984_ = crate::leanh::lean_ctor_get(v_s_2982_, 0);
                crate::leanh::lean_inc_ref(v_str_2984_);
                v_startPos_2985_ = crate::leanh::lean_ctor_get(v_s_2982_, 1);
                crate::leanh::lean_inc_n(v_startPos_2985_, 2);
                v_startPos_2986_ = crate::leanh::lean_ctor_get(v_t_2983_, 1);
                crate::leanh::lean_inc(v_startPos_2986_);
                v___x_2987_ =
                    l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(
                        v_s_2982_,
                        v_t_2983_,
                        v_startPos_2985_,
                        v_startPos_2986_,
                    );
                crate::leanh::lean_dec_ref(v_s_2982_);
                v_isSharedCheck_2994_ = (!crate::leanh::lean_is_exclusive(v_t_2983_)) as u8;
                if v_isSharedCheck_2994_ == 0 {
                    v_unused_2995_ = crate::leanh::lean_ctor_get(v_t_2983_, 2);
                    crate::leanh::lean_dec(v_unused_2995_);
                    v_unused_2996_ = crate::leanh::lean_ctor_get(v_t_2983_, 1);
                    crate::leanh::lean_dec(v_unused_2996_);
                    v_unused_2997_ = crate::leanh::lean_ctor_get(v_t_2983_, 0);
                    crate::leanh::lean_dec(v_unused_2997_);
                    v___x_2989_ = v_t_2983_;
                    v_isShared_2990_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_t_2983_);
                    v___x_2989_ = crate::leanh::lean_box(0);
                    v_isShared_2990_ = v_isSharedCheck_2994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2989_, 2, v___x_2987_);
                    crate::leanh::lean_ctor_set(v___x_2989_, 1, v_startPos_2985_);
                    crate::leanh::lean_ctor_set(v___x_2989_, 0, v_str_2984_);
                    v___x_2992_ = v___x_2989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_str_2984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_startPos_2985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 2, v___x_2987_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(
    mut v_s_2998_: *mut crate::leanh::LeanObject,
    mut v_t_2999_: *mut crate::leanh::LeanObject,
    mut v_spos_3000_: *mut crate::leanh::LeanObject,
    mut v_tpos_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: u8 = 0;
    let mut v_str_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v_spos_x27_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tpos_x27_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: u32 = 0;
    let mut v___x_3011_: u32 = 0;
    let mut v___x_3012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3002_ = crate::leanh::lean_ctor_get(v_s_2998_, 0);
                v_startPos_3003_ = crate::leanh::lean_ctor_get(v_s_2998_, 1);
                v___x_3004_ = lean_nat_dec_lt(v_startPos_3003_, v_spos_3000_);
                if v___x_3004_ == 0 {
                    crate::leanh::lean_dec(v_tpos_3001_);
                    return v_spos_3000_;
                } else {
                    v_str_3005_ = crate::leanh::lean_ctor_get(v_t_2999_, 0);
                    v_startPos_3006_ = crate::leanh::lean_ctor_get(v_t_2999_, 1);
                    v___x_3007_ = lean_nat_dec_lt(v_startPos_3006_, v_tpos_3001_);
                    if v___x_3007_ == 0 {
                        crate::leanh::lean_dec(v_tpos_3001_);
                        return v_spos_3000_;
                    } else {
                        v_spos_x27_3008_ = lean_string_utf8_prev(v_str_3002_, v_spos_3000_);
                        v_tpos_x27_3009_ = lean_string_utf8_prev(v_str_3005_, v_tpos_3001_);
                        crate::leanh::lean_dec(v_tpos_3001_);
                        v___x_3010_ = lean_string_utf8_get(v_str_3002_, v_spos_x27_3008_);
                        v___x_3011_ = lean_string_utf8_get(v_str_3005_, v_tpos_x27_3009_);
                        v___x_3012_ = lean_uint32_dec_eq(v___x_3010_, v___x_3011_);
                        if v___x_3012_ == 0 {
                            crate::leanh::lean_dec(v_tpos_x27_3009_);
                            crate::leanh::lean_dec(v_spos_x27_3008_);
                            return v_spos_3000_;
                        } else {
                            crate::leanh::lean_dec(v_spos_3000_);
                            v_spos_3000_ = v_spos_x27_3008_;
                            v_tpos_3001_ = v_tpos_x27_3009_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(
    mut v_s_3014_: *mut crate::leanh::LeanObject,
    mut v_t_3015_: *mut crate::leanh::LeanObject,
    mut v_spos_3016_: *mut crate::leanh::LeanObject,
    mut v_tpos_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(
        v_s_3014_,
        v_t_3015_,
        v_spos_3016_,
        v_tpos_3017_,
    );
    crate::leanh::lean_dec_ref(v_t_3015_);
    crate::leanh::lean_dec_ref(v_s_3014_);
    return v_res_3018_;
}
pub unsafe fn l_Substring_Raw_commonSuffix(
    mut v_s_3019_: *mut crate::leanh::LeanObject,
    mut v_t_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_unused_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3021_ = crate::leanh::lean_ctor_get(v_s_3019_, 0);
                crate::leanh::lean_inc_ref(v_str_3021_);
                v_stopPos_3022_ = crate::leanh::lean_ctor_get(v_s_3019_, 2);
                crate::leanh::lean_inc_n(v_stopPos_3022_, 2);
                v_stopPos_3023_ = crate::leanh::lean_ctor_get(v_t_3020_, 2);
                crate::leanh::lean_inc(v_stopPos_3023_);
                v___x_3024_ =
                    l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(
                        v_s_3019_,
                        v_t_3020_,
                        v_stopPos_3022_,
                        v_stopPos_3023_,
                    );
                crate::leanh::lean_dec_ref(v_s_3019_);
                v_isSharedCheck_3031_ = (!crate::leanh::lean_is_exclusive(v_t_3020_)) as u8;
                if v_isSharedCheck_3031_ == 0 {
                    v_unused_3032_ = crate::leanh::lean_ctor_get(v_t_3020_, 2);
                    crate::leanh::lean_dec(v_unused_3032_);
                    v_unused_3033_ = crate::leanh::lean_ctor_get(v_t_3020_, 1);
                    crate::leanh::lean_dec(v_unused_3033_);
                    v_unused_3034_ = crate::leanh::lean_ctor_get(v_t_3020_, 0);
                    crate::leanh::lean_dec(v_unused_3034_);
                    v___x_3026_ = v_t_3020_;
                    v_isShared_3027_ = v_isSharedCheck_3031_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_t_3020_);
                    v___x_3026_ = crate::leanh::lean_box(0);
                    v_isShared_3027_ = v_isSharedCheck_3031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3026_, 2, v_stopPos_3022_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 1, v___x_3024_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 0, v_str_3021_);
                    v___x_3029_ = v___x_3026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_str_3021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_stopPos_3022_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_dropPrefix_x3f(
    mut v_s_3035_: *mut crate::leanh::LeanObject,
    mut v_pre_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_pre_3036_);
                crate::leanh::lean_inc_ref(v_s_3035_);
                v_t_3037_ = l_Substring_Raw_commonPrefix(v_s_3035_, v_pre_3036_);
                v_startPos_3038_ = crate::leanh::lean_ctor_get(v_t_3037_, 1);
                crate::leanh::lean_inc(v_startPos_3038_);
                v_stopPos_3039_ = crate::leanh::lean_ctor_get(v_t_3037_, 2);
                crate::leanh::lean_inc(v_stopPos_3039_);
                crate::leanh::lean_dec_ref(v_t_3037_);
                v_startPos_3040_ = crate::leanh::lean_ctor_get(v_pre_3036_, 1);
                crate::leanh::lean_inc(v_startPos_3040_);
                v_stopPos_3041_ = crate::leanh::lean_ctor_get(v_pre_3036_, 2);
                crate::leanh::lean_inc(v_stopPos_3041_);
                crate::leanh::lean_dec_ref(v_pre_3036_);
                v___x_3042_ = lean_nat_sub(v_stopPos_3039_, v_startPos_3038_);
                crate::leanh::lean_dec(v_startPos_3038_);
                v___x_3043_ = lean_nat_sub(v_stopPos_3041_, v_startPos_3040_);
                crate::leanh::lean_dec(v_startPos_3040_);
                crate::leanh::lean_dec(v_stopPos_3041_);
                v___x_3044_ = lean_nat_dec_eq(v___x_3042_, v___x_3043_);
                crate::leanh::lean_dec(v___x_3043_);
                crate::leanh::lean_dec(v___x_3042_);
                if v___x_3044_ == 0 {
                    crate::leanh::lean_dec(v_stopPos_3039_);
                    crate::leanh::lean_dec_ref(v_s_3035_);
                    v___x_3045_ = crate::leanh::lean_box(0);
                    return v___x_3045_;
                } else {
                    v_str_3046_ = crate::leanh::lean_ctor_get(v_s_3035_, 0);
                    v_stopPos_3047_ = crate::leanh::lean_ctor_get(v_s_3035_, 2);
                    v_isSharedCheck_3055_ = (!crate::leanh::lean_is_exclusive(v_s_3035_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v_unused_3056_ = crate::leanh::lean_ctor_get(v_s_3035_, 1);
                        crate::leanh::lean_dec(v_unused_3056_);
                        v___x_3049_ = v_s_3035_;
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_stopPos_3047_);
                        crate::leanh::lean_inc(v_str_3046_);
                        crate::leanh::lean_dec(v_s_3035_);
                        v___x_3049_ = crate::leanh::lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3050_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3049_, 1, v_stopPos_3039_);
                    v___x_3052_ = v___x_3049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_str_3046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_stopPos_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_stopPos_3047_);
                    v___x_3052_ = v_reuseFailAlloc_3054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3053_, 0, v___x_3052_);
                return v___x_3053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_dropSuffix_x3f(
    mut v_s_3057_: *mut crate::leanh::LeanObject,
    mut v_suff_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v_unused_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_suff_3058_);
                crate::leanh::lean_inc_ref(v_s_3057_);
                v_t_3059_ = l_Substring_Raw_commonSuffix(v_s_3057_, v_suff_3058_);
                v_startPos_3060_ = crate::leanh::lean_ctor_get(v_t_3059_, 1);
                crate::leanh::lean_inc(v_startPos_3060_);
                v_stopPos_3061_ = crate::leanh::lean_ctor_get(v_t_3059_, 2);
                crate::leanh::lean_inc(v_stopPos_3061_);
                crate::leanh::lean_dec_ref(v_t_3059_);
                v_startPos_3062_ = crate::leanh::lean_ctor_get(v_suff_3058_, 1);
                crate::leanh::lean_inc(v_startPos_3062_);
                v_stopPos_3063_ = crate::leanh::lean_ctor_get(v_suff_3058_, 2);
                crate::leanh::lean_inc(v_stopPos_3063_);
                crate::leanh::lean_dec_ref(v_suff_3058_);
                v___x_3064_ = lean_nat_sub(v_stopPos_3061_, v_startPos_3060_);
                crate::leanh::lean_dec(v_stopPos_3061_);
                v___x_3065_ = lean_nat_sub(v_stopPos_3063_, v_startPos_3062_);
                crate::leanh::lean_dec(v_startPos_3062_);
                crate::leanh::lean_dec(v_stopPos_3063_);
                v___x_3066_ = lean_nat_dec_eq(v___x_3064_, v___x_3065_);
                crate::leanh::lean_dec(v___x_3065_);
                crate::leanh::lean_dec(v___x_3064_);
                if v___x_3066_ == 0 {
                    crate::leanh::lean_dec(v_startPos_3060_);
                    crate::leanh::lean_dec_ref(v_s_3057_);
                    v___x_3067_ = crate::leanh::lean_box(0);
                    return v___x_3067_;
                } else {
                    v_str_3068_ = crate::leanh::lean_ctor_get(v_s_3057_, 0);
                    v_startPos_3069_ = crate::leanh::lean_ctor_get(v_s_3057_, 1);
                    v_isSharedCheck_3077_ = (!crate::leanh::lean_is_exclusive(v_s_3057_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v_unused_3078_ = crate::leanh::lean_ctor_get(v_s_3057_, 2);
                        crate::leanh::lean_dec(v_unused_3078_);
                        v___x_3071_ = v_s_3057_;
                        v_isShared_3072_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_startPos_3069_);
                        crate::leanh::lean_inc(v_str_3068_);
                        crate::leanh::lean_dec(v_s_3057_);
                        v___x_3071_ = crate::leanh::lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3077_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3071_, 2, v_startPos_3060_);
                    v___x_3074_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3076_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_str_3068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_startPos_3069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_startPos_3060_);
                    v___x_3074_ = v_reuseFailAlloc_3076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3075_, 0, v___x_3074_);
                return v___x_3075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(
    mut v_x_3079_: *mut crate::leanh::LeanObject,
    mut v_x_3080_: *mut crate::leanh::LeanObject,
    mut v_x_3081_: *mut crate::leanh::LeanObject,
    mut v_h__1_3082_: *mut crate::leanh::LeanObject,
    mut v_h__2_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3085_: u8 = 0;
    v_zero_3084_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3085_ = lean_nat_dec_eq(v_x_3080_, v_zero_3084_);
    if v_isZero_3085_ == 1 {
        let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3083_);
        v___x_3086_ = crate::leanh::lean_apply_2(v_h__1_3082_, v_x_3079_, v_x_3081_);
        return v___x_3086_;
    } else {
        let mut v_one_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3082_);
        v_one_3087_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3088_ = lean_nat_sub(v_x_3080_, v_one_3087_);
        v___x_3089_ = crate::leanh::lean_apply_3(v_h__2_3083_, v_x_3079_, v_n_3088_, v_x_3081_);
        return v___x_3089_;
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(
    mut v_x_3090_: *mut crate::leanh::LeanObject,
    mut v_x_3091_: *mut crate::leanh::LeanObject,
    mut v_x_3092_: *mut crate::leanh::LeanObject,
    mut v_h__1_3093_: *mut crate::leanh::LeanObject,
    mut v_h__2_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3095_ =
        l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(
            v_x_3090_,
            v_x_3091_,
            v_x_3092_,
            v_h__1_3093_,
            v_h__2_3094_,
        );
    crate::leanh::lean_dec(v_x_3091_);
    return v_res_3095_;
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(
    mut v_motive_3096_: *mut crate::leanh::LeanObject,
    mut v_x_3097_: *mut crate::leanh::LeanObject,
    mut v_x_3098_: *mut crate::leanh::LeanObject,
    mut v_x_3099_: *mut crate::leanh::LeanObject,
    mut v_h__1_3100_: *mut crate::leanh::LeanObject,
    mut v_h__2_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3103_: u8 = 0;
    v_zero_3102_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3103_ = lean_nat_dec_eq(v_x_3098_, v_zero_3102_);
    if v_isZero_3103_ == 1 {
        let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3101_);
        v___x_3104_ = crate::leanh::lean_apply_2(v_h__1_3100_, v_x_3097_, v_x_3099_);
        return v___x_3104_;
    } else {
        let mut v_one_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3100_);
        v_one_3105_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3106_ = lean_nat_sub(v_x_3098_, v_one_3105_);
        v___x_3107_ = crate::leanh::lean_apply_3(v_h__2_3101_, v_x_3097_, v_n_3106_, v_x_3099_);
        return v___x_3107_;
    }
}
pub unsafe fn l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(
    mut v_motive_3108_: *mut crate::leanh::LeanObject,
    mut v_x_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
    mut v_x_3111_: *mut crate::leanh::LeanObject,
    mut v_h__1_3112_: *mut crate::leanh::LeanObject,
    mut v_h__2_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(
        v_motive_3108_,
        v_x_3109_,
        v_x_3110_,
        v_x_3111_,
        v_h__1_3112_,
        v_h__2_3113_,
    );
    crate::leanh::lean_dec(v_x_3110_);
    return v_res_3114_;
}
pub unsafe fn l_Substring_bsize(
    mut v_a_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startPos_3116_ = crate::leanh::lean_ctor_get(v_a_3115_, 1);
    v_stopPos_3117_ = crate::leanh::lean_ctor_get(v_a_3115_, 2);
    v___x_3118_ = lean_nat_sub(v_stopPos_3117_, v_startPos_3116_);
    return v___x_3118_;
}
pub unsafe fn l_Substring_bsize___boxed(
    mut v_a_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Substring_bsize(v_a_3119_);
    crate::leanh::lean_dec_ref(v_a_3119_);
    return v_res_3120_;
}
pub unsafe fn l_Substring_toString(
    mut v_a_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_3122_ = crate::leanh::lean_ctor_get(v_a_3121_, 0);
    v_startPos_3123_ = crate::leanh::lean_ctor_get(v_a_3121_, 1);
    v_stopPos_3124_ = crate::leanh::lean_ctor_get(v_a_3121_, 2);
    v___x_3125_ = lean_string_utf8_extract(v_str_3122_, v_startPos_3123_, v_stopPos_3124_);
    return v___x_3125_;
}
pub unsafe fn l_Substring_toString___boxed(
    mut v_a_3126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3127_ = l_Substring_toString(v_a_3126_);
    crate::leanh::lean_dec_ref(v_a_3126_);
    return v_res_3127_;
}
pub unsafe fn l_Substring_isEmpty(mut v_ss_3128_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_startPos_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: u8 = 0;
    v_startPos_3129_ = crate::leanh::lean_ctor_get(v_ss_3128_, 1);
    v_stopPos_3130_ = crate::leanh::lean_ctor_get(v_ss_3128_, 2);
    v___x_3131_ = lean_nat_sub(v_stopPos_3130_, v_startPos_3129_);
    v___x_3132_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3133_ = lean_nat_dec_eq(v___x_3131_, v___x_3132_);
    crate::leanh::lean_dec(v___x_3131_);
    return v___x_3133_;
}
pub unsafe fn l_Substring_isEmpty___boxed(
    mut v_ss_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: u8 = 0;
    let mut v_r_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Substring_isEmpty(v_ss_3134_);
    crate::leanh::lean_dec_ref(v_ss_3134_);
    v_r_3136_ = crate::leanh::lean_box((v_res_3135_) as usize);
    return v_r_3136_;
}
pub unsafe fn l_Substring_next(
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    v_str_3139_ = crate::leanh::lean_ctor_get(v_a_3137_, 0);
    v_startPos_3140_ = crate::leanh::lean_ctor_get(v_a_3137_, 1);
    v_stopPos_3141_ = crate::leanh::lean_ctor_get(v_a_3137_, 2);
    v_absP_3142_ = lean_nat_add(v_startPos_3140_, v_a_3138_);
    v___x_3143_ = lean_nat_dec_eq(v_absP_3142_, v_stopPos_3141_);
    if v___x_3143_ == 0 {
        let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3144_ = lean_string_utf8_next(v_str_3139_, v_absP_3142_);
        crate::leanh::lean_dec(v_absP_3142_);
        v___x_3145_ = lean_nat_sub(v___x_3144_, v_startPos_3140_);
        crate::leanh::lean_dec(v___x_3144_);
        return v___x_3145_;
    } else {
        crate::leanh::lean_dec(v_absP_3142_);
        crate::leanh::lean_inc(v_a_3138_);
        return v_a_3138_;
    }
}
pub unsafe fn l_Substring_next___boxed(
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Substring_next(v_a_3146_, v_a_3147_);
    crate::leanh::lean_dec(v_a_3147_);
    crate::leanh::lean_dec_ref(v_a_3146_);
    return v_res_3148_;
}
pub unsafe fn l_Substring_prev(
    mut v_a_3149_: *mut crate::leanh::LeanObject,
    mut v_a_3150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_absP_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: u8 = 0;
    v_str_3151_ = crate::leanh::lean_ctor_get(v_a_3149_, 0);
    v_startPos_3152_ = crate::leanh::lean_ctor_get(v_a_3149_, 1);
    v_absP_3153_ = lean_nat_add(v_startPos_3152_, v_a_3150_);
    v___x_3154_ = lean_nat_dec_eq(v_absP_3153_, v_startPos_3152_);
    if v___x_3154_ == 0 {
        let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3155_ = lean_string_utf8_prev(v_str_3151_, v_absP_3153_);
        crate::leanh::lean_dec(v_absP_3153_);
        v___x_3156_ = lean_nat_sub(v___x_3155_, v_startPos_3152_);
        crate::leanh::lean_dec(v___x_3155_);
        return v___x_3156_;
    } else {
        crate::leanh::lean_dec(v_absP_3153_);
        crate::leanh::lean_inc(v_a_3150_);
        return v_a_3150_;
    }
}
pub unsafe fn l_Substring_prev___boxed(
    mut v_a_3157_: *mut crate::leanh::LeanObject,
    mut v_a_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Substring_prev(v_a_3157_, v_a_3158_);
    crate::leanh::lean_dec(v_a_3158_);
    crate::leanh::lean_dec_ref(v_a_3157_);
    return v_res_3159_;
}
pub unsafe fn l_Substring_atEnd(
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_startPos_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    v_startPos_3162_ = crate::leanh::lean_ctor_get(v_a_3160_, 1);
    v_stopPos_3163_ = crate::leanh::lean_ctor_get(v_a_3160_, 2);
    v___x_3164_ = lean_nat_add(v_startPos_3162_, v_a_3161_);
    v___x_3165_ = lean_nat_dec_eq(v___x_3164_, v_stopPos_3163_);
    crate::leanh::lean_dec(v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Substring_atEnd___boxed(
    mut v_a_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3168_: u8 = 0;
    let mut v_r_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3168_ = l_Substring_atEnd(v_a_3166_, v_a_3167_);
    crate::leanh::lean_dec(v_a_3167_);
    crate::leanh::lean_dec_ref(v_a_3166_);
    v_r_3169_ = crate::leanh::lean_box((v_res_3168_) as usize);
    return v_r_3169_;
}
pub unsafe fn l_Substring_beq(
    mut v_ss1_3170_: *mut crate::leanh::LeanObject,
    mut v_ss2_3171_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3172_: u8 = 0;
    v___x_3172_ = l_Substring_Raw_beq(v_ss1_3170_, v_ss2_3171_);
    return v___x_3172_;
}
pub unsafe fn l_Substring_beq___boxed(
    mut v_ss1_3173_: *mut crate::leanh::LeanObject,
    mut v_ss2_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3175_: u8 = 0;
    let mut v_r_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Substring_beq(v_ss1_3173_, v_ss2_3174_);
    v_r_3176_ = crate::leanh::lean_box((v_res_3175_) as usize);
    return v_r_3176_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Substring(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Substring(
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
pub unsafe fn initialize_Init_Data_String_Substring(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Substring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Substring(builtin);
}
