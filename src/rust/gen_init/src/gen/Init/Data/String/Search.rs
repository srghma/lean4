// Lean compiler output
// Module: Init.Data.String.Search
// Imports: Init.Data.String.Slice Init.Data.Iterators.Consumers.Collect
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_is_valid_pos,
    lean_string_utf8_byte_size, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_instInhabited;
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x3f, l_String_Slice_pos_x3f, l_String_Slice_pos_x21, l_String_slice_x21,
};
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prev_x3f, l_String_Slice_posLE,
};
use crate::r#gen::Init::Data::String::Iterate::{
    l_String_Slice_positions, l_String_Slice_revPositions,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, l_String_Slice_contains___redArg, l_String_Slice_isInt,
    l_String_Slice_isNat, l_String_Slice_lines, l_String_Slice_replace___redArg,
    l_String_Slice_revFind_x3f___redArg, l_String_Slice_splitInclusive___redArg,
    l_String_Slice_splitToSubslice___redArg, l_String_Slice_toInt_x3f, l_String_Slice_toNat_x3f,
    l_String_Slice_toNat_x21, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
pub static l_String_Slice_Pos_find_x3f___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_Slice_Pos_find_x3f___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Slice_Pos_find_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_find_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_Pos_find_x3f___redArg___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_String_Slice_Pos_find_x3f___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_find_x3f___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_String_toInt_x21___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_String_toInt_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_toInt_x21___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_String_replace___redArg(
    mut v_inst_1489_: *mut leanh::LeanObject,
    mut v_inst_1490_: *mut leanh::LeanObject,
    mut v_s_1491_: *mut leanh::LeanObject,
    mut v_inst_1492_: *mut leanh::LeanObject,
    mut v_replacement_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = leanh::lean_unsigned_to_nat(0);
    v___x_1495_ = lean_string_utf8_byte_size(v_s_1491_);
    v___x_1496_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1496_, 0, v_s_1491_);
    leanh::lean_ctor_set(v___x_1496_, 1, v___x_1494_);
    leanh::lean_ctor_set(v___x_1496_, 2, v___x_1495_);
    v___x_1497_ = l_String_Slice_replace___redArg(
        v_inst_1489_,
        v_inst_1490_,
        v___x_1496_,
        v_inst_1492_,
        v_replacement_1493_,
    );
    return v___x_1497_;
}
pub unsafe fn l_String_replace(
    mut v_00_u03c1_1498_: *mut leanh::LeanObject,
    mut v_00_u03c3_1499_: *mut leanh::LeanObject,
    mut v_inst_1500_: *mut leanh::LeanObject,
    mut v_inst_1501_: *mut leanh::LeanObject,
    mut v_00_u03b1_1502_: *mut leanh::LeanObject,
    mut v_inst_1503_: *mut leanh::LeanObject,
    mut v_s_1504_: *mut leanh::LeanObject,
    mut v_pattern_1505_: *mut leanh::LeanObject,
    mut v_inst_1506_: *mut leanh::LeanObject,
    mut v_replacement_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = leanh::lean_unsigned_to_nat(0);
    v___x_1509_ = lean_string_utf8_byte_size(v_s_1504_);
    v___x_1510_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1510_, 0, v_s_1504_);
    leanh::lean_ctor_set(v___x_1510_, 1, v___x_1508_);
    leanh::lean_ctor_set(v___x_1510_, 2, v___x_1509_);
    v___x_1511_ = l_String_Slice_replace___redArg(
        v_inst_1501_,
        v_inst_1503_,
        v___x_1510_,
        v_inst_1506_,
        v_replacement_1507_,
    );
    return v___x_1511_;
}
pub unsafe fn l_String_replace___boxed(
    mut v_00_u03c1_1512_: *mut leanh::LeanObject,
    mut v_00_u03c3_1513_: *mut leanh::LeanObject,
    mut v_inst_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
    mut v_00_u03b1_1516_: *mut leanh::LeanObject,
    mut v_inst_1517_: *mut leanh::LeanObject,
    mut v_s_1518_: *mut leanh::LeanObject,
    mut v_pattern_1519_: *mut leanh::LeanObject,
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_replacement_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_String_replace(
        v_00_u03c1_1512_,
        v_00_u03c3_1513_,
        v_inst_1514_,
        v_inst_1515_,
        v_00_u03b1_1516_,
        v_inst_1517_,
        v_s_1518_,
        v_pattern_1519_,
        v_inst_1520_,
        v_replacement_1521_,
    );
    leanh::lean_dec(v_pattern_1519_);
    leanh::lean_dec(v_inst_1514_);
    return v_res_1522_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__0(
    mut v_x_1523_: *mut leanh::LeanObject,
    mut v_x_1524_: *mut leanh::LeanObject,
    mut v_f_1525_: *mut leanh::LeanObject,
    mut v_c_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = leanh::lean_apply_1(v_f_1525_, v_c_1526_);
    return v___x_1527_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__1(
    mut v___x_1528_: *mut leanh::LeanObject,
    mut v_x1_1529_: *mut leanh::LeanObject,
    mut v_x2_1530_: *mut leanh::LeanObject,
    mut v_x3_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x1_1529_) == 0 {
        let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1532_, 0, v___x_1528_);
        return v___x_1532_;
    } else {
        let mut v_startPos_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1528_);
        v_startPos_1533_ = leanh::lean_ctor_get(v_x1_1529_, 0);
        leanh::lean_inc(v_startPos_1533_);
        v___x_1534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1534_, 0, v_startPos_1533_);
        v___x_1535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
        return v___x_1535_;
    }
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(
    mut v___x_1536_: *mut leanh::LeanObject,
    mut v_x1_1537_: *mut leanh::LeanObject,
    mut v_x2_1538_: *mut leanh::LeanObject,
    mut v_x3_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_String_Slice_Pos_find_x3f___redArg___lam__1(
        v___x_1536_,
        v_x1_1537_,
        v_x2_1538_,
        v_x3_1539_,
    );
    leanh::lean_dec(v_x3_1539_);
    leanh::lean_dec_ref(v_x1_1537_);
    return v_res_1540_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg(
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_s_1545_: *mut leanh::LeanObject,
    mut v_pos_1546_: *mut leanh::LeanObject,
    mut v_inst_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___f_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut v_reuseFailAlloc_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1548_ = leanh::lean_ctor_get(v_s_1545_, 0);
                v_startInclusive_1549_ = leanh::lean_ctor_get(v_s_1545_, 1);
                v_endExclusive_1550_ = leanh::lean_ctor_get(v_s_1545_, 2);
                v_isSharedCheck_1572_ = (!leanh::lean_is_exclusive(v_s_1545_)) as u8;
                if v_isSharedCheck_1572_ == 0 {
                    v___x_1552_ = v_s_1545_;
                    v_isShared_1553_ = v_isSharedCheck_1572_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1550_);
                    leanh::lean_inc(v_startInclusive_1549_);
                    leanh::lean_inc(v_str_1548_);
                    leanh::lean_dec(v_s_1545_);
                    v___x_1552_ = leanh::lean_box(0);
                    v_isShared_1553_ = v_isSharedCheck_1572_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1554_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1555_ = lean_nat_add(v_startInclusive_1549_, v_pos_1546_);
                leanh::lean_dec(v_startInclusive_1549_);
                if v_isShared_1553_ == 0 {
                    leanh::lean_ctor_set(v___x_1552_, 1, v___x_1555_);
                    v___x_1557_ = v___x_1552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_str_1548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_endExclusive_1550_);
                    v___x_1557_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_1557_);
                v_searcher_1558_ = leanh::lean_apply_1(v_inst_1547_, v___x_1557_);
                v___x_1559_ = leanh::lean_box(0);
                v___f_1560_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1561_ = leanh::lean_apply_7(
                    v_inst_1544_,
                    v___x_1557_,
                    v___f_1554_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1558_,
                    v___x_1559_,
                    v___f_1560_,
                );
                if leanh::lean_obj_tag(v___x_1561_) == 0 {
                    return v___x_1561_;
                } else {
                    v_val_1562_ = leanh::lean_ctor_get(v___x_1561_, 0);
                    v_isSharedCheck_1570_ = (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1564_ = v___x_1561_;
                        v_isShared_1565_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1562_);
                        leanh::lean_dec(v___x_1561_);
                        v___x_1564_ = leanh::lean_box(0);
                        v_isShared_1565_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1566_ = lean_nat_add(v_pos_1546_, v_val_1562_);
                leanh::lean_dec(v_val_1562_);
                if v_isShared_1565_ == 0 {
                    leanh::lean_ctor_set(v___x_1564_, 0, v___x_1566_);
                    v___x_1568_ = v___x_1564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___boxed(
    mut v_inst_1573_: *mut leanh::LeanObject,
    mut v_s_1574_: *mut leanh::LeanObject,
    mut v_pos_1575_: *mut leanh::LeanObject,
    mut v_inst_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ =
        l_String_Slice_Pos_find_x3f___redArg(v_inst_1573_, v_s_1574_, v_pos_1575_, v_inst_1576_);
    leanh::lean_dec(v_pos_1575_);
    return v_res_1577_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f(
    mut v_00_u03c1_1578_: *mut leanh::LeanObject,
    mut v_00_u03c3_1579_: *mut leanh::LeanObject,
    mut v_inst_1580_: *mut leanh::LeanObject,
    mut v_inst_1581_: *mut leanh::LeanObject,
    mut v_s_1582_: *mut leanh::LeanObject,
    mut v_pos_1583_: *mut leanh::LeanObject,
    mut v_pattern_1584_: *mut leanh::LeanObject,
    mut v_inst_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___f_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_reuseFailAlloc_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1586_ = leanh::lean_ctor_get(v_s_1582_, 0);
                v_startInclusive_1587_ = leanh::lean_ctor_get(v_s_1582_, 1);
                v_endExclusive_1588_ = leanh::lean_ctor_get(v_s_1582_, 2);
                v_isSharedCheck_1610_ = (!leanh::lean_is_exclusive(v_s_1582_)) as u8;
                if v_isSharedCheck_1610_ == 0 {
                    v___x_1590_ = v_s_1582_;
                    v_isShared_1591_ = v_isSharedCheck_1610_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1588_);
                    leanh::lean_inc(v_startInclusive_1587_);
                    leanh::lean_inc(v_str_1586_);
                    leanh::lean_dec(v_s_1582_);
                    v___x_1590_ = leanh::lean_box(0);
                    v_isShared_1591_ = v_isSharedCheck_1610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1592_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1593_ = lean_nat_add(v_startInclusive_1587_, v_pos_1583_);
                leanh::lean_dec(v_startInclusive_1587_);
                if v_isShared_1591_ == 0 {
                    leanh::lean_ctor_set(v___x_1590_, 1, v___x_1593_);
                    v___x_1595_ = v___x_1590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_str_1586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_endExclusive_1588_);
                    v___x_1595_ = v_reuseFailAlloc_1609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_1595_);
                v_searcher_1596_ = leanh::lean_apply_1(v_inst_1585_, v___x_1595_);
                v___x_1597_ = leanh::lean_box(0);
                v___f_1598_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1599_ = leanh::lean_apply_7(
                    v_inst_1581_,
                    v___x_1595_,
                    v___f_1592_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1596_,
                    v___x_1597_,
                    v___f_1598_,
                );
                if leanh::lean_obj_tag(v___x_1599_) == 0 {
                    return v___x_1599_;
                } else {
                    v_val_1600_ = leanh::lean_ctor_get(v___x_1599_, 0);
                    v_isSharedCheck_1608_ = (!leanh::lean_is_exclusive(v___x_1599_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v___x_1602_ = v___x_1599_;
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1600_);
                        leanh::lean_dec(v___x_1599_);
                        v___x_1602_ = leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1604_ = lean_nat_add(v_pos_1583_, v_val_1600_);
                leanh::lean_dec(v_val_1600_);
                if v_isShared_1603_ == 0 {
                    leanh::lean_ctor_set(v___x_1602_, 0, v___x_1604_);
                    v___x_1606_ = v___x_1602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1607_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
                    v___x_1606_ = v_reuseFailAlloc_1607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find_x3f___boxed(
    mut v_00_u03c1_1611_: *mut leanh::LeanObject,
    mut v_00_u03c3_1612_: *mut leanh::LeanObject,
    mut v_inst_1613_: *mut leanh::LeanObject,
    mut v_inst_1614_: *mut leanh::LeanObject,
    mut v_s_1615_: *mut leanh::LeanObject,
    mut v_pos_1616_: *mut leanh::LeanObject,
    mut v_pattern_1617_: *mut leanh::LeanObject,
    mut v_inst_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_String_Slice_Pos_find_x3f(
        v_00_u03c1_1611_,
        v_00_u03c3_1612_,
        v_inst_1613_,
        v_inst_1614_,
        v_s_1615_,
        v_pos_1616_,
        v_pattern_1617_,
        v_inst_1618_,
    );
    leanh::lean_dec(v_pattern_1617_);
    leanh::lean_dec(v_pos_1616_);
    leanh::lean_dec(v_inst_1613_);
    return v_res_1619_;
}
pub unsafe fn l_String_Slice_Pos_find___redArg(
    mut v_inst_1620_: *mut leanh::LeanObject,
    mut v_s_1621_: *mut leanh::LeanObject,
    mut v_pos_1622_: *mut leanh::LeanObject,
    mut v_inst_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___f_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1624_ = leanh::lean_ctor_get(v_s_1621_, 0);
                v_startInclusive_1625_ = leanh::lean_ctor_get(v_s_1621_, 1);
                v_endExclusive_1626_ = leanh::lean_ctor_get(v_s_1621_, 2);
                v_isSharedCheck_1643_ = (!leanh::lean_is_exclusive(v_s_1621_)) as u8;
                if v_isSharedCheck_1643_ == 0 {
                    v___x_1628_ = v_s_1621_;
                    v_isShared_1629_ = v_isSharedCheck_1643_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1626_);
                    leanh::lean_inc(v_startInclusive_1625_);
                    leanh::lean_inc(v_str_1624_);
                    leanh::lean_dec(v_s_1621_);
                    v___x_1628_ = leanh::lean_box(0);
                    v_isShared_1629_ = v_isSharedCheck_1643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1630_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1631_ = lean_nat_add(v_startInclusive_1625_, v_pos_1622_);
                leanh::lean_dec(v_startInclusive_1625_);
                leanh::lean_inc(v_endExclusive_1626_);
                leanh::lean_inc(v___x_1631_);
                if v_isShared_1629_ == 0 {
                    leanh::lean_ctor_set(v___x_1628_, 1, v___x_1631_);
                    v___x_1633_ = v___x_1628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_str_1624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1631_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_endExclusive_1626_);
                    v___x_1633_ = v_reuseFailAlloc_1642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_1633_);
                v_searcher_1634_ = leanh::lean_apply_1(v_inst_1623_, v___x_1633_);
                v___x_1635_ = leanh::lean_box(0);
                v___f_1636_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1637_ = leanh::lean_apply_7(
                    v_inst_1620_,
                    v___x_1633_,
                    v___f_1630_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1634_,
                    v___x_1635_,
                    v___f_1636_,
                );
                if leanh::lean_obj_tag(v___x_1637_) == 0 {
                    v___x_1638_ = lean_nat_sub(v_endExclusive_1626_, v___x_1631_);
                    leanh::lean_dec(v___x_1631_);
                    leanh::lean_dec(v_endExclusive_1626_);
                    v___x_1639_ = lean_nat_add(v_pos_1622_, v___x_1638_);
                    leanh::lean_dec(v___x_1638_);
                    return v___x_1639_;
                } else {
                    leanh::lean_dec(v___x_1631_);
                    leanh::lean_dec(v_endExclusive_1626_);
                    v_val_1640_ = leanh::lean_ctor_get(v___x_1637_, 0);
                    leanh::lean_inc(v_val_1640_);
                    leanh::lean_dec_ref_known(v___x_1637_, 1);
                    v___x_1641_ = lean_nat_add(v_pos_1622_, v_val_1640_);
                    leanh::lean_dec(v_val_1640_);
                    return v___x_1641_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find___redArg___boxed(
    mut v_inst_1644_: *mut leanh::LeanObject,
    mut v_s_1645_: *mut leanh::LeanObject,
    mut v_pos_1646_: *mut leanh::LeanObject,
    mut v_inst_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ =
        l_String_Slice_Pos_find___redArg(v_inst_1644_, v_s_1645_, v_pos_1646_, v_inst_1647_);
    leanh::lean_dec(v_pos_1646_);
    return v_res_1648_;
}
pub unsafe fn l_String_Slice_Pos_find(
    mut v_00_u03c1_1649_: *mut leanh::LeanObject,
    mut v_00_u03c3_1650_: *mut leanh::LeanObject,
    mut v_inst_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_s_1653_: *mut leanh::LeanObject,
    mut v_pos_1654_: *mut leanh::LeanObject,
    mut v_pattern_1655_: *mut leanh::LeanObject,
    mut v_inst_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___f_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1657_ = leanh::lean_ctor_get(v_s_1653_, 0);
                v_startInclusive_1658_ = leanh::lean_ctor_get(v_s_1653_, 1);
                v_endExclusive_1659_ = leanh::lean_ctor_get(v_s_1653_, 2);
                v_isSharedCheck_1676_ = (!leanh::lean_is_exclusive(v_s_1653_)) as u8;
                if v_isSharedCheck_1676_ == 0 {
                    v___x_1661_ = v_s_1653_;
                    v_isShared_1662_ = v_isSharedCheck_1676_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1659_);
                    leanh::lean_inc(v_startInclusive_1658_);
                    leanh::lean_inc(v_str_1657_);
                    leanh::lean_dec(v_s_1653_);
                    v___x_1661_ = leanh::lean_box(0);
                    v_isShared_1662_ = v_isSharedCheck_1676_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1663_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1664_ = lean_nat_add(v_startInclusive_1658_, v_pos_1654_);
                leanh::lean_dec(v_startInclusive_1658_);
                leanh::lean_inc(v_endExclusive_1659_);
                leanh::lean_inc(v___x_1664_);
                if v_isShared_1662_ == 0 {
                    leanh::lean_ctor_set(v___x_1661_, 1, v___x_1664_);
                    v___x_1666_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_str_1657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_endExclusive_1659_);
                    v___x_1666_ = v_reuseFailAlloc_1675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_1666_);
                v_searcher_1667_ = leanh::lean_apply_1(v_inst_1656_, v___x_1666_);
                v___x_1668_ = leanh::lean_box(0);
                v___f_1669_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1670_ = leanh::lean_apply_7(
                    v_inst_1652_,
                    v___x_1666_,
                    v___f_1663_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1667_,
                    v___x_1668_,
                    v___f_1669_,
                );
                if leanh::lean_obj_tag(v___x_1670_) == 0 {
                    v___x_1671_ = lean_nat_sub(v_endExclusive_1659_, v___x_1664_);
                    leanh::lean_dec(v___x_1664_);
                    leanh::lean_dec(v_endExclusive_1659_);
                    v___x_1672_ = lean_nat_add(v_pos_1654_, v___x_1671_);
                    leanh::lean_dec(v___x_1671_);
                    return v___x_1672_;
                } else {
                    leanh::lean_dec(v___x_1664_);
                    leanh::lean_dec(v_endExclusive_1659_);
                    v_val_1673_ = leanh::lean_ctor_get(v___x_1670_, 0);
                    leanh::lean_inc(v_val_1673_);
                    leanh::lean_dec_ref_known(v___x_1670_, 1);
                    v___x_1674_ = lean_nat_add(v_pos_1654_, v_val_1673_);
                    leanh::lean_dec(v_val_1673_);
                    return v___x_1674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find___boxed(
    mut v_00_u03c1_1677_: *mut leanh::LeanObject,
    mut v_00_u03c3_1678_: *mut leanh::LeanObject,
    mut v_inst_1679_: *mut leanh::LeanObject,
    mut v_inst_1680_: *mut leanh::LeanObject,
    mut v_s_1681_: *mut leanh::LeanObject,
    mut v_pos_1682_: *mut leanh::LeanObject,
    mut v_pattern_1683_: *mut leanh::LeanObject,
    mut v_inst_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_String_Slice_Pos_find(
        v_00_u03c1_1677_,
        v_00_u03c3_1678_,
        v_inst_1679_,
        v_inst_1680_,
        v_s_1681_,
        v_pos_1682_,
        v_pattern_1683_,
        v_inst_1684_,
    );
    leanh::lean_dec(v_pattern_1683_);
    leanh::lean_dec(v_pos_1682_);
    leanh::lean_dec(v_inst_1679_);
    return v_res_1685_;
}
pub unsafe fn l_String_Pos_find_x3f___redArg(
    mut v_inst_1686_: *mut leanh::LeanObject,
    mut v_s_1687_: *mut leanh::LeanObject,
    mut v_pos_1688_: *mut leanh::LeanObject,
    mut v_inst_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1690_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1691_ = lean_string_utf8_byte_size(v_s_1687_);
                leanh::lean_inc(v_pos_1688_);
                v___x_1692_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1692_, 0, v_s_1687_);
                leanh::lean_ctor_set(v___x_1692_, 1, v_pos_1688_);
                leanh::lean_ctor_set(v___x_1692_, 2, v___x_1691_);
                leanh::lean_inc_ref(v___x_1692_);
                v_searcher_1693_ = leanh::lean_apply_1(v_inst_1689_, v___x_1692_);
                v___x_1694_ = leanh::lean_box(0);
                v___f_1695_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1696_ = leanh::lean_apply_7(
                    v_inst_1686_,
                    v___x_1692_,
                    v___f_1690_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1693_,
                    v___x_1694_,
                    v___f_1695_,
                );
                if leanh::lean_obj_tag(v___x_1696_) == 0 {
                    leanh::lean_dec(v_pos_1688_);
                    return v___x_1694_;
                } else {
                    v_val_1697_ = leanh::lean_ctor_get(v___x_1696_, 0);
                    v_isSharedCheck_1705_ = (!leanh::lean_is_exclusive(v___x_1696_)) as u8;
                    if v_isSharedCheck_1705_ == 0 {
                        v___x_1699_ = v___x_1696_;
                        v_isShared_1700_ = v_isSharedCheck_1705_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1697_);
                        leanh::lean_dec(v___x_1696_);
                        v___x_1699_ = leanh::lean_box(0);
                        v_isShared_1700_ = v_isSharedCheck_1705_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1701_ = lean_nat_add(v_pos_1688_, v_val_1697_);
                leanh::lean_dec(v_val_1697_);
                leanh::lean_dec(v_pos_1688_);
                if v_isShared_1700_ == 0 {
                    leanh::lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
                    v___x_1703_ = v_reuseFailAlloc_1704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_find_x3f(
    mut v_00_u03c1_1706_: *mut leanh::LeanObject,
    mut v_00_u03c3_1707_: *mut leanh::LeanObject,
    mut v_inst_1708_: *mut leanh::LeanObject,
    mut v_inst_1709_: *mut leanh::LeanObject,
    mut v_s_1710_: *mut leanh::LeanObject,
    mut v_pos_1711_: *mut leanh::LeanObject,
    mut v_pattern_1712_: *mut leanh::LeanObject,
    mut v_inst_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1714_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1715_ = lean_string_utf8_byte_size(v_s_1710_);
                leanh::lean_inc(v_pos_1711_);
                v___x_1716_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1716_, 0, v_s_1710_);
                leanh::lean_ctor_set(v___x_1716_, 1, v_pos_1711_);
                leanh::lean_ctor_set(v___x_1716_, 2, v___x_1715_);
                leanh::lean_inc_ref(v___x_1716_);
                v_searcher_1717_ = leanh::lean_apply_1(v_inst_1713_, v___x_1716_);
                v___x_1718_ = leanh::lean_box(0);
                v___f_1719_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1720_ = leanh::lean_apply_7(
                    v_inst_1709_,
                    v___x_1716_,
                    v___f_1714_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1717_,
                    v___x_1718_,
                    v___f_1719_,
                );
                if leanh::lean_obj_tag(v___x_1720_) == 0 {
                    leanh::lean_dec(v_pos_1711_);
                    return v___x_1718_;
                } else {
                    v_val_1721_ = leanh::lean_ctor_get(v___x_1720_, 0);
                    v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v___x_1720_)) as u8;
                    if v_isSharedCheck_1729_ == 0 {
                        v___x_1723_ = v___x_1720_;
                        v_isShared_1724_ = v_isSharedCheck_1729_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1721_);
                        leanh::lean_dec(v___x_1720_);
                        v___x_1723_ = leanh::lean_box(0);
                        v_isShared_1724_ = v_isSharedCheck_1729_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1725_ = lean_nat_add(v_pos_1711_, v_val_1721_);
                leanh::lean_dec(v_val_1721_);
                leanh::lean_dec(v_pos_1711_);
                if v_isShared_1724_ == 0 {
                    leanh::lean_ctor_set(v___x_1723_, 0, v___x_1725_);
                    v___x_1727_ = v___x_1723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
                    v___x_1727_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_find_x3f___boxed(
    mut v_00_u03c1_1730_: *mut leanh::LeanObject,
    mut v_00_u03c3_1731_: *mut leanh::LeanObject,
    mut v_inst_1732_: *mut leanh::LeanObject,
    mut v_inst_1733_: *mut leanh::LeanObject,
    mut v_s_1734_: *mut leanh::LeanObject,
    mut v_pos_1735_: *mut leanh::LeanObject,
    mut v_pattern_1736_: *mut leanh::LeanObject,
    mut v_inst_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1738_ = l_String_Pos_find_x3f(
        v_00_u03c1_1730_,
        v_00_u03c3_1731_,
        v_inst_1732_,
        v_inst_1733_,
        v_s_1734_,
        v_pos_1735_,
        v_pattern_1736_,
        v_inst_1737_,
    );
    leanh::lean_dec(v_pattern_1736_);
    leanh::lean_dec(v_inst_1732_);
    return v_res_1738_;
}
pub unsafe fn l_String_Pos_find___redArg(
    mut v_inst_1739_: *mut leanh::LeanObject,
    mut v_s_1740_: *mut leanh::LeanObject,
    mut v_pos_1741_: *mut leanh::LeanObject,
    mut v_inst_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1743_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1744_ = lean_string_utf8_byte_size(v_s_1740_);
    leanh::lean_inc(v_pos_1741_);
    v___x_1745_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v_s_1740_);
    leanh::lean_ctor_set(v___x_1745_, 1, v_pos_1741_);
    leanh::lean_ctor_set(v___x_1745_, 2, v___x_1744_);
    leanh::lean_inc_ref(v___x_1745_);
    v_searcher_1746_ = leanh::lean_apply_1(v_inst_1742_, v___x_1745_);
    v___x_1747_ = leanh::lean_box(0);
    v___f_1748_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1749_ = leanh::lean_apply_7(
        v_inst_1739_,
        v___x_1745_,
        v___f_1743_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_searcher_1746_,
        v___x_1747_,
        v___f_1748_,
    );
    if leanh::lean_obj_tag(v___x_1749_) == 0 {
        let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1750_ = lean_nat_sub(v___x_1744_, v_pos_1741_);
        v___x_1751_ = lean_nat_add(v_pos_1741_, v___x_1750_);
        leanh::lean_dec(v___x_1750_);
        leanh::lean_dec(v_pos_1741_);
        return v___x_1751_;
    } else {
        let mut v_val_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1752_ = leanh::lean_ctor_get(v___x_1749_, 0);
        leanh::lean_inc(v_val_1752_);
        leanh::lean_dec_ref_known(v___x_1749_, 1);
        v___x_1753_ = lean_nat_add(v_pos_1741_, v_val_1752_);
        leanh::lean_dec(v_val_1752_);
        leanh::lean_dec(v_pos_1741_);
        return v___x_1753_;
    }
}
pub unsafe fn l_String_Pos_find(
    mut v_00_u03c1_1754_: *mut leanh::LeanObject,
    mut v_00_u03c3_1755_: *mut leanh::LeanObject,
    mut v_inst_1756_: *mut leanh::LeanObject,
    mut v_inst_1757_: *mut leanh::LeanObject,
    mut v_s_1758_: *mut leanh::LeanObject,
    mut v_pos_1759_: *mut leanh::LeanObject,
    mut v_pattern_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1762_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1763_ = lean_string_utf8_byte_size(v_s_1758_);
    leanh::lean_inc(v_pos_1759_);
    v___x_1764_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1764_, 0, v_s_1758_);
    leanh::lean_ctor_set(v___x_1764_, 1, v_pos_1759_);
    leanh::lean_ctor_set(v___x_1764_, 2, v___x_1763_);
    leanh::lean_inc_ref(v___x_1764_);
    v_searcher_1765_ = leanh::lean_apply_1(v_inst_1761_, v___x_1764_);
    v___x_1766_ = leanh::lean_box(0);
    v___f_1767_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1768_ = leanh::lean_apply_7(
        v_inst_1757_,
        v___x_1764_,
        v___f_1762_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_searcher_1765_,
        v___x_1766_,
        v___f_1767_,
    );
    if leanh::lean_obj_tag(v___x_1768_) == 0 {
        let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1769_ = lean_nat_sub(v___x_1763_, v_pos_1759_);
        v___x_1770_ = lean_nat_add(v_pos_1759_, v___x_1769_);
        leanh::lean_dec(v___x_1769_);
        leanh::lean_dec(v_pos_1759_);
        return v___x_1770_;
    } else {
        let mut v_val_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1771_ = leanh::lean_ctor_get(v___x_1768_, 0);
        leanh::lean_inc(v_val_1771_);
        leanh::lean_dec_ref_known(v___x_1768_, 1);
        v___x_1772_ = lean_nat_add(v_pos_1759_, v_val_1771_);
        leanh::lean_dec(v_val_1771_);
        leanh::lean_dec(v_pos_1759_);
        return v___x_1772_;
    }
}
pub unsafe fn l_String_Pos_find___boxed(
    mut v_00_u03c1_1773_: *mut leanh::LeanObject,
    mut v_00_u03c3_1774_: *mut leanh::LeanObject,
    mut v_inst_1775_: *mut leanh::LeanObject,
    mut v_inst_1776_: *mut leanh::LeanObject,
    mut v_s_1777_: *mut leanh::LeanObject,
    mut v_pos_1778_: *mut leanh::LeanObject,
    mut v_pattern_1779_: *mut leanh::LeanObject,
    mut v_inst_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_String_Pos_find(
        v_00_u03c1_1773_,
        v_00_u03c3_1774_,
        v_inst_1775_,
        v_inst_1776_,
        v_s_1777_,
        v_pos_1778_,
        v_pattern_1779_,
        v_inst_1780_,
    );
    leanh::lean_dec(v_pattern_1779_);
    leanh::lean_dec(v_inst_1775_);
    return v_res_1781_;
}
pub unsafe fn l_String_find_x3f___redArg(
    mut v_inst_1782_: *mut leanh::LeanObject,
    mut v_s_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1785_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1786_ = leanh::lean_unsigned_to_nat(0);
                v___x_1787_ = lean_string_utf8_byte_size(v_s_1783_);
                v___x_1788_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1788_, 0, v_s_1783_);
                leanh::lean_ctor_set(v___x_1788_, 1, v___x_1786_);
                leanh::lean_ctor_set(v___x_1788_, 2, v___x_1787_);
                leanh::lean_inc_ref(v___x_1788_);
                v_searcher_1789_ = leanh::lean_apply_1(v_inst_1784_, v___x_1788_);
                v___x_1790_ = leanh::lean_box(0);
                v___f_1791_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1792_ = leanh::lean_apply_7(
                    v_inst_1782_,
                    v___x_1788_,
                    v___f_1785_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1789_,
                    v___x_1790_,
                    v___f_1791_,
                );
                if leanh::lean_obj_tag(v___x_1792_) == 0 {
                    return v___x_1790_;
                } else {
                    v_val_1793_ = leanh::lean_ctor_get(v___x_1792_, 0);
                    v_isSharedCheck_1800_ = (!leanh::lean_is_exclusive(v___x_1792_)) as u8;
                    if v_isSharedCheck_1800_ == 0 {
                        v___x_1795_ = v___x_1792_;
                        v_isShared_1796_ = v_isSharedCheck_1800_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1793_);
                        leanh::lean_dec(v___x_1792_);
                        v___x_1795_ = leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1800_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1796_ == 0 {
                    v___x_1798_ = v___x_1795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_val_1793_);
                    v___x_1798_ = v_reuseFailAlloc_1799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_find_x3f(
    mut v_00_u03c1_1801_: *mut leanh::LeanObject,
    mut v_00_u03c3_1802_: *mut leanh::LeanObject,
    mut v_inst_1803_: *mut leanh::LeanObject,
    mut v_inst_1804_: *mut leanh::LeanObject,
    mut v_s_1805_: *mut leanh::LeanObject,
    mut v_pattern_1806_: *mut leanh::LeanObject,
    mut v_inst_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1808_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1809_ = leanh::lean_unsigned_to_nat(0);
                v___x_1810_ = lean_string_utf8_byte_size(v_s_1805_);
                v___x_1811_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1811_, 0, v_s_1805_);
                leanh::lean_ctor_set(v___x_1811_, 1, v___x_1809_);
                leanh::lean_ctor_set(v___x_1811_, 2, v___x_1810_);
                leanh::lean_inc_ref(v___x_1811_);
                v_searcher_1812_ = leanh::lean_apply_1(v_inst_1807_, v___x_1811_);
                v___x_1813_ = leanh::lean_box(0);
                v___f_1814_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1815_ = leanh::lean_apply_7(
                    v_inst_1804_,
                    v___x_1811_,
                    v___f_1808_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_searcher_1812_,
                    v___x_1813_,
                    v___f_1814_,
                );
                if leanh::lean_obj_tag(v___x_1815_) == 0 {
                    return v___x_1813_;
                } else {
                    v_val_1816_ = leanh::lean_ctor_get(v___x_1815_, 0);
                    v_isSharedCheck_1823_ = (!leanh::lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1815_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1816_);
                        leanh::lean_dec(v___x_1815_);
                        v___x_1818_ = leanh::lean_box(0);
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_find_x3f___boxed(
    mut v_00_u03c1_1824_: *mut leanh::LeanObject,
    mut v_00_u03c3_1825_: *mut leanh::LeanObject,
    mut v_inst_1826_: *mut leanh::LeanObject,
    mut v_inst_1827_: *mut leanh::LeanObject,
    mut v_s_1828_: *mut leanh::LeanObject,
    mut v_pattern_1829_: *mut leanh::LeanObject,
    mut v_inst_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_String_find_x3f(
        v_00_u03c1_1824_,
        v_00_u03c3_1825_,
        v_inst_1826_,
        v_inst_1827_,
        v_s_1828_,
        v_pattern_1829_,
        v_inst_1830_,
    );
    leanh::lean_dec(v_pattern_1829_);
    leanh::lean_dec(v_inst_1826_);
    return v_res_1831_;
}
pub unsafe fn l_String_find___redArg(
    mut v_inst_1832_: *mut leanh::LeanObject,
    mut v_s_1833_: *mut leanh::LeanObject,
    mut v_inst_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1835_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1836_ = leanh::lean_unsigned_to_nat(0);
    v___x_1837_ = lean_string_utf8_byte_size(v_s_1833_);
    v___x_1838_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1838_, 0, v_s_1833_);
    leanh::lean_ctor_set(v___x_1838_, 1, v___x_1836_);
    leanh::lean_ctor_set(v___x_1838_, 2, v___x_1837_);
    leanh::lean_inc_ref(v___x_1838_);
    v_searcher_1839_ = leanh::lean_apply_1(v_inst_1834_, v___x_1838_);
    v___x_1840_ = leanh::lean_box(0);
    v___f_1841_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1842_ = leanh::lean_apply_7(
        v_inst_1832_,
        v___x_1838_,
        v___f_1835_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_searcher_1839_,
        v___x_1840_,
        v___f_1841_,
    );
    if leanh::lean_obj_tag(v___x_1842_) == 0 {
        return v___x_1837_;
    } else {
        let mut v_val_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1843_ = leanh::lean_ctor_get(v___x_1842_, 0);
        leanh::lean_inc(v_val_1843_);
        leanh::lean_dec_ref_known(v___x_1842_, 1);
        return v_val_1843_;
    }
}
pub unsafe fn l_String_find(
    mut v_00_u03c1_1844_: *mut leanh::LeanObject,
    mut v_00_u03c3_1845_: *mut leanh::LeanObject,
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_inst_1847_: *mut leanh::LeanObject,
    mut v_s_1848_: *mut leanh::LeanObject,
    mut v_pattern_1849_: *mut leanh::LeanObject,
    mut v_inst_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1851_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1852_ = leanh::lean_unsigned_to_nat(0);
    v___x_1853_ = lean_string_utf8_byte_size(v_s_1848_);
    v___x_1854_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1854_, 0, v_s_1848_);
    leanh::lean_ctor_set(v___x_1854_, 1, v___x_1852_);
    leanh::lean_ctor_set(v___x_1854_, 2, v___x_1853_);
    leanh::lean_inc_ref(v___x_1854_);
    v_searcher_1855_ = leanh::lean_apply_1(v_inst_1850_, v___x_1854_);
    v___x_1856_ = leanh::lean_box(0);
    v___f_1857_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1858_ = leanh::lean_apply_7(
        v_inst_1847_,
        v___x_1854_,
        v___f_1851_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_searcher_1855_,
        v___x_1856_,
        v___f_1857_,
    );
    if leanh::lean_obj_tag(v___x_1858_) == 0 {
        return v___x_1853_;
    } else {
        let mut v_val_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1859_ = leanh::lean_ctor_get(v___x_1858_, 0);
        leanh::lean_inc(v_val_1859_);
        leanh::lean_dec_ref_known(v___x_1858_, 1);
        return v_val_1859_;
    }
}
pub unsafe fn l_String_find___boxed(
    mut v_00_u03c1_1860_: *mut leanh::LeanObject,
    mut v_00_u03c3_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_inst_1863_: *mut leanh::LeanObject,
    mut v_s_1864_: *mut leanh::LeanObject,
    mut v_pattern_1865_: *mut leanh::LeanObject,
    mut v_inst_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_String_find(
        v_00_u03c1_1860_,
        v_00_u03c3_1861_,
        v_inst_1862_,
        v_inst_1863_,
        v_s_1864_,
        v_pattern_1865_,
        v_inst_1866_,
    );
    leanh::lean_dec(v_pattern_1865_);
    leanh::lean_dec(v_inst_1862_);
    return v_res_1867_;
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f___redArg(
    mut v_inst_1868_: *mut leanh::LeanObject,
    mut v_s_1869_: *mut leanh::LeanObject,
    mut v_pos_1870_: *mut leanh::LeanObject,
    mut v_inst_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut v_reuseFailAlloc_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut v_unused_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1872_ = leanh::lean_ctor_get(v_s_1869_, 0);
                v_startInclusive_1873_ = leanh::lean_ctor_get(v_s_1869_, 1);
                v_isSharedCheck_1890_ = (!leanh::lean_is_exclusive(v_s_1869_)) as u8;
                if v_isSharedCheck_1890_ == 0 {
                    v_unused_1891_ = leanh::lean_ctor_get(v_s_1869_, 2);
                    leanh::lean_dec(v_unused_1891_);
                    v___x_1875_ = v_s_1869_;
                    v_isShared_1876_ = v_isSharedCheck_1890_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_startInclusive_1873_);
                    leanh::lean_inc(v_str_1872_);
                    leanh::lean_dec(v_s_1869_);
                    v___x_1875_ = leanh::lean_box(0);
                    v_isShared_1876_ = v_isSharedCheck_1890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1877_ = lean_nat_add(v_startInclusive_1873_, v_pos_1870_);
                if v_isShared_1876_ == 0 {
                    leanh::lean_ctor_set(v___x_1875_, 2, v___x_1877_);
                    v___x_1879_ = v___x_1875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1889_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_str_1872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_startInclusive_1873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 2, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1880_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1868_, v___x_1879_, v_inst_1871_);
                if leanh::lean_obj_tag(v___x_1880_) == 0 {
                    return v___x_1880_;
                } else {
                    v_val_1881_ = leanh::lean_ctor_get(v___x_1880_, 0);
                    v_isSharedCheck_1888_ = (!leanh::lean_is_exclusive(v___x_1880_)) as u8;
                    if v_isSharedCheck_1888_ == 0 {
                        v___x_1883_ = v___x_1880_;
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1881_);
                        leanh::lean_dec(v___x_1880_);
                        v___x_1883_ = leanh::lean_box(0);
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1884_ == 0 {
                    v___x_1886_ = v___x_1883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_val_1881_);
                    v___x_1886_ = v_reuseFailAlloc_1887_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f___redArg___boxed(
    mut v_inst_1892_: *mut leanh::LeanObject,
    mut v_s_1893_: *mut leanh::LeanObject,
    mut v_pos_1894_: *mut leanh::LeanObject,
    mut v_inst_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1896_ =
        l_String_Slice_Pos_revFind_x3f___redArg(v_inst_1892_, v_s_1893_, v_pos_1894_, v_inst_1895_);
    leanh::lean_dec(v_pos_1894_);
    return v_res_1896_;
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f(
    mut v_00_u03c1_1897_: *mut leanh::LeanObject,
    mut v_00_u03c3_1898_: *mut leanh::LeanObject,
    mut v_inst_1899_: *mut leanh::LeanObject,
    mut v_inst_1900_: *mut leanh::LeanObject,
    mut v_s_1901_: *mut leanh::LeanObject,
    mut v_pos_1902_: *mut leanh::LeanObject,
    mut v_pattern_1903_: *mut leanh::LeanObject,
    mut v_inst_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v_unused_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1905_ = leanh::lean_ctor_get(v_s_1901_, 0);
                v_startInclusive_1906_ = leanh::lean_ctor_get(v_s_1901_, 1);
                v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v_s_1901_)) as u8;
                if v_isSharedCheck_1923_ == 0 {
                    v_unused_1924_ = leanh::lean_ctor_get(v_s_1901_, 2);
                    leanh::lean_dec(v_unused_1924_);
                    v___x_1908_ = v_s_1901_;
                    v_isShared_1909_ = v_isSharedCheck_1923_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_startInclusive_1906_);
                    leanh::lean_inc(v_str_1905_);
                    leanh::lean_dec(v_s_1901_);
                    v___x_1908_ = leanh::lean_box(0);
                    v_isShared_1909_ = v_isSharedCheck_1923_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = lean_nat_add(v_startInclusive_1906_, v_pos_1902_);
                if v_isShared_1909_ == 0 {
                    leanh::lean_ctor_set(v___x_1908_, 2, v___x_1910_);
                    v___x_1912_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_str_1905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_startInclusive_1906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 2, v___x_1910_);
                    v___x_1912_ = v_reuseFailAlloc_1922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1913_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1900_, v___x_1912_, v_inst_1904_);
                if leanh::lean_obj_tag(v___x_1913_) == 0 {
                    return v___x_1913_;
                } else {
                    v_val_1914_ = leanh::lean_ctor_get(v___x_1913_, 0);
                    v_isSharedCheck_1921_ = (!leanh::lean_is_exclusive(v___x_1913_)) as u8;
                    if v_isSharedCheck_1921_ == 0 {
                        v___x_1916_ = v___x_1913_;
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1914_);
                        leanh::lean_dec(v___x_1913_);
                        v___x_1916_ = leanh::lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1917_ == 0 {
                    v___x_1919_ = v___x_1916_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_val_1914_);
                    v___x_1919_ = v_reuseFailAlloc_1920_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f___boxed(
    mut v_00_u03c1_1925_: *mut leanh::LeanObject,
    mut v_00_u03c3_1926_: *mut leanh::LeanObject,
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_inst_1928_: *mut leanh::LeanObject,
    mut v_s_1929_: *mut leanh::LeanObject,
    mut v_pos_1930_: *mut leanh::LeanObject,
    mut v_pattern_1931_: *mut leanh::LeanObject,
    mut v_inst_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_String_Slice_Pos_revFind_x3f(
        v_00_u03c1_1925_,
        v_00_u03c3_1926_,
        v_inst_1927_,
        v_inst_1928_,
        v_s_1929_,
        v_pos_1930_,
        v_pattern_1931_,
        v_inst_1932_,
    );
    leanh::lean_dec(v_pattern_1931_);
    leanh::lean_dec(v_pos_1930_);
    leanh::lean_dec(v_inst_1927_);
    return v_res_1933_;
}
pub unsafe fn l_String_Pos_revFind_x3f___redArg(
    mut v_inst_1934_: *mut leanh::LeanObject,
    mut v_s_1935_: *mut leanh::LeanObject,
    mut v_pos_1936_: *mut leanh::LeanObject,
    mut v_inst_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1938_ = leanh::lean_unsigned_to_nat(0);
                v___x_1939_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1939_, 0, v_s_1935_);
                leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                leanh::lean_ctor_set(v___x_1939_, 2, v_pos_1936_);
                v___x_1940_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1934_, v___x_1939_, v_inst_1937_);
                if leanh::lean_obj_tag(v___x_1940_) == 0 {
                    if leanh::lean_obj_tag(v___x_1940_) == 0 {
                        v___x_1941_ = leanh::lean_box(0);
                        return v___x_1941_;
                    } else {
                        v_val_1942_ = leanh::lean_ctor_get(v___x_1940_, 0);
                        leanh::lean_inc(v_val_1942_);
                        leanh::lean_dec_ref_known(v___x_1940_, 1);
                        v___x_1943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1943_, 0, v_val_1942_);
                        return v___x_1943_;
                    }
                } else {
                    v_val_1944_ = leanh::lean_ctor_get(v___x_1940_, 0);
                    v_isSharedCheck_1951_ = (!leanh::lean_is_exclusive(v___x_1940_)) as u8;
                    if v_isSharedCheck_1951_ == 0 {
                        v___x_1946_ = v___x_1940_;
                        v_isShared_1947_ = v_isSharedCheck_1951_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1944_);
                        leanh::lean_dec(v___x_1940_);
                        v___x_1946_ = leanh::lean_box(0);
                        v_isShared_1947_ = v_isSharedCheck_1951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1947_ == 0 {
                    v___x_1949_ = v___x_1946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_val_1944_);
                    v___x_1949_ = v_reuseFailAlloc_1950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_revFind_x3f(
    mut v_00_u03c1_1952_: *mut leanh::LeanObject,
    mut v_00_u03c3_1953_: *mut leanh::LeanObject,
    mut v_inst_1954_: *mut leanh::LeanObject,
    mut v_inst_1955_: *mut leanh::LeanObject,
    mut v_s_1956_: *mut leanh::LeanObject,
    mut v_pos_1957_: *mut leanh::LeanObject,
    mut v_pattern_1958_: *mut leanh::LeanObject,
    mut v_inst_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1960_ = leanh::lean_unsigned_to_nat(0);
                v___x_1961_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1961_, 0, v_s_1956_);
                leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
                leanh::lean_ctor_set(v___x_1961_, 2, v_pos_1957_);
                v___x_1962_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1955_, v___x_1961_, v_inst_1959_);
                if leanh::lean_obj_tag(v___x_1962_) == 0 {
                    if leanh::lean_obj_tag(v___x_1962_) == 0 {
                        v___x_1963_ = leanh::lean_box(0);
                        return v___x_1963_;
                    } else {
                        v_val_1964_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        leanh::lean_inc(v_val_1964_);
                        leanh::lean_dec_ref_known(v___x_1962_, 1);
                        v___x_1965_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1965_, 0, v_val_1964_);
                        return v___x_1965_;
                    }
                } else {
                    v_val_1966_ = leanh::lean_ctor_get(v___x_1962_, 0);
                    v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v___x_1962_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1962_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1966_);
                        leanh::lean_dec(v___x_1962_);
                        v___x_1968_ = leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_val_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_revFind_x3f___boxed(
    mut v_00_u03c1_1974_: *mut leanh::LeanObject,
    mut v_00_u03c3_1975_: *mut leanh::LeanObject,
    mut v_inst_1976_: *mut leanh::LeanObject,
    mut v_inst_1977_: *mut leanh::LeanObject,
    mut v_s_1978_: *mut leanh::LeanObject,
    mut v_pos_1979_: *mut leanh::LeanObject,
    mut v_pattern_1980_: *mut leanh::LeanObject,
    mut v_inst_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1982_ = l_String_Pos_revFind_x3f(
        v_00_u03c1_1974_,
        v_00_u03c3_1975_,
        v_inst_1976_,
        v_inst_1977_,
        v_s_1978_,
        v_pos_1979_,
        v_pattern_1980_,
        v_inst_1981_,
    );
    leanh::lean_dec(v_pattern_1980_);
    leanh::lean_dec(v_inst_1976_);
    return v_res_1982_;
}
pub unsafe fn l_String_revFind_x3f___redArg(
    mut v_inst_1983_: *mut leanh::LeanObject,
    mut v_s_1984_: *mut leanh::LeanObject,
    mut v_inst_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1986_ = leanh::lean_unsigned_to_nat(0);
                v___x_1987_ = lean_string_utf8_byte_size(v_s_1984_);
                v___x_1988_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1988_, 0, v_s_1984_);
                leanh::lean_ctor_set(v___x_1988_, 1, v___x_1986_);
                leanh::lean_ctor_set(v___x_1988_, 2, v___x_1987_);
                v___x_1989_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1983_, v___x_1988_, v_inst_1985_);
                if leanh::lean_obj_tag(v___x_1989_) == 0 {
                    v___x_1990_ = leanh::lean_box(0);
                    return v___x_1990_;
                } else {
                    v_val_1991_ = leanh::lean_ctor_get(v___x_1989_, 0);
                    v_isSharedCheck_1998_ = (!leanh::lean_is_exclusive(v___x_1989_)) as u8;
                    if v_isSharedCheck_1998_ == 0 {
                        v___x_1993_ = v___x_1989_;
                        v_isShared_1994_ = v_isSharedCheck_1998_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1991_);
                        leanh::lean_dec(v___x_1989_);
                        v___x_1993_ = leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_1998_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1994_ == 0 {
                    v___x_1996_ = v___x_1993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_val_1991_);
                    v___x_1996_ = v_reuseFailAlloc_1997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_revFind_x3f(
    mut v_00_u03c1_1999_: *mut leanh::LeanObject,
    mut v_00_u03c3_2000_: *mut leanh::LeanObject,
    mut v_inst_2001_: *mut leanh::LeanObject,
    mut v_inst_2002_: *mut leanh::LeanObject,
    mut v_s_2003_: *mut leanh::LeanObject,
    mut v_pattern_2004_: *mut leanh::LeanObject,
    mut v_inst_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = leanh::lean_unsigned_to_nat(0);
                v___x_2007_ = lean_string_utf8_byte_size(v_s_2003_);
                v___x_2008_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2008_, 0, v_s_2003_);
                leanh::lean_ctor_set(v___x_2008_, 1, v___x_2006_);
                leanh::lean_ctor_set(v___x_2008_, 2, v___x_2007_);
                v___x_2009_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_2002_, v___x_2008_, v_inst_2005_);
                if leanh::lean_obj_tag(v___x_2009_) == 0 {
                    v___x_2010_ = leanh::lean_box(0);
                    return v___x_2010_;
                } else {
                    v_val_2011_ = leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2018_ = (!leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_2009_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2011_);
                        leanh::lean_dec(v___x_2009_);
                        v___x_2013_ = leanh::lean_box(0);
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2014_ == 0 {
                    v___x_2016_ = v___x_2013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_val_2011_);
                    v___x_2016_ = v_reuseFailAlloc_2017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_revFind_x3f___boxed(
    mut v_00_u03c1_2019_: *mut leanh::LeanObject,
    mut v_00_u03c3_2020_: *mut leanh::LeanObject,
    mut v_inst_2021_: *mut leanh::LeanObject,
    mut v_inst_2022_: *mut leanh::LeanObject,
    mut v_s_2023_: *mut leanh::LeanObject,
    mut v_pattern_2024_: *mut leanh::LeanObject,
    mut v_inst_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_String_revFind_x3f(
        v_00_u03c1_2019_,
        v_00_u03c3_2020_,
        v_inst_2021_,
        v_inst_2022_,
        v_s_2023_,
        v_pattern_2024_,
        v_inst_2025_,
    );
    leanh::lean_dec(v_pattern_2024_);
    leanh::lean_dec(v_inst_2021_);
    return v_res_2026_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
    mut v___x_2027_: *mut leanh::LeanObject,
    mut v_s_2028_: *mut leanh::LeanObject,
    mut v_c_2029_: u32,
    mut v_a_2030_: *mut leanh::LeanObject,
    mut v_b_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: u32 = 0;
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2032_ = leanh::lean_ctor_get(v___x_2027_, 1);
                v_endExclusive_2033_ = leanh::lean_ctor_get(v___x_2027_, 2);
                v___x_2034_ = lean_nat_sub(v_endExclusive_2033_, v_startInclusive_2032_);
                v___x_2035_ = lean_nat_dec_eq(v_a_2030_, v___x_2034_);
                leanh::lean_dec(v___x_2034_);
                if v___x_2035_ == 0 {
                    v___x_2036_ = lean_string_utf8_get_fast(v_s_2028_, v_a_2030_);
                    v___x_2037_ = lean_uint32_dec_eq(v___x_2036_, v_c_2029_);
                    if v___x_2037_ == 0 {
                        v___x_2038_ = leanh::lean_box(0);
                        v___x_2039_ = lean_string_utf8_next_fast(v_s_2028_, v_a_2030_);
                        leanh::lean_dec(v_a_2030_);
                        v_a_2030_ = v___x_2039_;
                        v_b_2031_ = v___x_2038_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2041_, 0, v_a_2030_);
                        return v___x_2041_;
                    }
                } else {
                    leanh::lean_dec(v_a_2030_);
                    leanh::lean_inc(v_b_2031_);
                    return v_b_2031_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(
    mut v___x_2042_: *mut leanh::LeanObject,
    mut v_s_2043_: *mut leanh::LeanObject,
    mut v_c_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_b_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2047_: u32 = 0;
    let mut v_res_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2047_ = leanh::lean_unbox_uint32(v_c_2044_);
    leanh::lean_dec(v_c_2044_);
    v_res_2048_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2042_,
        v_s_2043_,
        v_c_boxed_2047_,
        v_a_2045_,
        v_b_2046_,
    );
    leanh::lean_dec(v_b_2046_);
    leanh::lean_dec_ref(v_s_2043_);
    leanh::lean_dec_ref(v___x_2042_);
    return v_res_2048_;
}
pub unsafe fn lean_string_posof(
    mut v_s_2049_: *mut leanh::LeanObject,
    mut v_c_2050_: u32,
) -> *mut leanh::LeanObject {
    let mut v_searcher_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_searcher_2051_ = leanh::lean_unsigned_to_nat(0);
    v___x_2052_ = lean_string_utf8_byte_size(v_s_2049_);
    leanh::lean_inc_ref(v_s_2049_);
    v___x_2053_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2053_, 0, v_s_2049_);
    leanh::lean_ctor_set(v___x_2053_, 1, v_searcher_2051_);
    leanh::lean_ctor_set(v___x_2053_, 2, v___x_2052_);
    v___x_2054_ = leanh::lean_box(0);
    v___x_2055_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2053_,
        v_s_2049_,
        v_c_2050_,
        v_searcher_2051_,
        v___x_2054_,
    );
    leanh::lean_dec_ref(v_s_2049_);
    leanh::lean_dec_ref_known(v___x_2053_, 3);
    if leanh::lean_obj_tag(v___x_2055_) == 0 {
        return v___x_2052_;
    } else {
        let mut v_val_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2056_ = leanh::lean_ctor_get(v___x_2055_, 0);
        leanh::lean_inc(v_val_2056_);
        leanh::lean_dec_ref_known(v___x_2055_, 1);
        return v_val_2056_;
    }
}
pub unsafe fn l_String_Internal_posOfImpl___boxed(
    mut v_s_2057_: *mut leanh::LeanObject,
    mut v_c_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2059_: u32 = 0;
    let mut v_res_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2059_ = leanh::lean_unbox_uint32(v_c_2058_);
    leanh::lean_dec(v_c_2058_);
    v_res_2060_ = lean_string_posof(v_s_2057_, v_c_boxed_2059_);
    return v_res_2060_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(
    mut v___x_2061_: *mut leanh::LeanObject,
    mut v_s_2062_: *mut leanh::LeanObject,
    mut v_c_2063_: u32,
    mut v_inst_2064_: *mut leanh::LeanObject,
    mut v_R_2065_: *mut leanh::LeanObject,
    mut v_a_2066_: *mut leanh::LeanObject,
    mut v_b_2067_: *mut leanh::LeanObject,
    mut v_c_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2061_,
        v_s_2062_,
        v_c_2063_,
        v_a_2066_,
        v_b_2067_,
    );
    return v___x_2069_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___boxed(
    mut v___x_2070_: *mut leanh::LeanObject,
    mut v_s_2071_: *mut leanh::LeanObject,
    mut v_c_2072_: *mut leanh::LeanObject,
    mut v_inst_2073_: *mut leanh::LeanObject,
    mut v_R_2074_: *mut leanh::LeanObject,
    mut v_a_2075_: *mut leanh::LeanObject,
    mut v_b_2076_: *mut leanh::LeanObject,
    mut v_c_2077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2078_: u32 = 0;
    let mut v_res_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2078_ = leanh::lean_unbox_uint32(v_c_2072_);
    leanh::lean_dec(v_c_2072_);
    v_res_2079_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(
        v___x_2070_,
        v_s_2071_,
        v_c_boxed_2078_,
        v_inst_2073_,
        v_R_2074_,
        v_a_2075_,
        v_b_2076_,
        v_c_2077_,
    );
    leanh::lean_dec(v_b_2076_);
    leanh::lean_dec_ref(v_s_2071_);
    leanh::lean_dec_ref(v___x_2070_);
    return v_res_2079_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
    mut v___x_2080_: *mut leanh::LeanObject,
    mut v_pos_2081_: *mut leanh::LeanObject,
    mut v_s_2082_: *mut leanh::LeanObject,
    mut v_p_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
    mut v_b_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u32 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2086_ = leanh::lean_ctor_get(v___x_2080_, 1);
                v_endExclusive_2087_ = leanh::lean_ctor_get(v___x_2080_, 2);
                v___x_2088_ = lean_nat_sub(v_endExclusive_2087_, v_startInclusive_2086_);
                v___x_2089_ = lean_nat_dec_eq(v_a_2084_, v___x_2088_);
                leanh::lean_dec(v___x_2088_);
                if v___x_2089_ == 0 {
                    v___x_2090_ = lean_nat_add(v_pos_2081_, v_a_2084_);
                    v___x_2091_ = lean_string_utf8_get_fast(v_s_2082_, v___x_2090_);
                    v___x_2092_ = leanh::lean_box_uint32(v___x_2091_);
                    leanh::lean_inc_ref(v_p_2083_);
                    v___x_2093_ = leanh::lean_apply_1(v_p_2083_, v___x_2092_);
                    v___x_2094_ = (leanh::lean_unbox(v___x_2093_) as u8);
                    if v___x_2094_ == 0 {
                        leanh::lean_dec(v_a_2084_);
                        v___x_2095_ = leanh::lean_box(0);
                        v___x_2096_ = lean_string_utf8_next_fast(v_s_2082_, v___x_2090_);
                        leanh::lean_dec(v___x_2090_);
                        v___x_2097_ = lean_nat_sub(v___x_2096_, v_pos_2081_);
                        v_a_2084_ = v___x_2097_;
                        v_b_2085_ = v___x_2095_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2090_);
                        leanh::lean_dec_ref(v_p_2083_);
                        v___x_2099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2099_, 0, v_a_2084_);
                        return v___x_2099_;
                    }
                } else {
                    leanh::lean_dec(v_a_2084_);
                    leanh::lean_dec_ref(v_p_2083_);
                    leanh::lean_inc(v_b_2085_);
                    return v_b_2085_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg___boxed(
    mut v___x_2100_: *mut leanh::LeanObject,
    mut v_pos_2101_: *mut leanh::LeanObject,
    mut v_s_2102_: *mut leanh::LeanObject,
    mut v_p_2103_: *mut leanh::LeanObject,
    mut v_a_2104_: *mut leanh::LeanObject,
    mut v_b_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
        v___x_2100_,
        v_pos_2101_,
        v_s_2102_,
        v_p_2103_,
        v_a_2104_,
        v_b_2105_,
    );
    leanh::lean_dec(v_b_2105_);
    leanh::lean_dec_ref(v_s_2102_);
    leanh::lean_dec(v_pos_2101_);
    leanh::lean_dec_ref(v___x_2100_);
    return v_res_2106_;
}
pub unsafe fn l_String_findAux(
    mut v_s_2107_: *mut leanh::LeanObject,
    mut v_p_2108_: *mut leanh::LeanObject,
    mut v_stopPos_2109_: *mut leanh::LeanObject,
    mut v_pos_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2111_: u8 = 0;
    v___x_2111_ = lean_nat_dec_le(v_pos_2110_, v_stopPos_2109_);
    if v___x_2111_ == 0 {
        leanh::lean_dec(v_pos_2110_);
        leanh::lean_dec_ref(v_p_2108_);
        leanh::lean_dec_ref(v_s_2107_);
        return v_stopPos_2109_;
    } else {
        let mut v___x_2112_: u8 = 0;
        v___x_2112_ = lean_string_is_valid_pos(v_s_2107_, v_pos_2110_);
        if v___x_2112_ == 0 {
            leanh::lean_dec(v_pos_2110_);
            leanh::lean_dec_ref(v_p_2108_);
            leanh::lean_dec_ref(v_s_2107_);
            return v_stopPos_2109_;
        } else {
            let mut v___x_2113_: u8 = 0;
            v___x_2113_ = lean_string_is_valid_pos(v_s_2107_, v_stopPos_2109_);
            if v___x_2113_ == 0 {
                leanh::lean_dec(v_pos_2110_);
                leanh::lean_dec_ref(v_p_2108_);
                leanh::lean_dec_ref(v_s_2107_);
                return v_stopPos_2109_;
            } else {
                let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_stopPos_2109_);
                leanh::lean_inc(v_pos_2110_);
                leanh::lean_inc_ref(v_s_2107_);
                v___x_2114_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2114_, 0, v_s_2107_);
                leanh::lean_ctor_set(v___x_2114_, 1, v_pos_2110_);
                leanh::lean_ctor_set(v___x_2114_, 2, v_stopPos_2109_);
                v_searcher_2115_ = leanh::lean_unsigned_to_nat(0);
                v___x_2116_ = leanh::lean_box(0);
                v___x_2117_ =
                    l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
                        v___x_2114_,
                        v_pos_2110_,
                        v_s_2107_,
                        v_p_2108_,
                        v_searcher_2115_,
                        v___x_2116_,
                    );
                leanh::lean_dec_ref(v_s_2107_);
                leanh::lean_dec_ref_known(v___x_2114_, 3);
                if leanh::lean_obj_tag(v___x_2117_) == 0 {
                    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2118_ = lean_nat_sub(v_stopPos_2109_, v_pos_2110_);
                    leanh::lean_dec(v_stopPos_2109_);
                    v___x_2119_ = lean_nat_add(v_pos_2110_, v___x_2118_);
                    leanh::lean_dec(v___x_2118_);
                    leanh::lean_dec(v_pos_2110_);
                    return v___x_2119_;
                } else {
                    let mut v_val_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_stopPos_2109_);
                    v_val_2120_ = leanh::lean_ctor_get(v___x_2117_, 0);
                    leanh::lean_inc(v_val_2120_);
                    leanh::lean_dec_ref_known(v___x_2117_, 1);
                    v___x_2121_ = lean_nat_add(v_pos_2110_, v_val_2120_);
                    leanh::lean_dec(v_val_2120_);
                    leanh::lean_dec(v_pos_2110_);
                    return v___x_2121_;
                }
            }
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(
    mut v___x_2122_: *mut leanh::LeanObject,
    mut v_pos_2123_: *mut leanh::LeanObject,
    mut v_s_2124_: *mut leanh::LeanObject,
    mut v_p_2125_: *mut leanh::LeanObject,
    mut v_inst_2126_: *mut leanh::LeanObject,
    mut v_R_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_b_2129_: *mut leanh::LeanObject,
    mut v_c_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
        v___x_2122_,
        v_pos_2123_,
        v_s_2124_,
        v_p_2125_,
        v_a_2128_,
        v_b_2129_,
    );
    return v___x_2131_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___boxed(
    mut v___x_2132_: *mut leanh::LeanObject,
    mut v_pos_2133_: *mut leanh::LeanObject,
    mut v_s_2134_: *mut leanh::LeanObject,
    mut v_p_2135_: *mut leanh::LeanObject,
    mut v_inst_2136_: *mut leanh::LeanObject,
    mut v_R_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_b_2139_: *mut leanh::LeanObject,
    mut v_c_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(
        v___x_2132_,
        v_pos_2133_,
        v_s_2134_,
        v_p_2135_,
        v_inst_2136_,
        v_R_2137_,
        v_a_2138_,
        v_b_2139_,
        v_c_2140_,
    );
    leanh::lean_dec(v_b_2139_);
    leanh::lean_dec_ref(v_s_2134_);
    leanh::lean_dec(v_pos_2133_);
    leanh::lean_dec_ref(v___x_2132_);
    return v_res_2141_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
    mut v___x_2142_: *mut leanh::LeanObject,
    mut v_pos_2143_: *mut leanh::LeanObject,
    mut v_s_2144_: *mut leanh::LeanObject,
    mut v_c_2145_: u32,
    mut v_a_2146_: *mut leanh::LeanObject,
    mut v_b_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: u32 = 0;
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2148_ = leanh::lean_ctor_get(v___x_2142_, 1);
                v_endExclusive_2149_ = leanh::lean_ctor_get(v___x_2142_, 2);
                v___x_2150_ = lean_nat_sub(v_endExclusive_2149_, v_startInclusive_2148_);
                v___x_2151_ = lean_nat_dec_eq(v_a_2146_, v___x_2150_);
                leanh::lean_dec(v___x_2150_);
                if v___x_2151_ == 0 {
                    v___x_2152_ = lean_nat_add(v_pos_2143_, v_a_2146_);
                    v___x_2153_ = lean_string_utf8_get_fast(v_s_2144_, v___x_2152_);
                    v___x_2154_ = lean_uint32_dec_eq(v___x_2153_, v_c_2145_);
                    if v___x_2154_ == 0 {
                        leanh::lean_dec(v_a_2146_);
                        v___x_2155_ = leanh::lean_box(0);
                        v___x_2156_ = lean_string_utf8_next_fast(v_s_2144_, v___x_2152_);
                        leanh::lean_dec(v___x_2152_);
                        v___x_2157_ = lean_nat_sub(v___x_2156_, v_pos_2143_);
                        v_a_2146_ = v___x_2157_;
                        v_b_2147_ = v___x_2155_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2152_);
                        v___x_2159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2159_, 0, v_a_2146_);
                        return v___x_2159_;
                    }
                } else {
                    leanh::lean_dec(v_a_2146_);
                    leanh::lean_inc(v_b_2147_);
                    return v_b_2147_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg___boxed(
    mut v___x_2160_: *mut leanh::LeanObject,
    mut v_pos_2161_: *mut leanh::LeanObject,
    mut v_s_2162_: *mut leanh::LeanObject,
    mut v_c_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_b_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2166_: u32 = 0;
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2166_ = leanh::lean_unbox_uint32(v_c_2163_);
    leanh::lean_dec(v_c_2163_);
    v_res_2167_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
        v___x_2160_,
        v_pos_2161_,
        v_s_2162_,
        v_c_boxed_2166_,
        v_a_2164_,
        v_b_2165_,
    );
    leanh::lean_dec(v_b_2165_);
    leanh::lean_dec_ref(v_s_2162_);
    leanh::lean_dec(v_pos_2161_);
    leanh::lean_dec_ref(v___x_2160_);
    return v_res_2167_;
}
pub unsafe fn l_String_posOfAux(
    mut v_s_2168_: *mut leanh::LeanObject,
    mut v_c_2169_: u32,
    mut v_stopPos_2170_: *mut leanh::LeanObject,
    mut v_pos_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: u8 = 0;
    v___x_2172_ = lean_nat_dec_le(v_pos_2171_, v_stopPos_2170_);
    if v___x_2172_ == 0 {
        leanh::lean_dec(v_pos_2171_);
        leanh::lean_dec_ref(v_s_2168_);
        return v_stopPos_2170_;
    } else {
        let mut v___x_2173_: u8 = 0;
        v___x_2173_ = lean_string_is_valid_pos(v_s_2168_, v_pos_2171_);
        if v___x_2173_ == 0 {
            leanh::lean_dec(v_pos_2171_);
            leanh::lean_dec_ref(v_s_2168_);
            return v_stopPos_2170_;
        } else {
            let mut v___x_2174_: u8 = 0;
            v___x_2174_ = lean_string_is_valid_pos(v_s_2168_, v_stopPos_2170_);
            if v___x_2174_ == 0 {
                leanh::lean_dec(v_pos_2171_);
                leanh::lean_dec_ref(v_s_2168_);
                return v_stopPos_2170_;
            } else {
                let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_searcher_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_stopPos_2170_);
                leanh::lean_inc(v_pos_2171_);
                leanh::lean_inc_ref(v_s_2168_);
                v___x_2175_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2175_, 0, v_s_2168_);
                leanh::lean_ctor_set(v___x_2175_, 1, v_pos_2171_);
                leanh::lean_ctor_set(v___x_2175_, 2, v_stopPos_2170_);
                v_searcher_2176_ = leanh::lean_unsigned_to_nat(0);
                v___x_2177_ = leanh::lean_box(0);
                v___x_2178_ =
                    l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
                        v___x_2175_,
                        v_pos_2171_,
                        v_s_2168_,
                        v_c_2169_,
                        v_searcher_2176_,
                        v___x_2177_,
                    );
                leanh::lean_dec_ref(v_s_2168_);
                leanh::lean_dec_ref_known(v___x_2175_, 3);
                if leanh::lean_obj_tag(v___x_2178_) == 0 {
                    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2179_ = lean_nat_sub(v_stopPos_2170_, v_pos_2171_);
                    leanh::lean_dec(v_stopPos_2170_);
                    v___x_2180_ = lean_nat_add(v_pos_2171_, v___x_2179_);
                    leanh::lean_dec(v___x_2179_);
                    leanh::lean_dec(v_pos_2171_);
                    return v___x_2180_;
                } else {
                    let mut v_val_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_stopPos_2170_);
                    v_val_2181_ = leanh::lean_ctor_get(v___x_2178_, 0);
                    leanh::lean_inc(v_val_2181_);
                    leanh::lean_dec_ref_known(v___x_2178_, 1);
                    v___x_2182_ = lean_nat_add(v_pos_2171_, v_val_2181_);
                    leanh::lean_dec(v_val_2181_);
                    leanh::lean_dec(v_pos_2171_);
                    return v___x_2182_;
                }
            }
        }
    }
}
pub unsafe fn l_String_posOfAux___boxed(
    mut v_s_2183_: *mut leanh::LeanObject,
    mut v_c_2184_: *mut leanh::LeanObject,
    mut v_stopPos_2185_: *mut leanh::LeanObject,
    mut v_pos_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2187_: u32 = 0;
    let mut v_res_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2187_ = leanh::lean_unbox_uint32(v_c_2184_);
    leanh::lean_dec(v_c_2184_);
    v_res_2188_ = l_String_posOfAux(v_s_2183_, v_c_boxed_2187_, v_stopPos_2185_, v_pos_2186_);
    return v_res_2188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(
    mut v___x_2189_: *mut leanh::LeanObject,
    mut v_pos_2190_: *mut leanh::LeanObject,
    mut v_s_2191_: *mut leanh::LeanObject,
    mut v_c_2192_: u32,
    mut v_inst_2193_: *mut leanh::LeanObject,
    mut v_R_2194_: *mut leanh::LeanObject,
    mut v_a_2195_: *mut leanh::LeanObject,
    mut v_b_2196_: *mut leanh::LeanObject,
    mut v_c_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
        v___x_2189_,
        v_pos_2190_,
        v_s_2191_,
        v_c_2192_,
        v_a_2195_,
        v_b_2196_,
    );
    return v___x_2198_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___boxed(
    mut v___x_2199_: *mut leanh::LeanObject,
    mut v_pos_2200_: *mut leanh::LeanObject,
    mut v_s_2201_: *mut leanh::LeanObject,
    mut v_c_2202_: *mut leanh::LeanObject,
    mut v_inst_2203_: *mut leanh::LeanObject,
    mut v_R_2204_: *mut leanh::LeanObject,
    mut v_a_2205_: *mut leanh::LeanObject,
    mut v_b_2206_: *mut leanh::LeanObject,
    mut v_c_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2208_: u32 = 0;
    let mut v_res_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2208_ = leanh::lean_unbox_uint32(v_c_2202_);
    leanh::lean_dec(v_c_2202_);
    v_res_2209_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(
        v___x_2199_,
        v_pos_2200_,
        v_s_2201_,
        v_c_boxed_2208_,
        v_inst_2203_,
        v_R_2204_,
        v_a_2205_,
        v_b_2206_,
        v_c_2207_,
    );
    leanh::lean_dec(v_b_2206_);
    leanh::lean_dec_ref(v_s_2201_);
    leanh::lean_dec(v_pos_2200_);
    leanh::lean_dec_ref(v___x_2199_);
    return v_res_2209_;
}
pub unsafe fn l_String_posOf(
    mut v_s_2210_: *mut leanh::LeanObject,
    mut v_c_2211_: u32,
) -> *mut leanh::LeanObject {
    let mut v_searcher_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_searcher_2212_ = leanh::lean_unsigned_to_nat(0);
    v___x_2213_ = lean_string_utf8_byte_size(v_s_2210_);
    leanh::lean_inc_ref(v_s_2210_);
    v___x_2214_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2214_, 0, v_s_2210_);
    leanh::lean_ctor_set(v___x_2214_, 1, v_searcher_2212_);
    leanh::lean_ctor_set(v___x_2214_, 2, v___x_2213_);
    v___x_2215_ = leanh::lean_box(0);
    v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2214_,
        v_s_2210_,
        v_c_2211_,
        v_searcher_2212_,
        v___x_2215_,
    );
    leanh::lean_dec_ref(v_s_2210_);
    leanh::lean_dec_ref_known(v___x_2214_, 3);
    if leanh::lean_obj_tag(v___x_2216_) == 0 {
        return v___x_2213_;
    } else {
        let mut v_val_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2217_ = leanh::lean_ctor_get(v___x_2216_, 0);
        leanh::lean_inc(v_val_2217_);
        leanh::lean_dec_ref_known(v___x_2216_, 1);
        return v_val_2217_;
    }
}
pub unsafe fn l_String_posOf___boxed(
    mut v_s_2218_: *mut leanh::LeanObject,
    mut v_c_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2220_: u32 = 0;
    let mut v_res_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2220_ = leanh::lean_unbox_uint32(v_c_2219_);
    leanh::lean_dec(v_c_2219_);
    v_res_2221_ = l_String_posOf(v_s_2218_, v_c_boxed_2220_);
    return v_res_2221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(
    mut v_s_2222_: *mut leanh::LeanObject,
    mut v_c_2223_: u32,
    mut v_a_2224_: *mut leanh::LeanObject,
    mut v_b_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v_str_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u32 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2226_ = leanh::lean_unsigned_to_nat(0);
                v___x_2227_ = lean_nat_dec_eq(v_a_2224_, v___x_2226_);
                if v___x_2227_ == 0 {
                    v_str_2228_ = leanh::lean_ctor_get(v_s_2222_, 0);
                    v_startInclusive_2229_ = leanh::lean_ctor_get(v_s_2222_, 1);
                    v___x_2230_ = lean_nat_add(v_startInclusive_2229_, v_a_2224_);
                    leanh::lean_inc(v___x_2230_);
                    leanh::lean_inc(v_startInclusive_2229_);
                    leanh::lean_inc_ref(v_str_2228_);
                    v___x_2231_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2231_, 0, v_str_2228_);
                    leanh::lean_ctor_set(v___x_2231_, 1, v_startInclusive_2229_);
                    leanh::lean_ctor_set(v___x_2231_, 2, v___x_2230_);
                    v___x_2232_ = lean_nat_sub(v___x_2230_, v_startInclusive_2229_);
                    leanh::lean_dec(v___x_2230_);
                    v___x_2233_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2234_ = lean_nat_sub(v___x_2232_, v___x_2233_);
                    leanh::lean_dec(v___x_2232_);
                    v___x_2235_ = l_String_Slice_posLE(v___x_2231_, v___x_2234_);
                    leanh::lean_dec_ref_known(v___x_2231_, 3);
                    v___x_2236_ = lean_nat_add(v_startInclusive_2229_, v___x_2235_);
                    v___x_2237_ = lean_string_utf8_get_fast(v_str_2228_, v___x_2236_);
                    leanh::lean_dec(v___x_2236_);
                    v___x_2238_ = lean_uint32_dec_eq(v___x_2237_, v_c_2223_);
                    if v___x_2238_ == 0 {
                        leanh::lean_dec(v___x_2235_);
                        v___x_2239_ = leanh::lean_box(0);
                        v___x_2240_ = lean_nat_sub(v_a_2224_, v___x_2233_);
                        leanh::lean_dec(v_a_2224_);
                        v___x_2241_ = l_String_Slice_posLE(v_s_2222_, v___x_2240_);
                        v_a_2224_ = v___x_2241_;
                        v_b_2225_ = v___x_2239_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2224_);
                        v___x_2243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2243_, 0, v___x_2235_);
                        return v___x_2243_;
                    }
                } else {
                    leanh::lean_dec(v_a_2224_);
                    leanh::lean_inc(v_b_2225_);
                    return v_b_2225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2244_: *mut leanh::LeanObject,
    mut v_c_2245_: *mut leanh::LeanObject,
    mut v_a_2246_: *mut leanh::LeanObject,
    mut v_b_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2248_: u32 = 0;
    let mut v_res_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2248_ = leanh::lean_unbox_uint32(v_c_2245_);
    leanh::lean_dec(v_c_2245_);
    v_res_2249_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2244_, v_c_boxed_2248_, v_a_2246_, v_b_2247_);
    leanh::lean_dec(v_b_2247_);
    leanh::lean_dec_ref(v_s_2244_);
    return v_res_2249_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
    mut v_c_2250_: u32,
    mut v_s_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2252_ = leanh::lean_ctor_get(v_s_2251_, 1);
    v_endExclusive_2253_ = leanh::lean_ctor_get(v_s_2251_, 2);
    v_searcher_2254_ = lean_nat_sub(v_endExclusive_2253_, v_startInclusive_2252_);
    v___x_2255_ = leanh::lean_box(0);
    v___x_2256_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2251_, v_c_2250_, v_searcher_2254_, v___x_2255_);
    return v___x_2256_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0___boxed(
    mut v_c_2257_: *mut leanh::LeanObject,
    mut v_s_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2259_: u32 = 0;
    let mut v_res_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2259_ = leanh::lean_unbox_uint32(v_c_2257_);
    leanh::lean_dec(v_c_2257_);
    v_res_2260_ =
        l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(v_c_boxed_2259_, v_s_2258_);
    leanh::lean_dec_ref(v_s_2258_);
    return v_res_2260_;
}
pub unsafe fn l_String_revPosOfAux(
    mut v_s_2261_: *mut leanh::LeanObject,
    mut v_c_2262_: u32,
    mut v_pos_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2264_ = leanh::lean_unsigned_to_nat(0);
                v___x_2265_ = lean_string_utf8_byte_size(v_s_2261_);
                leanh::lean_inc_ref(v_s_2261_);
                v___x_2266_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2266_, 0, v_s_2261_);
                leanh::lean_ctor_set(v___x_2266_, 1, v___x_2264_);
                leanh::lean_ctor_set(v___x_2266_, 2, v___x_2265_);
                v___x_2267_ = l_String_Slice_pos_x3f(v___x_2266_, v_pos_2263_);
                leanh::lean_dec_ref_known(v___x_2266_, 3);
                if leanh::lean_obj_tag(v___x_2267_) == 0 {
                    leanh::lean_dec_ref(v_s_2261_);
                    v___x_2268_ = leanh::lean_box(0);
                    return v___x_2268_;
                } else {
                    v_val_2269_ = leanh::lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2288_ = (!leanh::lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2271_ = v___x_2267_;
                        v_isShared_2272_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2269_);
                        leanh::lean_dec(v___x_2267_);
                        v___x_2271_ = leanh::lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2273_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2273_, 0, v_s_2261_);
                leanh::lean_ctor_set(v___x_2273_, 1, v___x_2264_);
                leanh::lean_ctor_set(v___x_2273_, 2, v_val_2269_);
                v___x_2274_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
                    v_c_2262_,
                    v___x_2273_,
                );
                leanh::lean_dec_ref_known(v___x_2273_, 3);
                if leanh::lean_obj_tag(v___x_2274_) == 0 {
                    if leanh::lean_obj_tag(v___x_2274_) == 0 {
                        leanh::lean_del_object(v___x_2271_);
                        v___x_2275_ = leanh::lean_box(0);
                        return v___x_2275_;
                    } else {
                        v_val_2276_ = leanh::lean_ctor_get(v___x_2274_, 0);
                        leanh::lean_inc(v_val_2276_);
                        leanh::lean_dec_ref_known(v___x_2274_, 1);
                        if v_isShared_2272_ == 0 {
                            leanh::lean_ctor_set(v___x_2271_, 0, v_val_2276_);
                            v___x_2278_ = v___x_2271_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2279_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_val_2276_);
                            v___x_2278_ = v_reuseFailAlloc_2279_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2271_);
                    v_val_2280_ = leanh::lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2287_ = (!leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2274_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2280_);
                        leanh::lean_dec(v___x_2274_);
                        v___x_2282_ = leanh::lean_box(0);
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2278_;
            }
            3 => {
                if v_isShared_2283_ == 0 {
                    v___x_2285_ = v___x_2282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_val_2280_);
                    v___x_2285_ = v_reuseFailAlloc_2286_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_revPosOfAux___boxed(
    mut v_s_2289_: *mut leanh::LeanObject,
    mut v_c_2290_: *mut leanh::LeanObject,
    mut v_pos_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2292_: u32 = 0;
    let mut v_res_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2292_ = leanh::lean_unbox_uint32(v_c_2290_);
    leanh::lean_dec(v_c_2290_);
    v_res_2293_ = l_String_revPosOfAux(v_s_2289_, v_c_boxed_2292_, v_pos_2291_);
    return v_res_2293_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(
    mut v_s_2294_: *mut leanh::LeanObject,
    mut v_c_2295_: u32,
    mut v_inst_2296_: *mut leanh::LeanObject,
    mut v_R_2297_: *mut leanh::LeanObject,
    mut v_a_2298_: *mut leanh::LeanObject,
    mut v_b_2299_: *mut leanh::LeanObject,
    mut v_c_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2294_, v_c_2295_, v_a_2298_, v_b_2299_);
    return v___x_2301_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___boxed(
    mut v_s_2302_: *mut leanh::LeanObject,
    mut v_c_2303_: *mut leanh::LeanObject,
    mut v_inst_2304_: *mut leanh::LeanObject,
    mut v_R_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v_b_2307_: *mut leanh::LeanObject,
    mut v_c_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2309_: u32 = 0;
    let mut v_res_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2309_ = leanh::lean_unbox_uint32(v_c_2303_);
    leanh::lean_dec(v_c_2303_);
    v_res_2310_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(v_s_2302_, v_c_boxed_2309_, v_inst_2304_, v_R_2305_, v_a_2306_, v_b_2307_, v_c_2308_);
    leanh::lean_dec(v_b_2307_);
    leanh::lean_dec_ref(v_s_2302_);
    return v_res_2310_;
}
pub unsafe fn l_String_revPosOf(
    mut v_s_2311_: *mut leanh::LeanObject,
    mut v_c_2312_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2313_ = leanh::lean_unsigned_to_nat(0);
                v___x_2314_ = lean_string_utf8_byte_size(v_s_2311_);
                v___x_2315_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2315_, 0, v_s_2311_);
                leanh::lean_ctor_set(v___x_2315_, 1, v___x_2313_);
                leanh::lean_ctor_set(v___x_2315_, 2, v___x_2314_);
                v___x_2316_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
                    v_c_2312_,
                    v___x_2315_,
                );
                leanh::lean_dec_ref_known(v___x_2315_, 3);
                if leanh::lean_obj_tag(v___x_2316_) == 0 {
                    v___x_2317_ = leanh::lean_box(0);
                    return v___x_2317_;
                } else {
                    v_val_2318_ = leanh::lean_ctor_get(v___x_2316_, 0);
                    v_isSharedCheck_2325_ = (!leanh::lean_is_exclusive(v___x_2316_)) as u8;
                    if v_isSharedCheck_2325_ == 0 {
                        v___x_2320_ = v___x_2316_;
                        v_isShared_2321_ = v_isSharedCheck_2325_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2318_);
                        leanh::lean_dec(v___x_2316_);
                        v___x_2320_ = leanh::lean_box(0);
                        v_isShared_2321_ = v_isSharedCheck_2325_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2321_ == 0 {
                    v___x_2323_ = v___x_2320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_val_2318_);
                    v___x_2323_ = v_reuseFailAlloc_2324_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_revPosOf___boxed(
    mut v_s_2326_: *mut leanh::LeanObject,
    mut v_c_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2328_: u32 = 0;
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2328_ = leanh::lean_unbox_uint32(v_c_2327_);
    leanh::lean_dec(v_c_2327_);
    v_res_2329_ = l_String_revPosOf(v_s_2326_, v_c_boxed_2328_);
    return v_res_2329_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(
    mut v_s_2330_: *mut leanh::LeanObject,
    mut v_p_2331_: *mut leanh::LeanObject,
    mut v_a_2332_: *mut leanh::LeanObject,
    mut v_b_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v_str_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: u32 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = leanh::lean_unsigned_to_nat(0);
                v___x_2335_ = lean_nat_dec_eq(v_a_2332_, v___x_2334_);
                if v___x_2335_ == 0 {
                    v_str_2336_ = leanh::lean_ctor_get(v_s_2330_, 0);
                    v_startInclusive_2337_ = leanh::lean_ctor_get(v_s_2330_, 1);
                    v___x_2338_ = lean_nat_add(v_startInclusive_2337_, v_a_2332_);
                    leanh::lean_inc(v___x_2338_);
                    leanh::lean_inc(v_startInclusive_2337_);
                    leanh::lean_inc_ref(v_str_2336_);
                    v___x_2339_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2339_, 0, v_str_2336_);
                    leanh::lean_ctor_set(v___x_2339_, 1, v_startInclusive_2337_);
                    leanh::lean_ctor_set(v___x_2339_, 2, v___x_2338_);
                    v___x_2340_ = lean_nat_sub(v___x_2338_, v_startInclusive_2337_);
                    leanh::lean_dec(v___x_2338_);
                    v___x_2341_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2342_ = lean_nat_sub(v___x_2340_, v___x_2341_);
                    leanh::lean_dec(v___x_2340_);
                    v___x_2343_ = l_String_Slice_posLE(v___x_2339_, v___x_2342_);
                    leanh::lean_dec_ref_known(v___x_2339_, 3);
                    v___x_2344_ = lean_nat_add(v_startInclusive_2337_, v___x_2343_);
                    v___x_2345_ = lean_string_utf8_get_fast(v_str_2336_, v___x_2344_);
                    leanh::lean_dec(v___x_2344_);
                    v___x_2346_ = leanh::lean_box_uint32(v___x_2345_);
                    leanh::lean_inc_ref(v_p_2331_);
                    v___x_2347_ = leanh::lean_apply_1(v_p_2331_, v___x_2346_);
                    v___x_2348_ = (leanh::lean_unbox(v___x_2347_) as u8);
                    if v___x_2348_ == 0 {
                        leanh::lean_dec(v___x_2343_);
                        v___x_2349_ = leanh::lean_box(0);
                        v___x_2350_ = lean_nat_sub(v_a_2332_, v___x_2341_);
                        leanh::lean_dec(v_a_2332_);
                        v___x_2351_ = l_String_Slice_posLE(v_s_2330_, v___x_2350_);
                        v_a_2332_ = v___x_2351_;
                        v_b_2333_ = v___x_2349_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2332_);
                        leanh::lean_dec_ref(v_p_2331_);
                        v___x_2353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2353_, 0, v___x_2343_);
                        return v___x_2353_;
                    }
                } else {
                    leanh::lean_dec(v_a_2332_);
                    leanh::lean_dec_ref(v_p_2331_);
                    leanh::lean_inc(v_b_2333_);
                    return v_b_2333_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2354_: *mut leanh::LeanObject,
    mut v_p_2355_: *mut leanh::LeanObject,
    mut v_a_2356_: *mut leanh::LeanObject,
    mut v_b_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2354_, v_p_2355_, v_a_2356_, v_b_2357_);
    leanh::lean_dec(v_b_2357_);
    leanh::lean_dec_ref(v_s_2354_);
    return v_res_2358_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
    mut v_p_2359_: *mut leanh::LeanObject,
    mut v_s_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2361_ = leanh::lean_ctor_get(v_s_2360_, 1);
    v_endExclusive_2362_ = leanh::lean_ctor_get(v_s_2360_, 2);
    v_searcher_2363_ = lean_nat_sub(v_endExclusive_2362_, v_startInclusive_2361_);
    v___x_2364_ = leanh::lean_box(0);
    v___x_2365_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2360_, v_p_2359_, v_searcher_2363_, v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0___boxed(
    mut v_p_2366_: *mut leanh::LeanObject,
    mut v_s_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2368_ =
        l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(v_p_2366_, v_s_2367_);
    leanh::lean_dec_ref(v_s_2367_);
    return v_res_2368_;
}
pub unsafe fn l_String_revFindAux(
    mut v_s_2369_: *mut leanh::LeanObject,
    mut v_p_2370_: *mut leanh::LeanObject,
    mut v_pos_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2372_ = leanh::lean_unsigned_to_nat(0);
                v___x_2373_ = lean_string_utf8_byte_size(v_s_2369_);
                leanh::lean_inc_ref(v_s_2369_);
                v___x_2374_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2374_, 0, v_s_2369_);
                leanh::lean_ctor_set(v___x_2374_, 1, v___x_2372_);
                leanh::lean_ctor_set(v___x_2374_, 2, v___x_2373_);
                v___x_2375_ = l_String_Slice_pos_x3f(v___x_2374_, v_pos_2371_);
                leanh::lean_dec_ref_known(v___x_2374_, 3);
                if leanh::lean_obj_tag(v___x_2375_) == 0 {
                    leanh::lean_dec_ref(v_p_2370_);
                    leanh::lean_dec_ref(v_s_2369_);
                    v___x_2376_ = leanh::lean_box(0);
                    return v___x_2376_;
                } else {
                    v_val_2377_ = leanh::lean_ctor_get(v___x_2375_, 0);
                    v_isSharedCheck_2396_ = (!leanh::lean_is_exclusive(v___x_2375_)) as u8;
                    if v_isSharedCheck_2396_ == 0 {
                        v___x_2379_ = v___x_2375_;
                        v_isShared_2380_ = v_isSharedCheck_2396_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2377_);
                        leanh::lean_dec(v___x_2375_);
                        v___x_2379_ = leanh::lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2381_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2381_, 0, v_s_2369_);
                leanh::lean_ctor_set(v___x_2381_, 1, v___x_2372_);
                leanh::lean_ctor_set(v___x_2381_, 2, v_val_2377_);
                v___x_2382_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
                    v_p_2370_,
                    v___x_2381_,
                );
                leanh::lean_dec_ref_known(v___x_2381_, 3);
                if leanh::lean_obj_tag(v___x_2382_) == 0 {
                    if leanh::lean_obj_tag(v___x_2382_) == 0 {
                        leanh::lean_del_object(v___x_2379_);
                        v___x_2383_ = leanh::lean_box(0);
                        return v___x_2383_;
                    } else {
                        v_val_2384_ = leanh::lean_ctor_get(v___x_2382_, 0);
                        leanh::lean_inc(v_val_2384_);
                        leanh::lean_dec_ref_known(v___x_2382_, 1);
                        if v_isShared_2380_ == 0 {
                            leanh::lean_ctor_set(v___x_2379_, 0, v_val_2384_);
                            v___x_2386_ = v___x_2379_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2387_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_val_2384_);
                            v___x_2386_ = v_reuseFailAlloc_2387_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2379_);
                    v_val_2388_ = leanh::lean_ctor_get(v___x_2382_, 0);
                    v_isSharedCheck_2395_ = (!leanh::lean_is_exclusive(v___x_2382_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v___x_2390_ = v___x_2382_;
                        v_isShared_2391_ = v_isSharedCheck_2395_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2388_);
                        leanh::lean_dec(v___x_2382_);
                        v___x_2390_ = leanh::lean_box(0);
                        v_isShared_2391_ = v_isSharedCheck_2395_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2386_;
            }
            3 => {
                if v_isShared_2391_ == 0 {
                    v___x_2393_ = v___x_2390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_val_2388_);
                    v___x_2393_ = v_reuseFailAlloc_2394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(
    mut v_s_2397_: *mut leanh::LeanObject,
    mut v_p_2398_: *mut leanh::LeanObject,
    mut v_inst_2399_: *mut leanh::LeanObject,
    mut v_R_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
    mut v_b_2402_: *mut leanh::LeanObject,
    mut v_c_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2404_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2397_, v_p_2398_, v_a_2401_, v_b_2402_);
    return v___x_2404_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___boxed(
    mut v_s_2405_: *mut leanh::LeanObject,
    mut v_p_2406_: *mut leanh::LeanObject,
    mut v_inst_2407_: *mut leanh::LeanObject,
    mut v_R_2408_: *mut leanh::LeanObject,
    mut v_a_2409_: *mut leanh::LeanObject,
    mut v_b_2410_: *mut leanh::LeanObject,
    mut v_c_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(v_s_2405_, v_p_2406_, v_inst_2407_, v_R_2408_, v_a_2409_, v_b_2410_, v_c_2411_);
    leanh::lean_dec(v_b_2410_);
    leanh::lean_dec_ref(v_s_2405_);
    return v_res_2412_;
}
pub unsafe fn l_String_revFind(
    mut v_s_2413_: *mut leanh::LeanObject,
    mut v_p_2414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2415_ = leanh::lean_unsigned_to_nat(0);
                v___x_2416_ = lean_string_utf8_byte_size(v_s_2413_);
                v___x_2417_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2417_, 0, v_s_2413_);
                leanh::lean_ctor_set(v___x_2417_, 1, v___x_2415_);
                leanh::lean_ctor_set(v___x_2417_, 2, v___x_2416_);
                v___x_2418_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
                    v_p_2414_,
                    v___x_2417_,
                );
                leanh::lean_dec_ref_known(v___x_2417_, 3);
                if leanh::lean_obj_tag(v___x_2418_) == 0 {
                    v___x_2419_ = leanh::lean_box(0);
                    return v___x_2419_;
                } else {
                    v_val_2420_ = leanh::lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2427_ = (!leanh::lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2422_ = v___x_2418_;
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2420_);
                        leanh::lean_dec(v___x_2418_);
                        v___x_2422_ = leanh::lean_box(0);
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2423_ == 0 {
                    v___x_2425_ = v___x_2422_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_val_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(
    mut v_s_2428_: *mut leanh::LeanObject,
    mut v_a_2429_: *mut leanh::LeanObject,
    mut v_b_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v_str_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u32 = 0;
    let mut v___x_2443_: u32 = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2431_ = leanh::lean_unsigned_to_nat(0);
                v___x_2432_ = lean_nat_dec_eq(v_a_2429_, v___x_2431_);
                if v___x_2432_ == 0 {
                    v_str_2433_ = leanh::lean_ctor_get(v_s_2428_, 0);
                    v_startInclusive_2434_ = leanh::lean_ctor_get(v_s_2428_, 1);
                    v___x_2435_ = lean_nat_add(v_startInclusive_2434_, v_a_2429_);
                    leanh::lean_inc(v___x_2435_);
                    leanh::lean_inc(v_startInclusive_2434_);
                    leanh::lean_inc_ref(v_str_2433_);
                    v___x_2436_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2436_, 0, v_str_2433_);
                    leanh::lean_ctor_set(v___x_2436_, 1, v_startInclusive_2434_);
                    leanh::lean_ctor_set(v___x_2436_, 2, v___x_2435_);
                    v___x_2437_ = lean_nat_sub(v___x_2435_, v_startInclusive_2434_);
                    leanh::lean_dec(v___x_2435_);
                    v___x_2438_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2439_ = lean_nat_sub(v___x_2437_, v___x_2438_);
                    leanh::lean_dec(v___x_2437_);
                    v___x_2440_ = l_String_Slice_posLE(v___x_2436_, v___x_2439_);
                    leanh::lean_dec_ref_known(v___x_2436_, 3);
                    v___x_2441_ = lean_nat_add(v_startInclusive_2434_, v___x_2440_);
                    v___x_2442_ = lean_string_utf8_get_fast(v_str_2433_, v___x_2441_);
                    leanh::lean_dec(v___x_2441_);
                    v___x_2443_ = 10;
                    v___x_2444_ = lean_uint32_dec_eq(v___x_2442_, v___x_2443_);
                    if v___x_2444_ == 0 {
                        leanh::lean_dec(v___x_2440_);
                        v___x_2445_ = leanh::lean_box(0);
                        v___x_2446_ = lean_nat_sub(v_a_2429_, v___x_2438_);
                        leanh::lean_dec(v_a_2429_);
                        v___x_2447_ = l_String_Slice_posLE(v_s_2428_, v___x_2446_);
                        v_a_2429_ = v___x_2447_;
                        v_b_2430_ = v___x_2445_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2429_);
                        v___x_2449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2449_, 0, v___x_2440_);
                        return v___x_2449_;
                    }
                } else {
                    leanh::lean_dec(v_a_2429_);
                    leanh::lean_inc(v_b_2430_);
                    return v_b_2430_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg___boxed(
    mut v_s_2450_: *mut leanh::LeanObject,
    mut v_a_2451_: *mut leanh::LeanObject,
    mut v_b_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2450_, v_a_2451_, v_b_2452_);
    leanh::lean_dec(v_b_2452_);
    leanh::lean_dec_ref(v_s_2450_);
    return v_res_2453_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(
    mut v_s_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_2455_ = leanh::lean_ctor_get(v_s_2454_, 1);
    v_endExclusive_2456_ = leanh::lean_ctor_get(v_s_2454_, 2);
    v_searcher_2457_ = lean_nat_sub(v_endExclusive_2456_, v_startInclusive_2455_);
    v___x_2458_ = leanh::lean_box(0);
    v___x_2459_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2454_, v_searcher_2457_, v___x_2458_);
    return v___x_2459_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0___boxed(
    mut v_s_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v_s_2460_);
    leanh::lean_dec_ref(v_s_2460_);
    return v_res_2461_;
}
pub unsafe fn l_String_findLineStart(
    mut v_s_2462_: *mut leanh::LeanObject,
    mut v_pos_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2464_ = leanh::lean_unsigned_to_nat(0);
    v___x_2465_ = lean_string_utf8_byte_size(v_s_2462_);
    leanh::lean_inc_ref(v_s_2462_);
    v___x_2466_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2466_, 0, v_s_2462_);
    leanh::lean_ctor_set(v___x_2466_, 1, v___x_2464_);
    leanh::lean_ctor_set(v___x_2466_, 2, v___x_2465_);
    v___x_2467_ = l_String_Slice_pos_x3f(v___x_2466_, v_pos_2463_);
    leanh::lean_dec_ref_known(v___x_2466_, 3);
    if leanh::lean_obj_tag(v___x_2467_) == 0 {
        leanh::lean_dec_ref(v_s_2462_);
        return v___x_2464_;
    } else {
        let mut v_val_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2468_ = leanh::lean_ctor_get(v___x_2467_, 0);
        leanh::lean_inc(v_val_2468_);
        leanh::lean_dec_ref_known(v___x_2467_, 1);
        v___x_2469_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2469_, 0, v_s_2462_);
        leanh::lean_ctor_set(v___x_2469_, 1, v___x_2464_);
        leanh::lean_ctor_set(v___x_2469_, 2, v_val_2468_);
        v___x_2470_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v___x_2469_);
        leanh::lean_dec_ref_known(v___x_2469_, 3);
        if leanh::lean_obj_tag(v___x_2470_) == 0 {
            if leanh::lean_obj_tag(v___x_2470_) == 0 {
                return v___x_2464_;
            } else {
                let mut v_val_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_val_2471_ = leanh::lean_ctor_get(v___x_2470_, 0);
                leanh::lean_inc(v_val_2471_);
                leanh::lean_dec_ref_known(v___x_2470_, 1);
                return v_val_2471_;
            }
        } else {
            let mut v_val_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2472_ = leanh::lean_ctor_get(v___x_2470_, 0);
            leanh::lean_inc(v_val_2472_);
            leanh::lean_dec_ref_known(v___x_2470_, 1);
            return v_val_2472_;
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(
    mut v_s_2473_: *mut leanh::LeanObject,
    mut v_inst_2474_: *mut leanh::LeanObject,
    mut v_R_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_b_2477_: *mut leanh::LeanObject,
    mut v_c_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2473_, v_a_2476_, v_b_2477_);
    return v___x_2479_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___boxed(
    mut v_s_2480_: *mut leanh::LeanObject,
    mut v_inst_2481_: *mut leanh::LeanObject,
    mut v_R_2482_: *mut leanh::LeanObject,
    mut v_a_2483_: *mut leanh::LeanObject,
    mut v_b_2484_: *mut leanh::LeanObject,
    mut v_c_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(v_s_2480_, v_inst_2481_, v_R_2482_, v_a_2483_, v_b_2484_, v_c_2485_);
    leanh::lean_dec(v_b_2484_);
    leanh::lean_dec_ref(v_s_2480_);
    return v_res_2486_;
}
pub unsafe fn l_String_split___redArg(
    mut v_s_2487_: *mut leanh::LeanObject,
    mut v_inst_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = leanh::lean_unsigned_to_nat(0);
    v___x_2490_ = lean_string_utf8_byte_size(v_s_2487_);
    v___x_2491_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2491_, 0, v_s_2487_);
    leanh::lean_ctor_set(v___x_2491_, 1, v___x_2489_);
    leanh::lean_ctor_set(v___x_2491_, 2, v___x_2490_);
    v___x_2492_ = l_String_Slice_splitToSubslice___redArg(v___x_2491_, v_inst_2488_);
    return v___x_2492_;
}
pub unsafe fn l_String_split(
    mut v_00_u03c1_2493_: *mut leanh::LeanObject,
    mut v_00_u03c3_2494_: *mut leanh::LeanObject,
    mut v_inst_2495_: *mut leanh::LeanObject,
    mut v_s_2496_: *mut leanh::LeanObject,
    mut v_pat_2497_: *mut leanh::LeanObject,
    mut v_inst_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = leanh::lean_unsigned_to_nat(0);
    v___x_2500_ = lean_string_utf8_byte_size(v_s_2496_);
    v___x_2501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2501_, 0, v_s_2496_);
    leanh::lean_ctor_set(v___x_2501_, 1, v___x_2499_);
    leanh::lean_ctor_set(v___x_2501_, 2, v___x_2500_);
    v___x_2502_ = l_String_Slice_splitToSubslice___redArg(v___x_2501_, v_inst_2498_);
    return v___x_2502_;
}
pub unsafe fn l_String_split___boxed(
    mut v_00_u03c1_2503_: *mut leanh::LeanObject,
    mut v_00_u03c3_2504_: *mut leanh::LeanObject,
    mut v_inst_2505_: *mut leanh::LeanObject,
    mut v_s_2506_: *mut leanh::LeanObject,
    mut v_pat_2507_: *mut leanh::LeanObject,
    mut v_inst_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_String_split(
        v_00_u03c1_2503_,
        v_00_u03c3_2504_,
        v_inst_2505_,
        v_s_2506_,
        v_pat_2507_,
        v_inst_2508_,
    );
    leanh::lean_dec(v_pat_2507_);
    leanh::lean_dec(v_inst_2505_);
    return v_res_2509_;
}
pub unsafe fn l_String_splitInclusive___redArg(
    mut v_s_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ = leanh::lean_unsigned_to_nat(0);
    v___x_2513_ = lean_string_utf8_byte_size(v_s_2510_);
    v___x_2514_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2514_, 0, v_s_2510_);
    leanh::lean_ctor_set(v___x_2514_, 1, v___x_2512_);
    leanh::lean_ctor_set(v___x_2514_, 2, v___x_2513_);
    v___x_2515_ = l_String_Slice_splitInclusive___redArg(v___x_2514_, v_inst_2511_);
    return v___x_2515_;
}
pub unsafe fn l_String_splitInclusive(
    mut v_00_u03c1_2516_: *mut leanh::LeanObject,
    mut v_00_u03c3_2517_: *mut leanh::LeanObject,
    mut v_s_2518_: *mut leanh::LeanObject,
    mut v_pat_2519_: *mut leanh::LeanObject,
    mut v_inst_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = leanh::lean_unsigned_to_nat(0);
    v___x_2522_ = lean_string_utf8_byte_size(v_s_2518_);
    v___x_2523_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2523_, 0, v_s_2518_);
    leanh::lean_ctor_set(v___x_2523_, 1, v___x_2521_);
    leanh::lean_ctor_set(v___x_2523_, 2, v___x_2522_);
    v___x_2524_ = l_String_Slice_splitInclusive___redArg(v___x_2523_, v_inst_2520_);
    return v___x_2524_;
}
pub unsafe fn l_String_splitInclusive___boxed(
    mut v_00_u03c1_2525_: *mut leanh::LeanObject,
    mut v_00_u03c3_2526_: *mut leanh::LeanObject,
    mut v_s_2527_: *mut leanh::LeanObject,
    mut v_pat_2528_: *mut leanh::LeanObject,
    mut v_inst_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_String_splitInclusive(
        v_00_u03c1_2525_,
        v_00_u03c3_2526_,
        v_s_2527_,
        v_pat_2528_,
        v_inst_2529_,
    );
    leanh::lean_dec(v_pat_2528_);
    return v_res_2530_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
    mut v_f_2531_: *mut leanh::LeanObject,
    mut v___x_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
    mut v_b_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u32 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2535_ = leanh::lean_ctor_get(v___x_2532_, 0);
                v_startInclusive_2536_ = leanh::lean_ctor_get(v___x_2532_, 1);
                v_endExclusive_2537_ = leanh::lean_ctor_get(v___x_2532_, 2);
                v___x_2538_ = lean_nat_sub(v_endExclusive_2537_, v_startInclusive_2536_);
                v___x_2539_ = lean_nat_dec_eq(v_a_2533_, v___x_2538_);
                leanh::lean_dec(v___x_2538_);
                if v___x_2539_ == 0 {
                    v___x_2540_ = lean_nat_add(v_startInclusive_2536_, v_a_2533_);
                    leanh::lean_dec(v_a_2533_);
                    v___x_2541_ = lean_string_utf8_next_fast(v_str_2535_, v___x_2540_);
                    v___x_2542_ = lean_nat_sub(v___x_2541_, v_startInclusive_2536_);
                    v___x_2543_ = lean_string_utf8_get_fast(v_str_2535_, v___x_2540_);
                    leanh::lean_dec(v___x_2540_);
                    v___x_2544_ = leanh::lean_box_uint32(v___x_2543_);
                    leanh::lean_inc(v_f_2531_);
                    v___x_2545_ = leanh::lean_apply_2(v_f_2531_, v_b_2534_, v___x_2544_);
                    v_a_2533_ = v___x_2542_;
                    v_b_2534_ = v___x_2545_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2533_);
                    leanh::lean_dec(v_f_2531_);
                    return v_b_2534_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg___boxed(
    mut v_f_2547_: *mut leanh::LeanObject,
    mut v___x_2548_: *mut leanh::LeanObject,
    mut v_a_2549_: *mut leanh::LeanObject,
    mut v_b_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2547_,
        v___x_2548_,
        v_a_2549_,
        v_b_2550_,
    );
    leanh::lean_dec_ref(v___x_2548_);
    return v_res_2551_;
}
pub unsafe fn l_String_foldlAux___redArg(
    mut v_f_2552_: *mut leanh::LeanObject,
    mut v_s_2553_: *mut leanh::LeanObject,
    mut v_stopPos_2554_: *mut leanh::LeanObject,
    mut v_i_2555_: *mut leanh::LeanObject,
    mut v_a_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = leanh::lean_unsigned_to_nat(0);
    v___x_2558_ = lean_string_utf8_byte_size(v_s_2553_);
    leanh::lean_inc_ref(v_s_2553_);
    v___x_2559_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2559_, 0, v_s_2553_);
    leanh::lean_ctor_set(v___x_2559_, 1, v___x_2557_);
    leanh::lean_ctor_set(v___x_2559_, 2, v___x_2558_);
    v___x_2560_ = l_String_Slice_pos_x21(v___x_2559_, v_i_2555_);
    v___x_2561_ = l_String_Slice_pos_x21(v___x_2559_, v_stopPos_2554_);
    leanh::lean_dec_ref_known(v___x_2559_, 3);
    v___x_2562_ = l_String_slice_x21(v_s_2553_, v___x_2560_, v___x_2561_);
    leanh::lean_dec(v___x_2561_);
    leanh::lean_dec(v___x_2560_);
    v___x_2563_ = l_String_Slice_positions(v___x_2562_);
    v___x_2564_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2552_,
        v___x_2562_,
        v___x_2563_,
        v_a_2556_,
    );
    leanh::lean_dec_ref(v___x_2562_);
    return v___x_2564_;
}
pub unsafe fn l_String_foldlAux___redArg___boxed(
    mut v_f_2565_: *mut leanh::LeanObject,
    mut v_s_2566_: *mut leanh::LeanObject,
    mut v_stopPos_2567_: *mut leanh::LeanObject,
    mut v_i_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2570_ =
        l_String_foldlAux___redArg(v_f_2565_, v_s_2566_, v_stopPos_2567_, v_i_2568_, v_a_2569_);
    leanh::lean_dec(v_i_2568_);
    leanh::lean_dec(v_stopPos_2567_);
    return v_res_2570_;
}
pub unsafe fn l_String_foldlAux(
    mut v_00_u03b1_2571_: *mut leanh::LeanObject,
    mut v_f_2572_: *mut leanh::LeanObject,
    mut v_s_2573_: *mut leanh::LeanObject,
    mut v_stopPos_2574_: *mut leanh::LeanObject,
    mut v_i_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ =
        l_String_foldlAux___redArg(v_f_2572_, v_s_2573_, v_stopPos_2574_, v_i_2575_, v_a_2576_);
    return v___x_2577_;
}
pub unsafe fn l_String_foldlAux___boxed(
    mut v_00_u03b1_2578_: *mut leanh::LeanObject,
    mut v_f_2579_: *mut leanh::LeanObject,
    mut v_s_2580_: *mut leanh::LeanObject,
    mut v_stopPos_2581_: *mut leanh::LeanObject,
    mut v_i_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_String_foldlAux(
        v_00_u03b1_2578_,
        v_f_2579_,
        v_s_2580_,
        v_stopPos_2581_,
        v_i_2582_,
        v_a_2583_,
    );
    leanh::lean_dec(v_i_2582_);
    leanh::lean_dec(v_stopPos_2581_);
    return v_res_2584_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(
    mut v_00_u03b1_2585_: *mut leanh::LeanObject,
    mut v_f_2586_: *mut leanh::LeanObject,
    mut v___x_2587_: *mut leanh::LeanObject,
    mut v_inst_2588_: *mut leanh::LeanObject,
    mut v_R_2589_: *mut leanh::LeanObject,
    mut v_a_2590_: *mut leanh::LeanObject,
    mut v_b_2591_: *mut leanh::LeanObject,
    mut v_c_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2586_,
        v___x_2587_,
        v_a_2590_,
        v_b_2591_,
    );
    return v___x_2593_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___boxed(
    mut v_00_u03b1_2594_: *mut leanh::LeanObject,
    mut v_f_2595_: *mut leanh::LeanObject,
    mut v___x_2596_: *mut leanh::LeanObject,
    mut v_inst_2597_: *mut leanh::LeanObject,
    mut v_R_2598_: *mut leanh::LeanObject,
    mut v_a_2599_: *mut leanh::LeanObject,
    mut v_b_2600_: *mut leanh::LeanObject,
    mut v_c_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2602_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(
        v_00_u03b1_2594_,
        v_f_2595_,
        v___x_2596_,
        v_inst_2597_,
        v_R_2598_,
        v_a_2599_,
        v_b_2600_,
        v_c_2601_,
    );
    leanh::lean_dec_ref(v___x_2596_);
    return v_res_2602_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
    mut v_f_2603_: *mut leanh::LeanObject,
    mut v___x_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_b_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v_str_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevPos_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u32 = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = leanh::lean_unsigned_to_nat(0);
                v___x_2608_ = lean_nat_dec_eq(v_a_2605_, v___x_2607_);
                if v___x_2608_ == 0 {
                    v_str_2609_ = leanh::lean_ctor_get(v___x_2604_, 0);
                    v_startInclusive_2610_ = leanh::lean_ctor_get(v___x_2604_, 1);
                    v___x_2611_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2612_ = lean_nat_sub(v_a_2605_, v___x_2611_);
                    leanh::lean_dec(v_a_2605_);
                    v_prevPos_2613_ = l_String_Slice_posLE(v___x_2604_, v___x_2612_);
                    v___x_2614_ = lean_nat_add(v_startInclusive_2610_, v_prevPos_2613_);
                    v___x_2615_ = lean_string_utf8_get_fast(v_str_2609_, v___x_2614_);
                    leanh::lean_dec(v___x_2614_);
                    v___x_2616_ = leanh::lean_box_uint32(v___x_2615_);
                    leanh::lean_inc(v_f_2603_);
                    v___x_2617_ = leanh::lean_apply_2(v_f_2603_, v___x_2616_, v_b_2606_);
                    v_a_2605_ = v_prevPos_2613_;
                    v_b_2606_ = v___x_2617_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2605_);
                    leanh::lean_dec(v_f_2603_);
                    return v_b_2606_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg___boxed(
    mut v_f_2619_: *mut leanh::LeanObject,
    mut v___x_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
    mut v_b_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2619_,
        v___x_2620_,
        v_a_2621_,
        v_b_2622_,
    );
    leanh::lean_dec_ref(v___x_2620_);
    return v_res_2623_;
}
pub unsafe fn l_String_foldrAux___redArg(
    mut v_f_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_s_2626_: *mut leanh::LeanObject,
    mut v_i_2627_: *mut leanh::LeanObject,
    mut v_begPos_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = leanh::lean_unsigned_to_nat(0);
    v___x_2630_ = lean_string_utf8_byte_size(v_s_2626_);
    leanh::lean_inc_ref(v_s_2626_);
    v___x_2631_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2631_, 0, v_s_2626_);
    leanh::lean_ctor_set(v___x_2631_, 1, v___x_2629_);
    leanh::lean_ctor_set(v___x_2631_, 2, v___x_2630_);
    v___x_2632_ = l_String_Slice_pos_x21(v___x_2631_, v_begPos_2628_);
    v___x_2633_ = l_String_Slice_pos_x21(v___x_2631_, v_i_2627_);
    leanh::lean_dec_ref_known(v___x_2631_, 3);
    v___x_2634_ = l_String_slice_x21(v_s_2626_, v___x_2632_, v___x_2633_);
    leanh::lean_dec(v___x_2633_);
    leanh::lean_dec(v___x_2632_);
    v___x_2635_ = l_String_Slice_revPositions(v___x_2634_);
    v___x_2636_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2624_,
        v___x_2634_,
        v___x_2635_,
        v_a_2625_,
    );
    leanh::lean_dec_ref(v___x_2634_);
    return v___x_2636_;
}
pub unsafe fn l_String_foldrAux___redArg___boxed(
    mut v_f_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_s_2639_: *mut leanh::LeanObject,
    mut v_i_2640_: *mut leanh::LeanObject,
    mut v_begPos_2641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2642_ =
        l_String_foldrAux___redArg(v_f_2637_, v_a_2638_, v_s_2639_, v_i_2640_, v_begPos_2641_);
    leanh::lean_dec(v_begPos_2641_);
    leanh::lean_dec(v_i_2640_);
    return v_res_2642_;
}
pub unsafe fn l_String_foldrAux(
    mut v_00_u03b1_2643_: *mut leanh::LeanObject,
    mut v_f_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_s_2646_: *mut leanh::LeanObject,
    mut v_i_2647_: *mut leanh::LeanObject,
    mut v_begPos_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2649_ =
        l_String_foldrAux___redArg(v_f_2644_, v_a_2645_, v_s_2646_, v_i_2647_, v_begPos_2648_);
    return v___x_2649_;
}
pub unsafe fn l_String_foldrAux___boxed(
    mut v_00_u03b1_2650_: *mut leanh::LeanObject,
    mut v_f_2651_: *mut leanh::LeanObject,
    mut v_a_2652_: *mut leanh::LeanObject,
    mut v_s_2653_: *mut leanh::LeanObject,
    mut v_i_2654_: *mut leanh::LeanObject,
    mut v_begPos_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_String_foldrAux(
        v_00_u03b1_2650_,
        v_f_2651_,
        v_a_2652_,
        v_s_2653_,
        v_i_2654_,
        v_begPos_2655_,
    );
    leanh::lean_dec(v_begPos_2655_);
    leanh::lean_dec(v_i_2654_);
    return v_res_2656_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(
    mut v_00_u03b1_2657_: *mut leanh::LeanObject,
    mut v_f_2658_: *mut leanh::LeanObject,
    mut v___x_2659_: *mut leanh::LeanObject,
    mut v_inst_2660_: *mut leanh::LeanObject,
    mut v_R_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_b_2663_: *mut leanh::LeanObject,
    mut v_c_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2658_,
        v___x_2659_,
        v_a_2662_,
        v_b_2663_,
    );
    return v___x_2665_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___boxed(
    mut v_00_u03b1_2666_: *mut leanh::LeanObject,
    mut v_f_2667_: *mut leanh::LeanObject,
    mut v___x_2668_: *mut leanh::LeanObject,
    mut v_inst_2669_: *mut leanh::LeanObject,
    mut v_R_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_b_2672_: *mut leanh::LeanObject,
    mut v_c_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2674_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(
        v_00_u03b1_2666_,
        v_f_2667_,
        v___x_2668_,
        v_inst_2669_,
        v_R_2670_,
        v_a_2671_,
        v_b_2672_,
        v_c_2673_,
    );
    leanh::lean_dec_ref(v___x_2668_);
    return v_res_2674_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(
    mut v_s_2675_: *mut leanh::LeanObject,
    mut v_p_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_b_2678_: u8,
) -> u8 {
    let mut v_str_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u32 = 0;
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2679_ = leanh::lean_ctor_get(v_s_2675_, 0);
                v_startInclusive_2680_ = leanh::lean_ctor_get(v_s_2675_, 1);
                v_endExclusive_2681_ = leanh::lean_ctor_get(v_s_2675_, 2);
                v___x_2682_ = lean_nat_sub(v_endExclusive_2681_, v_startInclusive_2680_);
                v___x_2683_ = lean_nat_dec_eq(v_a_2677_, v___x_2682_);
                leanh::lean_dec(v___x_2682_);
                if v___x_2683_ == 0 {
                    v___x_2684_ = lean_nat_add(v_startInclusive_2680_, v_a_2677_);
                    leanh::lean_dec(v_a_2677_);
                    v___x_2685_ = lean_string_utf8_get_fast(v_str_2679_, v___x_2684_);
                    v___x_2686_ = leanh::lean_box_uint32(v___x_2685_);
                    leanh::lean_inc_ref(v_p_2676_);
                    v___x_2687_ = leanh::lean_apply_1(v_p_2676_, v___x_2686_);
                    v___x_2688_ = (leanh::lean_unbox(v___x_2687_) as u8);
                    if v___x_2688_ == 0 {
                        v___x_2689_ = lean_string_utf8_next_fast(v_str_2679_, v___x_2684_);
                        leanh::lean_dec(v___x_2684_);
                        v___x_2690_ = lean_nat_sub(v___x_2689_, v_startInclusive_2680_);
                        v___x_2691_ = (leanh::lean_unbox(v___x_2687_) as u8);
                        v_a_2677_ = v___x_2690_;
                        v_b_2678_ = v___x_2691_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2684_);
                        leanh::lean_dec_ref(v_p_2676_);
                        v___x_2693_ = (leanh::lean_unbox(v___x_2687_) as u8);
                        return v___x_2693_;
                    }
                } else {
                    leanh::lean_dec(v_a_2677_);
                    leanh::lean_dec_ref(v_p_2676_);
                    return v_b_2678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2694_: *mut leanh::LeanObject,
    mut v_p_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_b_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_2698_: u8 = 0;
    let mut v_res_2699_: u8 = 0;
    let mut v_r_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2698_ = (leanh::lean_unbox(v_b_2697_) as u8);
    v_res_2699_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2694_, v_p_2695_, v_a_2696_, v_b_boxed_2698_);
    leanh::lean_dec_ref(v_s_2694_);
    v_r_2700_ = leanh::lean_box((v_res_2699_) as usize);
    return v_r_2700_;
}
pub unsafe fn l_String_Slice_contains___at___00String_anyAux_spec__0(
    mut v_p_2701_: *mut leanh::LeanObject,
    mut v_s_2702_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_searcher_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: u8 = 0;
    let mut v___x_2705_: u8 = 0;
    v_searcher_2703_ = leanh::lean_unsigned_to_nat(0);
    v___x_2704_ = 0;
    v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2702_, v_p_2701_, v_searcher_2703_, v___x_2704_);
    return v___x_2705_;
}
pub unsafe fn l_String_Slice_contains___at___00String_anyAux_spec__0___boxed(
    mut v_p_2706_: *mut leanh::LeanObject,
    mut v_s_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2708_: u8 = 0;
    let mut v_r_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2706_, v_s_2707_);
    leanh::lean_dec_ref(v_s_2707_);
    v_r_2709_ = leanh::lean_box((v_res_2708_) as usize);
    return v_r_2709_;
}
pub unsafe fn l_String_anyAux(
    mut v_s_2710_: *mut leanh::LeanObject,
    mut v_stopPos_2711_: *mut leanh::LeanObject,
    mut v_p_2712_: *mut leanh::LeanObject,
    mut v_i_2713_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    v___x_2714_ = leanh::lean_unsigned_to_nat(0);
    v___x_2715_ = lean_string_utf8_byte_size(v_s_2710_);
    leanh::lean_inc_ref(v_s_2710_);
    v___x_2716_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2716_, 0, v_s_2710_);
    leanh::lean_ctor_set(v___x_2716_, 1, v___x_2714_);
    leanh::lean_ctor_set(v___x_2716_, 2, v___x_2715_);
    v___x_2717_ = l_String_Slice_pos_x21(v___x_2716_, v_i_2713_);
    v___x_2718_ = l_String_Slice_pos_x21(v___x_2716_, v_stopPos_2711_);
    leanh::lean_dec_ref_known(v___x_2716_, 3);
    v___x_2719_ = l_String_slice_x21(v_s_2710_, v___x_2717_, v___x_2718_);
    leanh::lean_dec(v___x_2718_);
    leanh::lean_dec(v___x_2717_);
    v___x_2720_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2712_, v___x_2719_);
    leanh::lean_dec_ref(v___x_2719_);
    return v___x_2720_;
}
pub unsafe fn l_String_anyAux___boxed(
    mut v_s_2721_: *mut leanh::LeanObject,
    mut v_stopPos_2722_: *mut leanh::LeanObject,
    mut v_p_2723_: *mut leanh::LeanObject,
    mut v_i_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2725_: u8 = 0;
    let mut v_r_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_String_anyAux(v_s_2721_, v_stopPos_2722_, v_p_2723_, v_i_2724_);
    leanh::lean_dec(v_i_2724_);
    leanh::lean_dec(v_stopPos_2722_);
    v_r_2726_ = leanh::lean_box((v_res_2725_) as usize);
    return v_r_2726_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(
    mut v_s_2727_: *mut leanh::LeanObject,
    mut v_p_2728_: *mut leanh::LeanObject,
    mut v_inst_2729_: *mut leanh::LeanObject,
    mut v_R_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_b_2732_: u8,
    mut v_c_2733_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2734_: u8 = 0;
    v___x_2734_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2727_, v_p_2728_, v_a_2731_, v_b_2732_);
    return v___x_2734_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___boxed(
    mut v_s_2735_: *mut leanh::LeanObject,
    mut v_p_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v_R_2738_: *mut leanh::LeanObject,
    mut v_a_2739_: *mut leanh::LeanObject,
    mut v_b_2740_: *mut leanh::LeanObject,
    mut v_c_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_2742_: u8 = 0;
    let mut v_res_2743_: u8 = 0;
    let mut v_r_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2742_ = (leanh::lean_unbox(v_b_2740_) as u8);
    v_res_2743_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(v_s_2735_, v_p_2736_, v_inst_2737_, v_R_2738_, v_a_2739_, v_b_boxed_2742_, v_c_2741_);
    leanh::lean_dec_ref(v_s_2735_);
    v_r_2744_ = leanh::lean_box((v_res_2743_) as usize);
    return v_r_2744_;
}
pub unsafe fn l_String_contains___redArg(
    mut v_inst_2745_: *mut leanh::LeanObject,
    mut v_s_2746_: *mut leanh::LeanObject,
    mut v_inst_2747_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    v___x_2748_ = leanh::lean_unsigned_to_nat(0);
    v___x_2749_ = lean_string_utf8_byte_size(v_s_2746_);
    v___x_2750_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2750_, 0, v_s_2746_);
    leanh::lean_ctor_set(v___x_2750_, 1, v___x_2748_);
    leanh::lean_ctor_set(v___x_2750_, 2, v___x_2749_);
    v___x_2751_ = l_String_Slice_contains___redArg(v_inst_2745_, v___x_2750_, v_inst_2747_);
    return v___x_2751_;
}
pub unsafe fn l_String_contains___redArg___boxed(
    mut v_inst_2752_: *mut leanh::LeanObject,
    mut v_s_2753_: *mut leanh::LeanObject,
    mut v_inst_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2755_: u8 = 0;
    let mut v_r_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2755_ = l_String_contains___redArg(v_inst_2752_, v_s_2753_, v_inst_2754_);
    v_r_2756_ = leanh::lean_box((v_res_2755_) as usize);
    return v_r_2756_;
}
pub unsafe fn l_String_contains(
    mut v_00_u03c1_2757_: *mut leanh::LeanObject,
    mut v_00_u03c3_2758_: *mut leanh::LeanObject,
    mut v_inst_2759_: *mut leanh::LeanObject,
    mut v_inst_2760_: *mut leanh::LeanObject,
    mut v_s_2761_: *mut leanh::LeanObject,
    mut v_pat_2762_: *mut leanh::LeanObject,
    mut v_inst_2763_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    v___x_2764_ = leanh::lean_unsigned_to_nat(0);
    v___x_2765_ = lean_string_utf8_byte_size(v_s_2761_);
    v___x_2766_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2766_, 0, v_s_2761_);
    leanh::lean_ctor_set(v___x_2766_, 1, v___x_2764_);
    leanh::lean_ctor_set(v___x_2766_, 2, v___x_2765_);
    v___x_2767_ = l_String_Slice_contains___redArg(v_inst_2760_, v___x_2766_, v_inst_2763_);
    return v___x_2767_;
}
pub unsafe fn l_String_contains___boxed(
    mut v_00_u03c1_2768_: *mut leanh::LeanObject,
    mut v_00_u03c3_2769_: *mut leanh::LeanObject,
    mut v_inst_2770_: *mut leanh::LeanObject,
    mut v_inst_2771_: *mut leanh::LeanObject,
    mut v_s_2772_: *mut leanh::LeanObject,
    mut v_pat_2773_: *mut leanh::LeanObject,
    mut v_inst_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2775_: u8 = 0;
    let mut v_r_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_String_contains(
        v_00_u03c1_2768_,
        v_00_u03c3_2769_,
        v_inst_2770_,
        v_inst_2771_,
        v_s_2772_,
        v_pat_2773_,
        v_inst_2774_,
    );
    leanh::lean_dec(v_pat_2773_);
    leanh::lean_dec(v_inst_2770_);
    v_r_2776_ = leanh::lean_box((v_res_2775_) as usize);
    return v_r_2776_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(
    mut v_s_2777_: *mut leanh::LeanObject,
    mut v_c_2778_: u32,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_b_2780_: u8,
) -> u8 {
    let mut v_str_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u32 = 0;
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2781_ = leanh::lean_ctor_get(v_s_2777_, 0);
                v_startInclusive_2782_ = leanh::lean_ctor_get(v_s_2777_, 1);
                v_endExclusive_2783_ = leanh::lean_ctor_get(v_s_2777_, 2);
                v___x_2784_ = lean_nat_sub(v_endExclusive_2783_, v_startInclusive_2782_);
                v___x_2785_ = lean_nat_dec_eq(v_a_2779_, v___x_2784_);
                leanh::lean_dec(v___x_2784_);
                if v___x_2785_ == 0 {
                    v___x_2786_ = lean_nat_add(v_startInclusive_2782_, v_a_2779_);
                    leanh::lean_dec(v_a_2779_);
                    v___x_2787_ = lean_string_utf8_get_fast(v_str_2781_, v___x_2786_);
                    v___x_2788_ = lean_uint32_dec_eq(v___x_2787_, v_c_2778_);
                    if v___x_2788_ == 0 {
                        v___x_2789_ = lean_string_utf8_next_fast(v_str_2781_, v___x_2786_);
                        leanh::lean_dec(v___x_2786_);
                        v___x_2790_ = lean_nat_sub(v___x_2789_, v_startInclusive_2782_);
                        v_a_2779_ = v___x_2790_;
                        v_b_2780_ = v___x_2788_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2786_);
                        return v___x_2788_;
                    }
                } else {
                    leanh::lean_dec(v_a_2779_);
                    return v_b_2780_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(
    mut v_s_2792_: *mut leanh::LeanObject,
    mut v_c_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
    mut v_b_2795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2796_: u32 = 0;
    let mut v_b_boxed_2797_: u8 = 0;
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2796_ = leanh::lean_unbox_uint32(v_c_2793_);
    leanh::lean_dec(v_c_2793_);
    v_b_boxed_2797_ = (leanh::lean_unbox(v_b_2795_) as u8);
    v_res_2798_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2792_, v_c_boxed_2796_, v_a_2794_, v_b_boxed_2797_);
    leanh::lean_dec_ref(v_s_2792_);
    v_r_2799_ = leanh::lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
    mut v_c_2800_: u32,
    mut v_s_2801_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_searcher_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: u8 = 0;
    v_searcher_2802_ = leanh::lean_unsigned_to_nat(0);
    v___x_2803_ = 0;
    v___x_2804_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2801_, v_c_2800_, v_searcher_2802_, v___x_2803_);
    return v___x_2804_;
}
pub unsafe fn l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(
    mut v_c_2805_: *mut leanh::LeanObject,
    mut v_s_2806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2807_: u32 = 0;
    let mut v_res_2808_: u8 = 0;
    let mut v_r_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2807_ = leanh::lean_unbox_uint32(v_c_2805_);
    leanh::lean_dec(v_c_2805_);
    v_res_2808_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
        v_c_boxed_2807_,
        v_s_2806_,
    );
    leanh::lean_dec_ref(v_s_2806_);
    v_r_2809_ = leanh::lean_box((v_res_2808_) as usize);
    return v_r_2809_;
}
pub unsafe fn lean_string_contains(
    mut v_s_2810_: *mut leanh::LeanObject,
    mut v_c_2811_: u32,
) -> u8 {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    v___x_2812_ = leanh::lean_unsigned_to_nat(0);
    v___x_2813_ = lean_string_utf8_byte_size(v_s_2810_);
    v___x_2814_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2814_, 0, v_s_2810_);
    leanh::lean_ctor_set(v___x_2814_, 1, v___x_2812_);
    leanh::lean_ctor_set(v___x_2814_, 2, v___x_2813_);
    v___x_2815_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
        v_c_2811_,
        v___x_2814_,
    );
    leanh::lean_dec_ref_known(v___x_2814_, 3);
    return v___x_2815_;
}
pub unsafe fn l_String_Internal_containsImpl___boxed(
    mut v_s_2816_: *mut leanh::LeanObject,
    mut v_c_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2818_: u32 = 0;
    let mut v_res_2819_: u8 = 0;
    let mut v_r_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2818_ = leanh::lean_unbox_uint32(v_c_2817_);
    leanh::lean_dec(v_c_2817_);
    v_res_2819_ = lean_string_contains(v_s_2816_, v_c_boxed_2818_);
    v_r_2820_ = leanh::lean_box((v_res_2819_) as usize);
    return v_r_2820_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(
    mut v_s_2821_: *mut leanh::LeanObject,
    mut v_c_2822_: u32,
    mut v_inst_2823_: *mut leanh::LeanObject,
    mut v_R_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
    mut v_b_2826_: u8,
    mut v_c_2827_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2828_: u8 = 0;
    v___x_2828_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2821_, v_c_2822_, v_a_2825_, v_b_2826_);
    return v___x_2828_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(
    mut v_s_2829_: *mut leanh::LeanObject,
    mut v_c_2830_: *mut leanh::LeanObject,
    mut v_inst_2831_: *mut leanh::LeanObject,
    mut v_R_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_b_2834_: *mut leanh::LeanObject,
    mut v_c_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2836_: u32 = 0;
    let mut v_b_boxed_2837_: u8 = 0;
    let mut v_res_2838_: u8 = 0;
    let mut v_r_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2836_ = leanh::lean_unbox_uint32(v_c_2830_);
    leanh::lean_dec(v_c_2830_);
    v_b_boxed_2837_ = (leanh::lean_unbox(v_b_2834_) as u8);
    v_res_2838_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(v_s_2829_, v_c_boxed_2836_, v_inst_2831_, v_R_2832_, v_a_2833_, v_b_boxed_2837_, v_c_2835_);
    leanh::lean_dec_ref(v_s_2829_);
    v_r_2839_ = leanh::lean_box((v_res_2838_) as usize);
    return v_r_2839_;
}
pub unsafe fn l_String_any___redArg(
    mut v_inst_2840_: *mut leanh::LeanObject,
    mut v_s_2841_: *mut leanh::LeanObject,
    mut v_inst_2842_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    v___x_2843_ = leanh::lean_unsigned_to_nat(0);
    v___x_2844_ = lean_string_utf8_byte_size(v_s_2841_);
    v___x_2845_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2845_, 0, v_s_2841_);
    leanh::lean_ctor_set(v___x_2845_, 1, v___x_2843_);
    leanh::lean_ctor_set(v___x_2845_, 2, v___x_2844_);
    v___x_2846_ = l_String_Slice_contains___redArg(v_inst_2840_, v___x_2845_, v_inst_2842_);
    return v___x_2846_;
}
pub unsafe fn l_String_any___redArg___boxed(
    mut v_inst_2847_: *mut leanh::LeanObject,
    mut v_s_2848_: *mut leanh::LeanObject,
    mut v_inst_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2850_: u8 = 0;
    let mut v_r_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2850_ = l_String_any___redArg(v_inst_2847_, v_s_2848_, v_inst_2849_);
    v_r_2851_ = leanh::lean_box((v_res_2850_) as usize);
    return v_r_2851_;
}
pub unsafe fn l_String_any(
    mut v_00_u03c1_2852_: *mut leanh::LeanObject,
    mut v_00_u03c3_2853_: *mut leanh::LeanObject,
    mut v_inst_2854_: *mut leanh::LeanObject,
    mut v_inst_2855_: *mut leanh::LeanObject,
    mut v_s_2856_: *mut leanh::LeanObject,
    mut v_pat_2857_: *mut leanh::LeanObject,
    mut v_inst_2858_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    v___x_2859_ = leanh::lean_unsigned_to_nat(0);
    v___x_2860_ = lean_string_utf8_byte_size(v_s_2856_);
    v___x_2861_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2861_, 0, v_s_2856_);
    leanh::lean_ctor_set(v___x_2861_, 1, v___x_2859_);
    leanh::lean_ctor_set(v___x_2861_, 2, v___x_2860_);
    v___x_2862_ = l_String_Slice_contains___redArg(v_inst_2855_, v___x_2861_, v_inst_2858_);
    return v___x_2862_;
}
pub unsafe fn l_String_any___boxed(
    mut v_00_u03c1_2863_: *mut leanh::LeanObject,
    mut v_00_u03c3_2864_: *mut leanh::LeanObject,
    mut v_inst_2865_: *mut leanh::LeanObject,
    mut v_inst_2866_: *mut leanh::LeanObject,
    mut v_s_2867_: *mut leanh::LeanObject,
    mut v_pat_2868_: *mut leanh::LeanObject,
    mut v_inst_2869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2870_: u8 = 0;
    let mut v_r_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_String_any(
        v_00_u03c1_2863_,
        v_00_u03c3_2864_,
        v_inst_2865_,
        v_inst_2866_,
        v_s_2867_,
        v_pat_2868_,
        v_inst_2869_,
    );
    leanh::lean_dec(v_pat_2868_);
    leanh::lean_dec(v_inst_2865_);
    v_r_2871_ = leanh::lean_box((v_res_2870_) as usize);
    return v_r_2871_;
}
pub unsafe fn lean_string_any(
    mut v_s_2872_: *mut leanh::LeanObject,
    mut v_p_2873_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    v___x_2874_ = leanh::lean_unsigned_to_nat(0);
    v___x_2875_ = lean_string_utf8_byte_size(v_s_2872_);
    v___x_2876_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2876_, 0, v_s_2872_);
    leanh::lean_ctor_set(v___x_2876_, 1, v___x_2874_);
    leanh::lean_ctor_set(v___x_2876_, 2, v___x_2875_);
    v___x_2877_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2873_, v___x_2876_);
    leanh::lean_dec_ref_known(v___x_2876_, 3);
    return v___x_2877_;
}
pub unsafe fn l_String_Internal_anyImpl___boxed(
    mut v_s_2878_: *mut leanh::LeanObject,
    mut v_p_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2880_: u8 = 0;
    let mut v_r_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2880_ = lean_string_any(v_s_2878_, v_p_2879_);
    v_r_2881_ = leanh::lean_box((v_res_2880_) as usize);
    return v_r_2881_;
}
pub unsafe fn l_String_isNat(mut v_s_2882_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    v___x_2883_ = leanh::lean_unsigned_to_nat(0);
    v___x_2884_ = lean_string_utf8_byte_size(v_s_2882_);
    v___x_2885_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2885_, 0, v_s_2882_);
    leanh::lean_ctor_set(v___x_2885_, 1, v___x_2883_);
    leanh::lean_ctor_set(v___x_2885_, 2, v___x_2884_);
    v___x_2886_ = l_String_Slice_isNat(v___x_2885_);
    leanh::lean_dec_ref_known(v___x_2885_, 3);
    return v___x_2886_;
}
pub unsafe fn l_String_isNat___boxed(
    mut v_s_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2888_: u8 = 0;
    let mut v_r_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_String_isNat(v_s_2887_);
    v_r_2889_ = leanh::lean_box((v_res_2888_) as usize);
    return v_r_2889_;
}
pub unsafe fn l_String_toNat_x3f(
    mut v_s_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = leanh::lean_unsigned_to_nat(0);
    v___x_2892_ = lean_string_utf8_byte_size(v_s_2890_);
    v___x_2893_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2893_, 0, v_s_2890_);
    leanh::lean_ctor_set(v___x_2893_, 1, v___x_2891_);
    leanh::lean_ctor_set(v___x_2893_, 2, v___x_2892_);
    v___x_2894_ = l_String_Slice_toNat_x3f(v___x_2893_);
    leanh::lean_dec_ref_known(v___x_2893_, 3);
    return v___x_2894_;
}
pub unsafe fn l_String_toNat_x21(
    mut v_s_2895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = leanh::lean_unsigned_to_nat(0);
    v___x_2897_ = lean_string_utf8_byte_size(v_s_2895_);
    v___x_2898_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2898_, 0, v_s_2895_);
    leanh::lean_ctor_set(v___x_2898_, 1, v___x_2896_);
    leanh::lean_ctor_set(v___x_2898_, 2, v___x_2897_);
    v___x_2899_ = l_String_Slice_toNat_x21(v___x_2898_);
    leanh::lean_dec_ref_known(v___x_2898_, 3);
    return v___x_2899_;
}
pub unsafe fn l_String_toInt_x3f(
    mut v_s_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2901_ = leanh::lean_unsigned_to_nat(0);
    v___x_2902_ = lean_string_utf8_byte_size(v_s_2900_);
    v___x_2903_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2903_, 0, v_s_2900_);
    leanh::lean_ctor_set(v___x_2903_, 1, v___x_2901_);
    leanh::lean_ctor_set(v___x_2903_, 2, v___x_2902_);
    v___x_2904_ = l_String_Slice_toInt_x3f(v___x_2903_);
    return v___x_2904_;
}
pub unsafe fn l_String_isInt(mut v_s_2905_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: u8 = 0;
    v___x_2906_ = leanh::lean_unsigned_to_nat(0);
    v___x_2907_ = lean_string_utf8_byte_size(v_s_2905_);
    v___x_2908_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2908_, 0, v_s_2905_);
    leanh::lean_ctor_set(v___x_2908_, 1, v___x_2906_);
    leanh::lean_ctor_set(v___x_2908_, 2, v___x_2907_);
    v___x_2909_ = l_String_Slice_isInt(v___x_2908_);
    return v___x_2909_;
}
pub unsafe fn l_String_isInt___boxed(
    mut v_s_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2911_: u8 = 0;
    let mut v_r_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_String_isInt(v_s_2910_);
    v_r_2912_ = leanh::lean_box((v_res_2911_) as usize);
    return v_r_2912_;
}
pub unsafe fn l_String_toInt_x21(
    mut v_s_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = leanh::lean_unsigned_to_nat(0);
    v___x_2916_ = lean_string_utf8_byte_size(v_s_2914_);
    v___x_2917_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2917_, 0, v_s_2914_);
    leanh::lean_ctor_set(v___x_2917_, 1, v___x_2915_);
    leanh::lean_ctor_set(v___x_2917_, 2, v___x_2916_);
    v___x_2918_ = l_String_Slice_toInt_x3f(v___x_2917_);
    if leanh::lean_obj_tag(v___x_2918_) == 0 {
        let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2919_ = l_Int_instInhabited;
        v___x_2920_ = l_String_toInt_x21___closed__0;
        v___x_2921_ = l_panic___redArg(v___x_2919_, v___x_2920_);
        return v___x_2921_;
    } else {
        let mut v_val_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2922_ = leanh::lean_ctor_get(v___x_2918_, 0);
        leanh::lean_inc(v_val_2922_);
        leanh::lean_dec_ref_known(v___x_2918_, 1);
        return v_val_2922_;
    }
}
pub unsafe fn l_String_front_x3f(
    mut v_s_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = leanh::lean_unsigned_to_nat(0);
    v___x_2925_ = lean_string_utf8_byte_size(v_s_2923_);
    v___x_2926_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2926_, 0, v_s_2923_);
    leanh::lean_ctor_set(v___x_2926_, 1, v___x_2924_);
    leanh::lean_ctor_set(v___x_2926_, 2, v___x_2925_);
    v___x_2927_ = l_String_Slice_Pos_get_x3f(v___x_2926_, v___x_2924_);
    leanh::lean_dec_ref_known(v___x_2926_, 3);
    return v___x_2927_;
}
pub unsafe fn l_String_front(mut v_s_2928_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = leanh::lean_unsigned_to_nat(0);
    v___x_2930_ = lean_string_utf8_byte_size(v_s_2928_);
    v___x_2931_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2931_, 0, v_s_2928_);
    leanh::lean_ctor_set(v___x_2931_, 1, v___x_2929_);
    leanh::lean_ctor_set(v___x_2931_, 2, v___x_2930_);
    v___x_2932_ = l_String_Slice_Pos_get_x3f(v___x_2931_, v___x_2929_);
    leanh::lean_dec_ref_known(v___x_2931_, 3);
    if leanh::lean_obj_tag(v___x_2932_) == 0 {
        let mut v___x_2933_: u32 = 0;
        v___x_2933_ = 65;
        return v___x_2933_;
    } else {
        let mut v_val_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2935_: u32 = 0;
        v_val_2934_ = leanh::lean_ctor_get(v___x_2932_, 0);
        leanh::lean_inc(v_val_2934_);
        leanh::lean_dec_ref_known(v___x_2932_, 1);
        v___x_2935_ = leanh::lean_unbox_uint32(v_val_2934_);
        leanh::lean_dec(v_val_2934_);
        return v___x_2935_;
    }
}
pub unsafe fn l_String_front___boxed(
    mut v_s_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2937_: u32 = 0;
    let mut v_r_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_String_front(v_s_2936_);
    v_r_2938_ = leanh::lean_box_uint32(v_res_2937_);
    return v_r_2938_;
}
pub unsafe fn lean_string_front(mut v_s_2939_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = leanh::lean_unsigned_to_nat(0);
    v___x_2941_ = lean_string_utf8_byte_size(v_s_2939_);
    v___x_2942_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2942_, 0, v_s_2939_);
    leanh::lean_ctor_set(v___x_2942_, 1, v___x_2940_);
    leanh::lean_ctor_set(v___x_2942_, 2, v___x_2941_);
    v___x_2943_ = l_String_Slice_Pos_get_x3f(v___x_2942_, v___x_2940_);
    leanh::lean_dec_ref_known(v___x_2942_, 3);
    if leanh::lean_obj_tag(v___x_2943_) == 0 {
        let mut v___x_2944_: u32 = 0;
        v___x_2944_ = 65;
        return v___x_2944_;
    } else {
        let mut v_val_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: u32 = 0;
        v_val_2945_ = leanh::lean_ctor_get(v___x_2943_, 0);
        leanh::lean_inc(v_val_2945_);
        leanh::lean_dec_ref_known(v___x_2943_, 1);
        v___x_2946_ = leanh::lean_unbox_uint32(v_val_2945_);
        leanh::lean_dec(v_val_2945_);
        return v___x_2946_;
    }
}
pub unsafe fn l_String_Internal_frontImpl___boxed(
    mut v_s_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2948_: u32 = 0;
    let mut v_r_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = lean_string_front(v_s_2947_);
    v_r_2949_ = leanh::lean_box_uint32(v_res_2948_);
    return v_r_2949_;
}
pub unsafe fn l_String_back_x3f(
    mut v_s_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = leanh::lean_unsigned_to_nat(0);
    v___x_2952_ = lean_string_utf8_byte_size(v_s_2950_);
    v___x_2953_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2953_, 0, v_s_2950_);
    leanh::lean_ctor_set(v___x_2953_, 1, v___x_2951_);
    leanh::lean_ctor_set(v___x_2953_, 2, v___x_2952_);
    v___x_2954_ = l_String_Slice_Pos_prev_x3f(v___x_2953_, v___x_2952_);
    if leanh::lean_obj_tag(v___x_2954_) == 0 {
        let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2953_, 3);
        v___x_2955_ = leanh::lean_box(0);
        return v___x_2955_;
    } else {
        let mut v_val_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2956_ = leanh::lean_ctor_get(v___x_2954_, 0);
        leanh::lean_inc(v_val_2956_);
        leanh::lean_dec_ref_known(v___x_2954_, 1);
        v___x_2957_ = l_String_Slice_Pos_get_x3f(v___x_2953_, v_val_2956_);
        leanh::lean_dec(v_val_2956_);
        leanh::lean_dec_ref_known(v___x_2953_, 3);
        return v___x_2957_;
    }
}
pub unsafe fn l_String_back(mut v_s_2958_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = leanh::lean_unsigned_to_nat(0);
    v___x_2960_ = lean_string_utf8_byte_size(v_s_2958_);
    v___x_2961_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2961_, 0, v_s_2958_);
    leanh::lean_ctor_set(v___x_2961_, 1, v___x_2959_);
    leanh::lean_ctor_set(v___x_2961_, 2, v___x_2960_);
    v___x_2962_ = l_String_Slice_Pos_prev_x3f(v___x_2961_, v___x_2960_);
    if leanh::lean_obj_tag(v___x_2962_) == 0 {
        let mut v___x_2963_: u32 = 0;
        leanh::lean_dec_ref_known(v___x_2961_, 3);
        v___x_2963_ = 65;
        return v___x_2963_;
    } else {
        let mut v_val_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2964_ = leanh::lean_ctor_get(v___x_2962_, 0);
        leanh::lean_inc(v_val_2964_);
        leanh::lean_dec_ref_known(v___x_2962_, 1);
        v___x_2965_ = l_String_Slice_Pos_get_x3f(v___x_2961_, v_val_2964_);
        leanh::lean_dec(v_val_2964_);
        leanh::lean_dec_ref_known(v___x_2961_, 3);
        if leanh::lean_obj_tag(v___x_2965_) == 0 {
            let mut v___x_2966_: u32 = 0;
            v___x_2966_ = 65;
            return v___x_2966_;
        } else {
            let mut v_val_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2968_: u32 = 0;
            v_val_2967_ = leanh::lean_ctor_get(v___x_2965_, 0);
            leanh::lean_inc(v_val_2967_);
            leanh::lean_dec_ref_known(v___x_2965_, 1);
            v___x_2968_ = leanh::lean_unbox_uint32(v_val_2967_);
            leanh::lean_dec(v_val_2967_);
            return v___x_2968_;
        }
    }
}
pub unsafe fn l_String_back___boxed(
    mut v_s_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2970_: u32 = 0;
    let mut v_r_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2970_ = l_String_back(v_s_2969_);
    v_r_2971_ = leanh::lean_box_uint32(v_res_2970_);
    return v_r_2971_;
}
pub unsafe fn l_String_lines(
    mut v_s_2972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = leanh::lean_unsigned_to_nat(0);
    v___x_2974_ = lean_string_utf8_byte_size(v_s_2972_);
    v___x_2975_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2975_, 0, v_s_2972_);
    leanh::lean_ctor_set(v___x_2975_, 1, v___x_2973_);
    leanh::lean_ctor_set(v___x_2975_, 2, v___x_2974_);
    v___x_2976_ = l_String_Slice_lines(v___x_2975_);
    leanh::lean_dec_ref_known(v___x_2975_, 3);
    return v___x_2976_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Search(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Search(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Search(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Search(builtin);
}