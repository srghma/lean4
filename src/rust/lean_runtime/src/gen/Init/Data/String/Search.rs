// Lean compiler output
// Module: Init.Data.String.Search
// Imports: Init.Data.String.Slice Init.Data.Iterators.Consumers.Collect
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
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_is_valid_pos, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_7,
    lean_box, lean_box_uint32, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_String_Slice_Pos_find_x3f___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_Pos_find_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Slice_Pos_find_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_find_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_Pos_find_x3f___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_String_Slice_Pos_find_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_find_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l_String_toInt_x21___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_toInt_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_toInt_x21___closed__0_value) as *mut LeanObject;
pub unsafe fn l_String_replace___redArg(
    mut v_inst_1489_: *mut LeanObject,
    mut v_inst_1490_: *mut LeanObject,
    mut v_s_1491_: *mut LeanObject,
    mut v_inst_1492_: *mut LeanObject,
    mut v_replacement_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1494_ = lean_unsigned_to_nat(0);
    v___x_1495_ = lean_string_utf8_byte_size(v_s_1491_);
    v___x_1496_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1496_, 0, v_s_1491_);
    lean_ctor_set(v___x_1496_, 1, v___x_1494_);
    lean_ctor_set(v___x_1496_, 2, v___x_1495_);
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
    mut v_00_u03c1_1498_: *mut LeanObject,
    mut v_00_u03c3_1499_: *mut LeanObject,
    mut v_inst_1500_: *mut LeanObject,
    mut v_inst_1501_: *mut LeanObject,
    mut v_00_u03b1_1502_: *mut LeanObject,
    mut v_inst_1503_: *mut LeanObject,
    mut v_s_1504_: *mut LeanObject,
    mut v_pattern_1505_: *mut LeanObject,
    mut v_inst_1506_: *mut LeanObject,
    mut v_replacement_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    v___x_1508_ = lean_unsigned_to_nat(0);
    v___x_1509_ = lean_string_utf8_byte_size(v_s_1504_);
    v___x_1510_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1510_, 0, v_s_1504_);
    lean_ctor_set(v___x_1510_, 1, v___x_1508_);
    lean_ctor_set(v___x_1510_, 2, v___x_1509_);
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
    mut v_00_u03c1_1512_: *mut LeanObject,
    mut v_00_u03c3_1513_: *mut LeanObject,
    mut v_inst_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
    mut v_00_u03b1_1516_: *mut LeanObject,
    mut v_inst_1517_: *mut LeanObject,
    mut v_s_1518_: *mut LeanObject,
    mut v_pattern_1519_: *mut LeanObject,
    mut v_inst_1520_: *mut LeanObject,
    mut v_replacement_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1522_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1519_);
    lean_dec(v_inst_1514_);
    return v_res_1522_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__0(
    mut v_x_1523_: *mut LeanObject,
    mut v_x_1524_: *mut LeanObject,
    mut v_f_1525_: *mut LeanObject,
    mut v_c_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = lean_apply_1(v_f_1525_, v_c_1526_);
    return v___x_1527_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__1(
    mut v___x_1528_: *mut LeanObject,
    mut v_x1_1529_: *mut LeanObject,
    mut v_x2_1530_: *mut LeanObject,
    mut v_x3_1531_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x1_1529_) == 0 {
        let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
        v___x_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1532_, 0, v___x_1528_);
        return v___x_1532_;
    } else {
        let mut v_startPos_1533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1528_);
        v_startPos_1533_ = lean_ctor_get(v_x1_1529_, 0);
        lean_inc(v_startPos_1533_);
        v___x_1534_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1534_, 0, v_startPos_1533_);
        v___x_1535_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1535_, 0, v___x_1534_);
        return v___x_1535_;
    }
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg___lam__1___boxed(
    mut v___x_1536_: *mut LeanObject,
    mut v_x1_1537_: *mut LeanObject,
    mut v_x2_1538_: *mut LeanObject,
    mut v_x3_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1540_: *mut LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_String_Slice_Pos_find_x3f___redArg___lam__1(
        v___x_1536_,
        v_x1_1537_,
        v_x2_1538_,
        v_x3_1539_,
    );
    lean_dec(v_x3_1539_);
    lean_dec_ref(v_x1_1537_);
    return v_res_1540_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f___redArg(
    mut v_inst_1544_: *mut LeanObject,
    mut v_s_1545_: *mut LeanObject,
    mut v_pos_1546_: *mut LeanObject,
    mut v_inst_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___f_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1548_ = lean_ctor_get(v_s_1545_, 0);
                v_startInclusive_1549_ = lean_ctor_get(v_s_1545_, 1);
                v_endExclusive_1550_ = lean_ctor_get(v_s_1545_, 2);
                v_isSharedCheck_1572_ = (!lean_is_exclusive(v_s_1545_)) as u8;
                if v_isSharedCheck_1572_ == 0 {
                    v___x_1552_ = v_s_1545_;
                    v_isShared_1553_ = v_isSharedCheck_1572_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1550_);
                    lean_inc(v_startInclusive_1549_);
                    lean_inc(v_str_1548_);
                    lean_dec(v_s_1545_);
                    v___x_1552_ = lean_box(0);
                    v_isShared_1553_ = v_isSharedCheck_1572_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1554_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1555_ = lean_nat_add(v_startInclusive_1549_, v_pos_1546_);
                lean_dec(v_startInclusive_1549_);
                if v_isShared_1553_ == 0 {
                    lean_ctor_set(v___x_1552_, 1, v___x_1555_);
                    v___x_1557_ = v___x_1552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_str_1548_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1555_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_endExclusive_1550_);
                    v___x_1557_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_1557_);
                v_searcher_1558_ = lean_apply_1(v_inst_1547_, v___x_1557_);
                v___x_1559_ = lean_box(0);
                v___f_1560_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1561_ = lean_apply_7(
                    v_inst_1544_,
                    v___x_1557_,
                    v___f_1554_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1558_,
                    v___x_1559_,
                    v___f_1560_,
                );
                if lean_obj_tag(v___x_1561_) == 0 {
                    return v___x_1561_;
                } else {
                    v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
                    v_isSharedCheck_1570_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1564_ = v___x_1561_;
                        v_isShared_1565_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1562_);
                        lean_dec(v___x_1561_);
                        v___x_1564_ = lean_box(0);
                        v_isShared_1565_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1566_ = lean_nat_add(v_pos_1546_, v_val_1562_);
                lean_dec(v_val_1562_);
                if v_isShared_1565_ == 0 {
                    lean_ctor_set(v___x_1564_, 0, v___x_1566_);
                    v___x_1568_ = v___x_1564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
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
    mut v_inst_1573_: *mut LeanObject,
    mut v_s_1574_: *mut LeanObject,
    mut v_pos_1575_: *mut LeanObject,
    mut v_inst_1576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1577_: *mut LeanObject = core::ptr::null_mut();
    v_res_1577_ =
        l_String_Slice_Pos_find_x3f___redArg(v_inst_1573_, v_s_1574_, v_pos_1575_, v_inst_1576_);
    lean_dec(v_pos_1575_);
    return v_res_1577_;
}
pub unsafe fn l_String_Slice_Pos_find_x3f(
    mut v_00_u03c1_1578_: *mut LeanObject,
    mut v_00_u03c3_1579_: *mut LeanObject,
    mut v_inst_1580_: *mut LeanObject,
    mut v_inst_1581_: *mut LeanObject,
    mut v_s_1582_: *mut LeanObject,
    mut v_pos_1583_: *mut LeanObject,
    mut v_pattern_1584_: *mut LeanObject,
    mut v_inst_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___f_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_reuseFailAlloc_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1586_ = lean_ctor_get(v_s_1582_, 0);
                v_startInclusive_1587_ = lean_ctor_get(v_s_1582_, 1);
                v_endExclusive_1588_ = lean_ctor_get(v_s_1582_, 2);
                v_isSharedCheck_1610_ = (!lean_is_exclusive(v_s_1582_)) as u8;
                if v_isSharedCheck_1610_ == 0 {
                    v___x_1590_ = v_s_1582_;
                    v_isShared_1591_ = v_isSharedCheck_1610_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1588_);
                    lean_inc(v_startInclusive_1587_);
                    lean_inc(v_str_1586_);
                    lean_dec(v_s_1582_);
                    v___x_1590_ = lean_box(0);
                    v_isShared_1591_ = v_isSharedCheck_1610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1592_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1593_ = lean_nat_add(v_startInclusive_1587_, v_pos_1583_);
                lean_dec(v_startInclusive_1587_);
                if v_isShared_1591_ == 0 {
                    lean_ctor_set(v___x_1590_, 1, v___x_1593_);
                    v___x_1595_ = v___x_1590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_str_1586_);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1593_);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_endExclusive_1588_);
                    v___x_1595_ = v_reuseFailAlloc_1609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_1595_);
                v_searcher_1596_ = lean_apply_1(v_inst_1585_, v___x_1595_);
                v___x_1597_ = lean_box(0);
                v___f_1598_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1599_ = lean_apply_7(
                    v_inst_1581_,
                    v___x_1595_,
                    v___f_1592_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1596_,
                    v___x_1597_,
                    v___f_1598_,
                );
                if lean_obj_tag(v___x_1599_) == 0 {
                    return v___x_1599_;
                } else {
                    v_val_1600_ = lean_ctor_get(v___x_1599_, 0);
                    v_isSharedCheck_1608_ = (!lean_is_exclusive(v___x_1599_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v___x_1602_ = v___x_1599_;
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1600_);
                        lean_dec(v___x_1599_);
                        v___x_1602_ = lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1604_ = lean_nat_add(v_pos_1583_, v_val_1600_);
                lean_dec(v_val_1600_);
                if v_isShared_1603_ == 0 {
                    lean_ctor_set(v___x_1602_, 0, v___x_1604_);
                    v___x_1606_ = v___x_1602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
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
    mut v_00_u03c1_1611_: *mut LeanObject,
    mut v_00_u03c3_1612_: *mut LeanObject,
    mut v_inst_1613_: *mut LeanObject,
    mut v_inst_1614_: *mut LeanObject,
    mut v_s_1615_: *mut LeanObject,
    mut v_pos_1616_: *mut LeanObject,
    mut v_pattern_1617_: *mut LeanObject,
    mut v_inst_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1617_);
    lean_dec(v_pos_1616_);
    lean_dec(v_inst_1613_);
    return v_res_1619_;
}
pub unsafe fn l_String_Slice_Pos_find___redArg(
    mut v_inst_1620_: *mut LeanObject,
    mut v_s_1621_: *mut LeanObject,
    mut v_pos_1622_: *mut LeanObject,
    mut v_inst_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___f_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1624_ = lean_ctor_get(v_s_1621_, 0);
                v_startInclusive_1625_ = lean_ctor_get(v_s_1621_, 1);
                v_endExclusive_1626_ = lean_ctor_get(v_s_1621_, 2);
                v_isSharedCheck_1643_ = (!lean_is_exclusive(v_s_1621_)) as u8;
                if v_isSharedCheck_1643_ == 0 {
                    v___x_1628_ = v_s_1621_;
                    v_isShared_1629_ = v_isSharedCheck_1643_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1626_);
                    lean_inc(v_startInclusive_1625_);
                    lean_inc(v_str_1624_);
                    lean_dec(v_s_1621_);
                    v___x_1628_ = lean_box(0);
                    v_isShared_1629_ = v_isSharedCheck_1643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1630_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1631_ = lean_nat_add(v_startInclusive_1625_, v_pos_1622_);
                lean_dec(v_startInclusive_1625_);
                lean_inc(v_endExclusive_1626_);
                lean_inc(v___x_1631_);
                if v_isShared_1629_ == 0 {
                    lean_ctor_set(v___x_1628_, 1, v___x_1631_);
                    v___x_1633_ = v___x_1628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_str_1624_);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1631_);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_endExclusive_1626_);
                    v___x_1633_ = v_reuseFailAlloc_1642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_1633_);
                v_searcher_1634_ = lean_apply_1(v_inst_1623_, v___x_1633_);
                v___x_1635_ = lean_box(0);
                v___f_1636_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1637_ = lean_apply_7(
                    v_inst_1620_,
                    v___x_1633_,
                    v___f_1630_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1634_,
                    v___x_1635_,
                    v___f_1636_,
                );
                if lean_obj_tag(v___x_1637_) == 0 {
                    v___x_1638_ = lean_nat_sub(v_endExclusive_1626_, v___x_1631_);
                    lean_dec(v___x_1631_);
                    lean_dec(v_endExclusive_1626_);
                    v___x_1639_ = lean_nat_add(v_pos_1622_, v___x_1638_);
                    lean_dec(v___x_1638_);
                    return v___x_1639_;
                } else {
                    lean_dec(v___x_1631_);
                    lean_dec(v_endExclusive_1626_);
                    v_val_1640_ = lean_ctor_get(v___x_1637_, 0);
                    lean_inc(v_val_1640_);
                    lean_dec_ref_known(v___x_1637_, 1);
                    v___x_1641_ = lean_nat_add(v_pos_1622_, v_val_1640_);
                    lean_dec(v_val_1640_);
                    return v___x_1641_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find___redArg___boxed(
    mut v_inst_1644_: *mut LeanObject,
    mut v_s_1645_: *mut LeanObject,
    mut v_pos_1646_: *mut LeanObject,
    mut v_inst_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ =
        l_String_Slice_Pos_find___redArg(v_inst_1644_, v_s_1645_, v_pos_1646_, v_inst_1647_);
    lean_dec(v_pos_1646_);
    return v_res_1648_;
}
pub unsafe fn l_String_Slice_Pos_find(
    mut v_00_u03c1_1649_: *mut LeanObject,
    mut v_00_u03c3_1650_: *mut LeanObject,
    mut v_inst_1651_: *mut LeanObject,
    mut v_inst_1652_: *mut LeanObject,
    mut v_s_1653_: *mut LeanObject,
    mut v_pos_1654_: *mut LeanObject,
    mut v_pattern_1655_: *mut LeanObject,
    mut v_inst_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___f_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1657_ = lean_ctor_get(v_s_1653_, 0);
                v_startInclusive_1658_ = lean_ctor_get(v_s_1653_, 1);
                v_endExclusive_1659_ = lean_ctor_get(v_s_1653_, 2);
                v_isSharedCheck_1676_ = (!lean_is_exclusive(v_s_1653_)) as u8;
                if v_isSharedCheck_1676_ == 0 {
                    v___x_1661_ = v_s_1653_;
                    v_isShared_1662_ = v_isSharedCheck_1676_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1659_);
                    lean_inc(v_startInclusive_1658_);
                    lean_inc(v_str_1657_);
                    lean_dec(v_s_1653_);
                    v___x_1661_ = lean_box(0);
                    v_isShared_1662_ = v_isSharedCheck_1676_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1663_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1664_ = lean_nat_add(v_startInclusive_1658_, v_pos_1654_);
                lean_dec(v_startInclusive_1658_);
                lean_inc(v_endExclusive_1659_);
                lean_inc(v___x_1664_);
                if v_isShared_1662_ == 0 {
                    lean_ctor_set(v___x_1661_, 1, v___x_1664_);
                    v___x_1666_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_str_1657_);
                    lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1664_);
                    lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_endExclusive_1659_);
                    v___x_1666_ = v_reuseFailAlloc_1675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_1666_);
                v_searcher_1667_ = lean_apply_1(v_inst_1656_, v___x_1666_);
                v___x_1668_ = lean_box(0);
                v___f_1669_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1670_ = lean_apply_7(
                    v_inst_1652_,
                    v___x_1666_,
                    v___f_1663_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1667_,
                    v___x_1668_,
                    v___f_1669_,
                );
                if lean_obj_tag(v___x_1670_) == 0 {
                    v___x_1671_ = lean_nat_sub(v_endExclusive_1659_, v___x_1664_);
                    lean_dec(v___x_1664_);
                    lean_dec(v_endExclusive_1659_);
                    v___x_1672_ = lean_nat_add(v_pos_1654_, v___x_1671_);
                    lean_dec(v___x_1671_);
                    return v___x_1672_;
                } else {
                    lean_dec(v___x_1664_);
                    lean_dec(v_endExclusive_1659_);
                    v_val_1673_ = lean_ctor_get(v___x_1670_, 0);
                    lean_inc(v_val_1673_);
                    lean_dec_ref_known(v___x_1670_, 1);
                    v___x_1674_ = lean_nat_add(v_pos_1654_, v_val_1673_);
                    lean_dec(v_val_1673_);
                    return v___x_1674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_find___boxed(
    mut v_00_u03c1_1677_: *mut LeanObject,
    mut v_00_u03c3_1678_: *mut LeanObject,
    mut v_inst_1679_: *mut LeanObject,
    mut v_inst_1680_: *mut LeanObject,
    mut v_s_1681_: *mut LeanObject,
    mut v_pos_1682_: *mut LeanObject,
    mut v_pattern_1683_: *mut LeanObject,
    mut v_inst_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1685_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1683_);
    lean_dec(v_pos_1682_);
    lean_dec(v_inst_1679_);
    return v_res_1685_;
}
pub unsafe fn l_String_Pos_find_x3f___redArg(
    mut v_inst_1686_: *mut LeanObject,
    mut v_s_1687_: *mut LeanObject,
    mut v_pos_1688_: *mut LeanObject,
    mut v_inst_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1690_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1691_ = lean_string_utf8_byte_size(v_s_1687_);
                lean_inc(v_pos_1688_);
                v___x_1692_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1692_, 0, v_s_1687_);
                lean_ctor_set(v___x_1692_, 1, v_pos_1688_);
                lean_ctor_set(v___x_1692_, 2, v___x_1691_);
                lean_inc_ref(v___x_1692_);
                v_searcher_1693_ = lean_apply_1(v_inst_1689_, v___x_1692_);
                v___x_1694_ = lean_box(0);
                v___f_1695_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1696_ = lean_apply_7(
                    v_inst_1686_,
                    v___x_1692_,
                    v___f_1690_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1693_,
                    v___x_1694_,
                    v___f_1695_,
                );
                if lean_obj_tag(v___x_1696_) == 0 {
                    lean_dec(v_pos_1688_);
                    return v___x_1694_;
                } else {
                    v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
                    v_isSharedCheck_1705_ = (!lean_is_exclusive(v___x_1696_)) as u8;
                    if v_isSharedCheck_1705_ == 0 {
                        v___x_1699_ = v___x_1696_;
                        v_isShared_1700_ = v_isSharedCheck_1705_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1697_);
                        lean_dec(v___x_1696_);
                        v___x_1699_ = lean_box(0);
                        v_isShared_1700_ = v_isSharedCheck_1705_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1701_ = lean_nat_add(v_pos_1688_, v_val_1697_);
                lean_dec(v_val_1697_);
                lean_dec(v_pos_1688_);
                if v_isShared_1700_ == 0 {
                    lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
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
    mut v_00_u03c1_1706_: *mut LeanObject,
    mut v_00_u03c3_1707_: *mut LeanObject,
    mut v_inst_1708_: *mut LeanObject,
    mut v_inst_1709_: *mut LeanObject,
    mut v_s_1710_: *mut LeanObject,
    mut v_pos_1711_: *mut LeanObject,
    mut v_pattern_1712_: *mut LeanObject,
    mut v_inst_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1714_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1715_ = lean_string_utf8_byte_size(v_s_1710_);
                lean_inc(v_pos_1711_);
                v___x_1716_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1716_, 0, v_s_1710_);
                lean_ctor_set(v___x_1716_, 1, v_pos_1711_);
                lean_ctor_set(v___x_1716_, 2, v___x_1715_);
                lean_inc_ref(v___x_1716_);
                v_searcher_1717_ = lean_apply_1(v_inst_1713_, v___x_1716_);
                v___x_1718_ = lean_box(0);
                v___f_1719_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1720_ = lean_apply_7(
                    v_inst_1709_,
                    v___x_1716_,
                    v___f_1714_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1717_,
                    v___x_1718_,
                    v___f_1719_,
                );
                if lean_obj_tag(v___x_1720_) == 0 {
                    lean_dec(v_pos_1711_);
                    return v___x_1718_;
                } else {
                    v_val_1721_ = lean_ctor_get(v___x_1720_, 0);
                    v_isSharedCheck_1729_ = (!lean_is_exclusive(v___x_1720_)) as u8;
                    if v_isSharedCheck_1729_ == 0 {
                        v___x_1723_ = v___x_1720_;
                        v_isShared_1724_ = v_isSharedCheck_1729_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1721_);
                        lean_dec(v___x_1720_);
                        v___x_1723_ = lean_box(0);
                        v_isShared_1724_ = v_isSharedCheck_1729_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1725_ = lean_nat_add(v_pos_1711_, v_val_1721_);
                lean_dec(v_val_1721_);
                lean_dec(v_pos_1711_);
                if v_isShared_1724_ == 0 {
                    lean_ctor_set(v___x_1723_, 0, v___x_1725_);
                    v___x_1727_ = v___x_1723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
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
    mut v_00_u03c1_1730_: *mut LeanObject,
    mut v_00_u03c3_1731_: *mut LeanObject,
    mut v_inst_1732_: *mut LeanObject,
    mut v_inst_1733_: *mut LeanObject,
    mut v_s_1734_: *mut LeanObject,
    mut v_pos_1735_: *mut LeanObject,
    mut v_pattern_1736_: *mut LeanObject,
    mut v_inst_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1738_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1736_);
    lean_dec(v_inst_1732_);
    return v_res_1738_;
}
pub unsafe fn l_String_Pos_find___redArg(
    mut v_inst_1739_: *mut LeanObject,
    mut v_s_1740_: *mut LeanObject,
    mut v_pos_1741_: *mut LeanObject,
    mut v_inst_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___f_1743_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1744_ = lean_string_utf8_byte_size(v_s_1740_);
    lean_inc(v_pos_1741_);
    v___x_1745_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1745_, 0, v_s_1740_);
    lean_ctor_set(v___x_1745_, 1, v_pos_1741_);
    lean_ctor_set(v___x_1745_, 2, v___x_1744_);
    lean_inc_ref(v___x_1745_);
    v_searcher_1746_ = lean_apply_1(v_inst_1742_, v___x_1745_);
    v___x_1747_ = lean_box(0);
    v___f_1748_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1749_ = lean_apply_7(
        v_inst_1739_,
        v___x_1745_,
        v___f_1743_,
        lean_box(0),
        lean_box(0),
        v_searcher_1746_,
        v___x_1747_,
        v___f_1748_,
    );
    if lean_obj_tag(v___x_1749_) == 0 {
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        v___x_1750_ = lean_nat_sub(v___x_1744_, v_pos_1741_);
        v___x_1751_ = lean_nat_add(v_pos_1741_, v___x_1750_);
        lean_dec(v___x_1750_);
        lean_dec(v_pos_1741_);
        return v___x_1751_;
    } else {
        let mut v_val_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
        v_val_1752_ = lean_ctor_get(v___x_1749_, 0);
        lean_inc(v_val_1752_);
        lean_dec_ref_known(v___x_1749_, 1);
        v___x_1753_ = lean_nat_add(v_pos_1741_, v_val_1752_);
        lean_dec(v_val_1752_);
        lean_dec(v_pos_1741_);
        return v___x_1753_;
    }
}
pub unsafe fn l_String_Pos_find(
    mut v_00_u03c1_1754_: *mut LeanObject,
    mut v_00_u03c3_1755_: *mut LeanObject,
    mut v_inst_1756_: *mut LeanObject,
    mut v_inst_1757_: *mut LeanObject,
    mut v_s_1758_: *mut LeanObject,
    mut v_pos_1759_: *mut LeanObject,
    mut v_pattern_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    v___f_1762_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1763_ = lean_string_utf8_byte_size(v_s_1758_);
    lean_inc(v_pos_1759_);
    v___x_1764_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1764_, 0, v_s_1758_);
    lean_ctor_set(v___x_1764_, 1, v_pos_1759_);
    lean_ctor_set(v___x_1764_, 2, v___x_1763_);
    lean_inc_ref(v___x_1764_);
    v_searcher_1765_ = lean_apply_1(v_inst_1761_, v___x_1764_);
    v___x_1766_ = lean_box(0);
    v___f_1767_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1768_ = lean_apply_7(
        v_inst_1757_,
        v___x_1764_,
        v___f_1762_,
        lean_box(0),
        lean_box(0),
        v_searcher_1765_,
        v___x_1766_,
        v___f_1767_,
    );
    if lean_obj_tag(v___x_1768_) == 0 {
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        v___x_1769_ = lean_nat_sub(v___x_1763_, v_pos_1759_);
        v___x_1770_ = lean_nat_add(v_pos_1759_, v___x_1769_);
        lean_dec(v___x_1769_);
        lean_dec(v_pos_1759_);
        return v___x_1770_;
    } else {
        let mut v_val_1771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
        v_val_1771_ = lean_ctor_get(v___x_1768_, 0);
        lean_inc(v_val_1771_);
        lean_dec_ref_known(v___x_1768_, 1);
        v___x_1772_ = lean_nat_add(v_pos_1759_, v_val_1771_);
        lean_dec(v_val_1771_);
        lean_dec(v_pos_1759_);
        return v___x_1772_;
    }
}
pub unsafe fn l_String_Pos_find___boxed(
    mut v_00_u03c1_1773_: *mut LeanObject,
    mut v_00_u03c3_1774_: *mut LeanObject,
    mut v_inst_1775_: *mut LeanObject,
    mut v_inst_1776_: *mut LeanObject,
    mut v_s_1777_: *mut LeanObject,
    mut v_pos_1778_: *mut LeanObject,
    mut v_pattern_1779_: *mut LeanObject,
    mut v_inst_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1781_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1779_);
    lean_dec(v_inst_1775_);
    return v_res_1781_;
}
pub unsafe fn l_String_find_x3f___redArg(
    mut v_inst_1782_: *mut LeanObject,
    mut v_s_1783_: *mut LeanObject,
    mut v_inst_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1785_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1786_ = lean_unsigned_to_nat(0);
                v___x_1787_ = lean_string_utf8_byte_size(v_s_1783_);
                v___x_1788_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v_s_1783_);
                lean_ctor_set(v___x_1788_, 1, v___x_1786_);
                lean_ctor_set(v___x_1788_, 2, v___x_1787_);
                lean_inc_ref(v___x_1788_);
                v_searcher_1789_ = lean_apply_1(v_inst_1784_, v___x_1788_);
                v___x_1790_ = lean_box(0);
                v___f_1791_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1792_ = lean_apply_7(
                    v_inst_1782_,
                    v___x_1788_,
                    v___f_1785_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1789_,
                    v___x_1790_,
                    v___f_1791_,
                );
                if lean_obj_tag(v___x_1792_) == 0 {
                    return v___x_1790_;
                } else {
                    v_val_1793_ = lean_ctor_get(v___x_1792_, 0);
                    v_isSharedCheck_1800_ = (!lean_is_exclusive(v___x_1792_)) as u8;
                    if v_isSharedCheck_1800_ == 0 {
                        v___x_1795_ = v___x_1792_;
                        v_isShared_1796_ = v_isSharedCheck_1800_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1793_);
                        lean_dec(v___x_1792_);
                        v___x_1795_ = lean_box(0);
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
                    v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_val_1793_);
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
    mut v_00_u03c1_1801_: *mut LeanObject,
    mut v_00_u03c3_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_s_1805_: *mut LeanObject,
    mut v_pattern_1806_: *mut LeanObject,
    mut v_inst_1807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1808_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
                v___x_1809_ = lean_unsigned_to_nat(0);
                v___x_1810_ = lean_string_utf8_byte_size(v_s_1805_);
                v___x_1811_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1811_, 0, v_s_1805_);
                lean_ctor_set(v___x_1811_, 1, v___x_1809_);
                lean_ctor_set(v___x_1811_, 2, v___x_1810_);
                lean_inc_ref(v___x_1811_);
                v_searcher_1812_ = lean_apply_1(v_inst_1807_, v___x_1811_);
                v___x_1813_ = lean_box(0);
                v___f_1814_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
                v___x_1815_ = lean_apply_7(
                    v_inst_1804_,
                    v___x_1811_,
                    v___f_1808_,
                    lean_box(0),
                    lean_box(0),
                    v_searcher_1812_,
                    v___x_1813_,
                    v___f_1814_,
                );
                if lean_obj_tag(v___x_1815_) == 0 {
                    return v___x_1813_;
                } else {
                    v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
                    v_isSharedCheck_1823_ = (!lean_is_exclusive(v___x_1815_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1815_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1816_);
                        lean_dec(v___x_1815_);
                        v___x_1818_ = lean_box(0);
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
                    v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1816_);
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
    mut v_00_u03c1_1824_: *mut LeanObject,
    mut v_00_u03c3_1825_: *mut LeanObject,
    mut v_inst_1826_: *mut LeanObject,
    mut v_inst_1827_: *mut LeanObject,
    mut v_s_1828_: *mut LeanObject,
    mut v_pattern_1829_: *mut LeanObject,
    mut v_inst_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1831_: *mut LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_String_find_x3f(
        v_00_u03c1_1824_,
        v_00_u03c3_1825_,
        v_inst_1826_,
        v_inst_1827_,
        v_s_1828_,
        v_pattern_1829_,
        v_inst_1830_,
    );
    lean_dec(v_pattern_1829_);
    lean_dec(v_inst_1826_);
    return v_res_1831_;
}
pub unsafe fn l_String_find___redArg(
    mut v_inst_1832_: *mut LeanObject,
    mut v_s_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    v___f_1835_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1836_ = lean_unsigned_to_nat(0);
    v___x_1837_ = lean_string_utf8_byte_size(v_s_1833_);
    v___x_1838_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1838_, 0, v_s_1833_);
    lean_ctor_set(v___x_1838_, 1, v___x_1836_);
    lean_ctor_set(v___x_1838_, 2, v___x_1837_);
    lean_inc_ref(v___x_1838_);
    v_searcher_1839_ = lean_apply_1(v_inst_1834_, v___x_1838_);
    v___x_1840_ = lean_box(0);
    v___f_1841_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1842_ = lean_apply_7(
        v_inst_1832_,
        v___x_1838_,
        v___f_1835_,
        lean_box(0),
        lean_box(0),
        v_searcher_1839_,
        v___x_1840_,
        v___f_1841_,
    );
    if lean_obj_tag(v___x_1842_) == 0 {
        return v___x_1837_;
    } else {
        let mut v_val_1843_: *mut LeanObject = core::ptr::null_mut();
        v_val_1843_ = lean_ctor_get(v___x_1842_, 0);
        lean_inc(v_val_1843_);
        lean_dec_ref_known(v___x_1842_, 1);
        return v_val_1843_;
    }
}
pub unsafe fn l_String_find(
    mut v_00_u03c1_1844_: *mut LeanObject,
    mut v_00_u03c3_1845_: *mut LeanObject,
    mut v_inst_1846_: *mut LeanObject,
    mut v_inst_1847_: *mut LeanObject,
    mut v_s_1848_: *mut LeanObject,
    mut v_pattern_1849_: *mut LeanObject,
    mut v_inst_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___f_1851_ = l_String_Slice_Pos_find_x3f___redArg___closed__0;
    v___x_1852_ = lean_unsigned_to_nat(0);
    v___x_1853_ = lean_string_utf8_byte_size(v_s_1848_);
    v___x_1854_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1854_, 0, v_s_1848_);
    lean_ctor_set(v___x_1854_, 1, v___x_1852_);
    lean_ctor_set(v___x_1854_, 2, v___x_1853_);
    lean_inc_ref(v___x_1854_);
    v_searcher_1855_ = lean_apply_1(v_inst_1850_, v___x_1854_);
    v___x_1856_ = lean_box(0);
    v___f_1857_ = l_String_Slice_Pos_find_x3f___redArg___closed__1;
    v___x_1858_ = lean_apply_7(
        v_inst_1847_,
        v___x_1854_,
        v___f_1851_,
        lean_box(0),
        lean_box(0),
        v_searcher_1855_,
        v___x_1856_,
        v___f_1857_,
    );
    if lean_obj_tag(v___x_1858_) == 0 {
        return v___x_1853_;
    } else {
        let mut v_val_1859_: *mut LeanObject = core::ptr::null_mut();
        v_val_1859_ = lean_ctor_get(v___x_1858_, 0);
        lean_inc(v_val_1859_);
        lean_dec_ref_known(v___x_1858_, 1);
        return v_val_1859_;
    }
}
pub unsafe fn l_String_find___boxed(
    mut v_00_u03c1_1860_: *mut LeanObject,
    mut v_00_u03c3_1861_: *mut LeanObject,
    mut v_inst_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
    mut v_s_1864_: *mut LeanObject,
    mut v_pattern_1865_: *mut LeanObject,
    mut v_inst_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_String_find(
        v_00_u03c1_1860_,
        v_00_u03c3_1861_,
        v_inst_1862_,
        v_inst_1863_,
        v_s_1864_,
        v_pattern_1865_,
        v_inst_1866_,
    );
    lean_dec(v_pattern_1865_);
    lean_dec(v_inst_1862_);
    return v_res_1867_;
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f___redArg(
    mut v_inst_1868_: *mut LeanObject,
    mut v_s_1869_: *mut LeanObject,
    mut v_pos_1870_: *mut LeanObject,
    mut v_inst_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut v_reuseFailAlloc_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut v_unused_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1872_ = lean_ctor_get(v_s_1869_, 0);
                v_startInclusive_1873_ = lean_ctor_get(v_s_1869_, 1);
                v_isSharedCheck_1890_ = (!lean_is_exclusive(v_s_1869_)) as u8;
                if v_isSharedCheck_1890_ == 0 {
                    v_unused_1891_ = lean_ctor_get(v_s_1869_, 2);
                    lean_dec(v_unused_1891_);
                    v___x_1875_ = v_s_1869_;
                    v_isShared_1876_ = v_isSharedCheck_1890_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_startInclusive_1873_);
                    lean_inc(v_str_1872_);
                    lean_dec(v_s_1869_);
                    v___x_1875_ = lean_box(0);
                    v_isShared_1876_ = v_isSharedCheck_1890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1877_ = lean_nat_add(v_startInclusive_1873_, v_pos_1870_);
                if v_isShared_1876_ == 0 {
                    lean_ctor_set(v___x_1875_, 2, v___x_1877_);
                    v___x_1879_ = v___x_1875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_str_1872_);
                    lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_startInclusive_1873_);
                    lean_ctor_set(v_reuseFailAlloc_1889_, 2, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1880_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1868_, v___x_1879_, v_inst_1871_);
                if lean_obj_tag(v___x_1880_) == 0 {
                    return v___x_1880_;
                } else {
                    v_val_1881_ = lean_ctor_get(v___x_1880_, 0);
                    v_isSharedCheck_1888_ = (!lean_is_exclusive(v___x_1880_)) as u8;
                    if v_isSharedCheck_1888_ == 0 {
                        v___x_1883_ = v___x_1880_;
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1881_);
                        lean_dec(v___x_1880_);
                        v___x_1883_ = lean_box(0);
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
                    v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_val_1881_);
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
    mut v_inst_1892_: *mut LeanObject,
    mut v_s_1893_: *mut LeanObject,
    mut v_pos_1894_: *mut LeanObject,
    mut v_inst_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1896_: *mut LeanObject = core::ptr::null_mut();
    v_res_1896_ =
        l_String_Slice_Pos_revFind_x3f___redArg(v_inst_1892_, v_s_1893_, v_pos_1894_, v_inst_1895_);
    lean_dec(v_pos_1894_);
    return v_res_1896_;
}
pub unsafe fn l_String_Slice_Pos_revFind_x3f(
    mut v_00_u03c1_1897_: *mut LeanObject,
    mut v_00_u03c3_1898_: *mut LeanObject,
    mut v_inst_1899_: *mut LeanObject,
    mut v_inst_1900_: *mut LeanObject,
    mut v_s_1901_: *mut LeanObject,
    mut v_pos_1902_: *mut LeanObject,
    mut v_pattern_1903_: *mut LeanObject,
    mut v_inst_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_reuseFailAlloc_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v_unused_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1905_ = lean_ctor_get(v_s_1901_, 0);
                v_startInclusive_1906_ = lean_ctor_get(v_s_1901_, 1);
                v_isSharedCheck_1923_ = (!lean_is_exclusive(v_s_1901_)) as u8;
                if v_isSharedCheck_1923_ == 0 {
                    v_unused_1924_ = lean_ctor_get(v_s_1901_, 2);
                    lean_dec(v_unused_1924_);
                    v___x_1908_ = v_s_1901_;
                    v_isShared_1909_ = v_isSharedCheck_1923_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_startInclusive_1906_);
                    lean_inc(v_str_1905_);
                    lean_dec(v_s_1901_);
                    v___x_1908_ = lean_box(0);
                    v_isShared_1909_ = v_isSharedCheck_1923_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = lean_nat_add(v_startInclusive_1906_, v_pos_1902_);
                if v_isShared_1909_ == 0 {
                    lean_ctor_set(v___x_1908_, 2, v___x_1910_);
                    v___x_1912_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_str_1905_);
                    lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_startInclusive_1906_);
                    lean_ctor_set(v_reuseFailAlloc_1922_, 2, v___x_1910_);
                    v___x_1912_ = v_reuseFailAlloc_1922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1913_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1900_, v___x_1912_, v_inst_1904_);
                if lean_obj_tag(v___x_1913_) == 0 {
                    return v___x_1913_;
                } else {
                    v_val_1914_ = lean_ctor_get(v___x_1913_, 0);
                    v_isSharedCheck_1921_ = (!lean_is_exclusive(v___x_1913_)) as u8;
                    if v_isSharedCheck_1921_ == 0 {
                        v___x_1916_ = v___x_1913_;
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1914_);
                        lean_dec(v___x_1913_);
                        v___x_1916_ = lean_box(0);
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
                    v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_val_1914_);
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
    mut v_00_u03c1_1925_: *mut LeanObject,
    mut v_00_u03c3_1926_: *mut LeanObject,
    mut v_inst_1927_: *mut LeanObject,
    mut v_inst_1928_: *mut LeanObject,
    mut v_s_1929_: *mut LeanObject,
    mut v_pos_1930_: *mut LeanObject,
    mut v_pattern_1931_: *mut LeanObject,
    mut v_inst_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1931_);
    lean_dec(v_pos_1930_);
    lean_dec(v_inst_1927_);
    return v_res_1933_;
}
pub unsafe fn l_String_Pos_revFind_x3f___redArg(
    mut v_inst_1934_: *mut LeanObject,
    mut v_s_1935_: *mut LeanObject,
    mut v_pos_1936_: *mut LeanObject,
    mut v_inst_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1938_ = lean_unsigned_to_nat(0);
                v___x_1939_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1939_, 0, v_s_1935_);
                lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                lean_ctor_set(v___x_1939_, 2, v_pos_1936_);
                v___x_1940_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1934_, v___x_1939_, v_inst_1937_);
                if lean_obj_tag(v___x_1940_) == 0 {
                    if lean_obj_tag(v___x_1940_) == 0 {
                        v___x_1941_ = lean_box(0);
                        return v___x_1941_;
                    } else {
                        v_val_1942_ = lean_ctor_get(v___x_1940_, 0);
                        lean_inc(v_val_1942_);
                        lean_dec_ref_known(v___x_1940_, 1);
                        v___x_1943_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1943_, 0, v_val_1942_);
                        return v___x_1943_;
                    }
                } else {
                    v_val_1944_ = lean_ctor_get(v___x_1940_, 0);
                    v_isSharedCheck_1951_ = (!lean_is_exclusive(v___x_1940_)) as u8;
                    if v_isSharedCheck_1951_ == 0 {
                        v___x_1946_ = v___x_1940_;
                        v_isShared_1947_ = v_isSharedCheck_1951_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1944_);
                        lean_dec(v___x_1940_);
                        v___x_1946_ = lean_box(0);
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
                    v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_val_1944_);
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
    mut v_00_u03c1_1952_: *mut LeanObject,
    mut v_00_u03c3_1953_: *mut LeanObject,
    mut v_inst_1954_: *mut LeanObject,
    mut v_inst_1955_: *mut LeanObject,
    mut v_s_1956_: *mut LeanObject,
    mut v_pos_1957_: *mut LeanObject,
    mut v_pattern_1958_: *mut LeanObject,
    mut v_inst_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1960_ = lean_unsigned_to_nat(0);
                v___x_1961_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1961_, 0, v_s_1956_);
                lean_ctor_set(v___x_1961_, 1, v___x_1960_);
                lean_ctor_set(v___x_1961_, 2, v_pos_1957_);
                v___x_1962_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1955_, v___x_1961_, v_inst_1959_);
                if lean_obj_tag(v___x_1962_) == 0 {
                    if lean_obj_tag(v___x_1962_) == 0 {
                        v___x_1963_ = lean_box(0);
                        return v___x_1963_;
                    } else {
                        v_val_1964_ = lean_ctor_get(v___x_1962_, 0);
                        lean_inc(v_val_1964_);
                        lean_dec_ref_known(v___x_1962_, 1);
                        v___x_1965_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1965_, 0, v_val_1964_);
                        return v___x_1965_;
                    }
                } else {
                    v_val_1966_ = lean_ctor_get(v___x_1962_, 0);
                    v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1962_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v___x_1968_ = v___x_1962_;
                        v_isShared_1969_ = v_isSharedCheck_1973_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1966_);
                        lean_dec(v___x_1962_);
                        v___x_1968_ = lean_box(0);
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
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_val_1966_);
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
    mut v_00_u03c1_1974_: *mut LeanObject,
    mut v_00_u03c3_1975_: *mut LeanObject,
    mut v_inst_1976_: *mut LeanObject,
    mut v_inst_1977_: *mut LeanObject,
    mut v_s_1978_: *mut LeanObject,
    mut v_pos_1979_: *mut LeanObject,
    mut v_pattern_1980_: *mut LeanObject,
    mut v_inst_1981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1982_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_pattern_1980_);
    lean_dec(v_inst_1976_);
    return v_res_1982_;
}
pub unsafe fn l_String_revFind_x3f___redArg(
    mut v_inst_1983_: *mut LeanObject,
    mut v_s_1984_: *mut LeanObject,
    mut v_inst_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1986_ = lean_unsigned_to_nat(0);
                v___x_1987_ = lean_string_utf8_byte_size(v_s_1984_);
                v___x_1988_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1988_, 0, v_s_1984_);
                lean_ctor_set(v___x_1988_, 1, v___x_1986_);
                lean_ctor_set(v___x_1988_, 2, v___x_1987_);
                v___x_1989_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_1983_, v___x_1988_, v_inst_1985_);
                if lean_obj_tag(v___x_1989_) == 0 {
                    v___x_1990_ = lean_box(0);
                    return v___x_1990_;
                } else {
                    v_val_1991_ = lean_ctor_get(v___x_1989_, 0);
                    v_isSharedCheck_1998_ = (!lean_is_exclusive(v___x_1989_)) as u8;
                    if v_isSharedCheck_1998_ == 0 {
                        v___x_1993_ = v___x_1989_;
                        v_isShared_1994_ = v_isSharedCheck_1998_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1991_);
                        lean_dec(v___x_1989_);
                        v___x_1993_ = lean_box(0);
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
                    v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_val_1991_);
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
    mut v_00_u03c1_1999_: *mut LeanObject,
    mut v_00_u03c3_2000_: *mut LeanObject,
    mut v_inst_2001_: *mut LeanObject,
    mut v_inst_2002_: *mut LeanObject,
    mut v_s_2003_: *mut LeanObject,
    mut v_pattern_2004_: *mut LeanObject,
    mut v_inst_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = lean_unsigned_to_nat(0);
                v___x_2007_ = lean_string_utf8_byte_size(v_s_2003_);
                v___x_2008_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2008_, 0, v_s_2003_);
                lean_ctor_set(v___x_2008_, 1, v___x_2006_);
                lean_ctor_set(v___x_2008_, 2, v___x_2007_);
                v___x_2009_ =
                    l_String_Slice_revFind_x3f___redArg(v_inst_2002_, v___x_2008_, v_inst_2005_);
                if lean_obj_tag(v___x_2009_) == 0 {
                    v___x_2010_ = lean_box(0);
                    return v___x_2010_;
                } else {
                    v_val_2011_ = lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2018_ = (!lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v___x_2013_ = v___x_2009_;
                        v_isShared_2014_ = v_isSharedCheck_2018_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2011_);
                        lean_dec(v___x_2009_);
                        v___x_2013_ = lean_box(0);
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
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_val_2011_);
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
    mut v_00_u03c1_2019_: *mut LeanObject,
    mut v_00_u03c3_2020_: *mut LeanObject,
    mut v_inst_2021_: *mut LeanObject,
    mut v_inst_2022_: *mut LeanObject,
    mut v_s_2023_: *mut LeanObject,
    mut v_pattern_2024_: *mut LeanObject,
    mut v_inst_2025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2026_: *mut LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_String_revFind_x3f(
        v_00_u03c1_2019_,
        v_00_u03c3_2020_,
        v_inst_2021_,
        v_inst_2022_,
        v_s_2023_,
        v_pattern_2024_,
        v_inst_2025_,
    );
    lean_dec(v_pattern_2024_);
    lean_dec(v_inst_2021_);
    return v_res_2026_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
    mut v___x_2027_: *mut LeanObject,
    mut v_s_2028_: *mut LeanObject,
    mut v_c_2029_: u32,
    mut v_a_2030_: *mut LeanObject,
    mut v_b_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: u32 = 0;
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2032_ = lean_ctor_get(v___x_2027_, 1);
                v_endExclusive_2033_ = lean_ctor_get(v___x_2027_, 2);
                v___x_2034_ = lean_nat_sub(v_endExclusive_2033_, v_startInclusive_2032_);
                v___x_2035_ = lean_nat_dec_eq(v_a_2030_, v___x_2034_);
                lean_dec(v___x_2034_);
                if v___x_2035_ == 0 {
                    v___x_2036_ = lean_string_utf8_get_fast(v_s_2028_, v_a_2030_);
                    v___x_2037_ = lean_uint32_dec_eq(v___x_2036_, v_c_2029_);
                    if v___x_2037_ == 0 {
                        v___x_2038_ = lean_box(0);
                        v___x_2039_ = lean_string_utf8_next_fast(v_s_2028_, v_a_2030_);
                        lean_dec(v_a_2030_);
                        v_a_2030_ = v___x_2039_;
                        v_b_2031_ = v___x_2038_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2041_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2041_, 0, v_a_2030_);
                        return v___x_2041_;
                    }
                } else {
                    lean_dec(v_a_2030_);
                    lean_inc(v_b_2031_);
                    return v_b_2031_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg___boxed(
    mut v___x_2042_: *mut LeanObject,
    mut v_s_2043_: *mut LeanObject,
    mut v_c_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_b_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2047_: u32 = 0;
    let mut v_res_2048_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2047_ = lean_unbox_uint32(v_c_2044_);
    lean_dec(v_c_2044_);
    v_res_2048_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2042_,
        v_s_2043_,
        v_c_boxed_2047_,
        v_a_2045_,
        v_b_2046_,
    );
    lean_dec(v_b_2046_);
    lean_dec_ref(v_s_2043_);
    lean_dec_ref(v___x_2042_);
    return v_res_2048_;
}
pub unsafe fn lean_string_posof(
    mut v_s_2049_: *mut LeanObject,
    mut v_c_2050_: u32,
) -> *mut LeanObject {
    let mut v_searcher_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    v_searcher_2051_ = lean_unsigned_to_nat(0);
    v___x_2052_ = lean_string_utf8_byte_size(v_s_2049_);
    lean_inc_ref(v_s_2049_);
    v___x_2053_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2053_, 0, v_s_2049_);
    lean_ctor_set(v___x_2053_, 1, v_searcher_2051_);
    lean_ctor_set(v___x_2053_, 2, v___x_2052_);
    v___x_2054_ = lean_box(0);
    v___x_2055_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2053_,
        v_s_2049_,
        v_c_2050_,
        v_searcher_2051_,
        v___x_2054_,
    );
    lean_dec_ref(v_s_2049_);
    lean_dec_ref_known(v___x_2053_, 3);
    if lean_obj_tag(v___x_2055_) == 0 {
        return v___x_2052_;
    } else {
        let mut v_val_2056_: *mut LeanObject = core::ptr::null_mut();
        v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
        lean_inc(v_val_2056_);
        lean_dec_ref_known(v___x_2055_, 1);
        return v_val_2056_;
    }
}
pub unsafe fn l_String_Internal_posOfImpl___boxed(
    mut v_s_2057_: *mut LeanObject,
    mut v_c_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2059_: u32 = 0;
    let mut v_res_2060_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2059_ = lean_unbox_uint32(v_c_2058_);
    lean_dec(v_c_2058_);
    v_res_2060_ = lean_string_posof(v_s_2057_, v_c_boxed_2059_);
    return v_res_2060_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0(
    mut v___x_2061_: *mut LeanObject,
    mut v_s_2062_: *mut LeanObject,
    mut v_c_2063_: u32,
    mut v_inst_2064_: *mut LeanObject,
    mut v_R_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_b_2067_: *mut LeanObject,
    mut v_c_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_2070_: *mut LeanObject,
    mut v_s_2071_: *mut LeanObject,
    mut v_c_2072_: *mut LeanObject,
    mut v_inst_2073_: *mut LeanObject,
    mut v_R_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v_b_2076_: *mut LeanObject,
    mut v_c_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2078_: u32 = 0;
    let mut v_res_2079_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2078_ = lean_unbox_uint32(v_c_2072_);
    lean_dec(v_c_2072_);
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
    lean_dec(v_b_2076_);
    lean_dec_ref(v_s_2071_);
    lean_dec_ref(v___x_2070_);
    return v_res_2079_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
    mut v___x_2080_: *mut LeanObject,
    mut v_pos_2081_: *mut LeanObject,
    mut v_s_2082_: *mut LeanObject,
    mut v_p_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_b_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u32 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2086_ = lean_ctor_get(v___x_2080_, 1);
                v_endExclusive_2087_ = lean_ctor_get(v___x_2080_, 2);
                v___x_2088_ = lean_nat_sub(v_endExclusive_2087_, v_startInclusive_2086_);
                v___x_2089_ = lean_nat_dec_eq(v_a_2084_, v___x_2088_);
                lean_dec(v___x_2088_);
                if v___x_2089_ == 0 {
                    v___x_2090_ = lean_nat_add(v_pos_2081_, v_a_2084_);
                    v___x_2091_ = lean_string_utf8_get_fast(v_s_2082_, v___x_2090_);
                    v___x_2092_ = lean_box_uint32(v___x_2091_);
                    lean_inc_ref(v_p_2083_);
                    v___x_2093_ = lean_apply_1(v_p_2083_, v___x_2092_);
                    v___x_2094_ = (lean_unbox(v___x_2093_) as u8);
                    if v___x_2094_ == 0 {
                        lean_dec(v_a_2084_);
                        v___x_2095_ = lean_box(0);
                        v___x_2096_ = lean_string_utf8_next_fast(v_s_2082_, v___x_2090_);
                        lean_dec(v___x_2090_);
                        v___x_2097_ = lean_nat_sub(v___x_2096_, v_pos_2081_);
                        v_a_2084_ = v___x_2097_;
                        v_b_2085_ = v___x_2095_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2090_);
                        lean_dec_ref(v_p_2083_);
                        v___x_2099_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2099_, 0, v_a_2084_);
                        return v___x_2099_;
                    }
                } else {
                    lean_dec(v_a_2084_);
                    lean_dec_ref(v_p_2083_);
                    lean_inc(v_b_2085_);
                    return v_b_2085_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg___boxed(
    mut v___x_2100_: *mut LeanObject,
    mut v_pos_2101_: *mut LeanObject,
    mut v_s_2102_: *mut LeanObject,
    mut v_p_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
    mut v_b_2105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2106_: *mut LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
        v___x_2100_,
        v_pos_2101_,
        v_s_2102_,
        v_p_2103_,
        v_a_2104_,
        v_b_2105_,
    );
    lean_dec(v_b_2105_);
    lean_dec_ref(v_s_2102_);
    lean_dec(v_pos_2101_);
    lean_dec_ref(v___x_2100_);
    return v_res_2106_;
}
pub unsafe fn l_String_findAux(
    mut v_s_2107_: *mut LeanObject,
    mut v_p_2108_: *mut LeanObject,
    mut v_stopPos_2109_: *mut LeanObject,
    mut v_pos_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2111_: u8 = 0;
    v___x_2111_ = lean_nat_dec_le(v_pos_2110_, v_stopPos_2109_);
    if v___x_2111_ == 0 {
        lean_dec(v_pos_2110_);
        lean_dec_ref(v_p_2108_);
        lean_dec_ref(v_s_2107_);
        return v_stopPos_2109_;
    } else {
        let mut v___x_2112_: u8 = 0;
        v___x_2112_ = lean_string_is_valid_pos(v_s_2107_, v_pos_2110_);
        if v___x_2112_ == 0 {
            lean_dec(v_pos_2110_);
            lean_dec_ref(v_p_2108_);
            lean_dec_ref(v_s_2107_);
            return v_stopPos_2109_;
        } else {
            let mut v___x_2113_: u8 = 0;
            v___x_2113_ = lean_string_is_valid_pos(v_s_2107_, v_stopPos_2109_);
            if v___x_2113_ == 0 {
                lean_dec(v_pos_2110_);
                lean_dec_ref(v_p_2108_);
                lean_dec_ref(v_s_2107_);
                return v_stopPos_2109_;
            } else {
                let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
                let mut v_searcher_2115_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_stopPos_2109_);
                lean_inc(v_pos_2110_);
                lean_inc_ref(v_s_2107_);
                v___x_2114_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v_s_2107_);
                lean_ctor_set(v___x_2114_, 1, v_pos_2110_);
                lean_ctor_set(v___x_2114_, 2, v_stopPos_2109_);
                v_searcher_2115_ = lean_unsigned_to_nat(0);
                v___x_2116_ = lean_box(0);
                v___x_2117_ =
                    l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0___redArg(
                        v___x_2114_,
                        v_pos_2110_,
                        v_s_2107_,
                        v_p_2108_,
                        v_searcher_2115_,
                        v___x_2116_,
                    );
                lean_dec_ref(v_s_2107_);
                lean_dec_ref_known(v___x_2114_, 3);
                if lean_obj_tag(v___x_2117_) == 0 {
                    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2118_ = lean_nat_sub(v_stopPos_2109_, v_pos_2110_);
                    lean_dec(v_stopPos_2109_);
                    v___x_2119_ = lean_nat_add(v_pos_2110_, v___x_2118_);
                    lean_dec(v___x_2118_);
                    lean_dec(v_pos_2110_);
                    return v___x_2119_;
                } else {
                    let mut v_val_2120_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_stopPos_2109_);
                    v_val_2120_ = lean_ctor_get(v___x_2117_, 0);
                    lean_inc(v_val_2120_);
                    lean_dec_ref_known(v___x_2117_, 1);
                    v___x_2121_ = lean_nat_add(v_pos_2110_, v_val_2120_);
                    lean_dec(v_val_2120_);
                    lean_dec(v_pos_2110_);
                    return v___x_2121_;
                }
            }
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_findAux_spec__0(
    mut v___x_2122_: *mut LeanObject,
    mut v_pos_2123_: *mut LeanObject,
    mut v_s_2124_: *mut LeanObject,
    mut v_p_2125_: *mut LeanObject,
    mut v_inst_2126_: *mut LeanObject,
    mut v_R_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_b_2129_: *mut LeanObject,
    mut v_c_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_2132_: *mut LeanObject,
    mut v_pos_2133_: *mut LeanObject,
    mut v_s_2134_: *mut LeanObject,
    mut v_p_2135_: *mut LeanObject,
    mut v_inst_2136_: *mut LeanObject,
    mut v_R_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_b_2139_: *mut LeanObject,
    mut v_c_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_b_2139_);
    lean_dec_ref(v_s_2134_);
    lean_dec(v_pos_2133_);
    lean_dec_ref(v___x_2132_);
    return v_res_2141_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
    mut v___x_2142_: *mut LeanObject,
    mut v_pos_2143_: *mut LeanObject,
    mut v_s_2144_: *mut LeanObject,
    mut v_c_2145_: u32,
    mut v_a_2146_: *mut LeanObject,
    mut v_b_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: u32 = 0;
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2148_ = lean_ctor_get(v___x_2142_, 1);
                v_endExclusive_2149_ = lean_ctor_get(v___x_2142_, 2);
                v___x_2150_ = lean_nat_sub(v_endExclusive_2149_, v_startInclusive_2148_);
                v___x_2151_ = lean_nat_dec_eq(v_a_2146_, v___x_2150_);
                lean_dec(v___x_2150_);
                if v___x_2151_ == 0 {
                    v___x_2152_ = lean_nat_add(v_pos_2143_, v_a_2146_);
                    v___x_2153_ = lean_string_utf8_get_fast(v_s_2144_, v___x_2152_);
                    v___x_2154_ = lean_uint32_dec_eq(v___x_2153_, v_c_2145_);
                    if v___x_2154_ == 0 {
                        lean_dec(v_a_2146_);
                        v___x_2155_ = lean_box(0);
                        v___x_2156_ = lean_string_utf8_next_fast(v_s_2144_, v___x_2152_);
                        lean_dec(v___x_2152_);
                        v___x_2157_ = lean_nat_sub(v___x_2156_, v_pos_2143_);
                        v_a_2146_ = v___x_2157_;
                        v_b_2147_ = v___x_2155_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2152_);
                        v___x_2159_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2159_, 0, v_a_2146_);
                        return v___x_2159_;
                    }
                } else {
                    lean_dec(v_a_2146_);
                    lean_inc(v_b_2147_);
                    return v_b_2147_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg___boxed(
    mut v___x_2160_: *mut LeanObject,
    mut v_pos_2161_: *mut LeanObject,
    mut v_s_2162_: *mut LeanObject,
    mut v_c_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_b_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2166_: u32 = 0;
    let mut v_res_2167_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2166_ = lean_unbox_uint32(v_c_2163_);
    lean_dec(v_c_2163_);
    v_res_2167_ = l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
        v___x_2160_,
        v_pos_2161_,
        v_s_2162_,
        v_c_boxed_2166_,
        v_a_2164_,
        v_b_2165_,
    );
    lean_dec(v_b_2165_);
    lean_dec_ref(v_s_2162_);
    lean_dec(v_pos_2161_);
    lean_dec_ref(v___x_2160_);
    return v_res_2167_;
}
pub unsafe fn l_String_posOfAux(
    mut v_s_2168_: *mut LeanObject,
    mut v_c_2169_: u32,
    mut v_stopPos_2170_: *mut LeanObject,
    mut v_pos_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2172_: u8 = 0;
    v___x_2172_ = lean_nat_dec_le(v_pos_2171_, v_stopPos_2170_);
    if v___x_2172_ == 0 {
        lean_dec(v_pos_2171_);
        lean_dec_ref(v_s_2168_);
        return v_stopPos_2170_;
    } else {
        let mut v___x_2173_: u8 = 0;
        v___x_2173_ = lean_string_is_valid_pos(v_s_2168_, v_pos_2171_);
        if v___x_2173_ == 0 {
            lean_dec(v_pos_2171_);
            lean_dec_ref(v_s_2168_);
            return v_stopPos_2170_;
        } else {
            let mut v___x_2174_: u8 = 0;
            v___x_2174_ = lean_string_is_valid_pos(v_s_2168_, v_stopPos_2170_);
            if v___x_2174_ == 0 {
                lean_dec(v_pos_2171_);
                lean_dec_ref(v_s_2168_);
                return v_stopPos_2170_;
            } else {
                let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
                let mut v_searcher_2176_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_stopPos_2170_);
                lean_inc(v_pos_2171_);
                lean_inc_ref(v_s_2168_);
                v___x_2175_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v_s_2168_);
                lean_ctor_set(v___x_2175_, 1, v_pos_2171_);
                lean_ctor_set(v___x_2175_, 2, v_stopPos_2170_);
                v_searcher_2176_ = lean_unsigned_to_nat(0);
                v___x_2177_ = lean_box(0);
                v___x_2178_ =
                    l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0___redArg(
                        v___x_2175_,
                        v_pos_2171_,
                        v_s_2168_,
                        v_c_2169_,
                        v_searcher_2176_,
                        v___x_2177_,
                    );
                lean_dec_ref(v_s_2168_);
                lean_dec_ref_known(v___x_2175_, 3);
                if lean_obj_tag(v___x_2178_) == 0 {
                    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2179_ = lean_nat_sub(v_stopPos_2170_, v_pos_2171_);
                    lean_dec(v_stopPos_2170_);
                    v___x_2180_ = lean_nat_add(v_pos_2171_, v___x_2179_);
                    lean_dec(v___x_2179_);
                    lean_dec(v_pos_2171_);
                    return v___x_2180_;
                } else {
                    let mut v_val_2181_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_stopPos_2170_);
                    v_val_2181_ = lean_ctor_get(v___x_2178_, 0);
                    lean_inc(v_val_2181_);
                    lean_dec_ref_known(v___x_2178_, 1);
                    v___x_2182_ = lean_nat_add(v_pos_2171_, v_val_2181_);
                    lean_dec(v_val_2181_);
                    lean_dec(v_pos_2171_);
                    return v___x_2182_;
                }
            }
        }
    }
}
pub unsafe fn l_String_posOfAux___boxed(
    mut v_s_2183_: *mut LeanObject,
    mut v_c_2184_: *mut LeanObject,
    mut v_stopPos_2185_: *mut LeanObject,
    mut v_pos_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2187_: u32 = 0;
    let mut v_res_2188_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2187_ = lean_unbox_uint32(v_c_2184_);
    lean_dec(v_c_2184_);
    v_res_2188_ = l_String_posOfAux(v_s_2183_, v_c_boxed_2187_, v_stopPos_2185_, v_pos_2186_);
    return v_res_2188_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_posOfAux_spec__0(
    mut v___x_2189_: *mut LeanObject,
    mut v_pos_2190_: *mut LeanObject,
    mut v_s_2191_: *mut LeanObject,
    mut v_c_2192_: u32,
    mut v_inst_2193_: *mut LeanObject,
    mut v_R_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_b_2196_: *mut LeanObject,
    mut v_c_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_2199_: *mut LeanObject,
    mut v_pos_2200_: *mut LeanObject,
    mut v_s_2201_: *mut LeanObject,
    mut v_c_2202_: *mut LeanObject,
    mut v_inst_2203_: *mut LeanObject,
    mut v_R_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_b_2206_: *mut LeanObject,
    mut v_c_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2208_: u32 = 0;
    let mut v_res_2209_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2208_ = lean_unbox_uint32(v_c_2202_);
    lean_dec(v_c_2202_);
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
    lean_dec(v_b_2206_);
    lean_dec_ref(v_s_2201_);
    lean_dec(v_pos_2200_);
    lean_dec_ref(v___x_2199_);
    return v_res_2209_;
}
pub unsafe fn l_String_posOf(
    mut v_s_2210_: *mut LeanObject,
    mut v_c_2211_: u32,
) -> *mut LeanObject {
    let mut v_searcher_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    v_searcher_2212_ = lean_unsigned_to_nat(0);
    v___x_2213_ = lean_string_utf8_byte_size(v_s_2210_);
    lean_inc_ref(v_s_2210_);
    v___x_2214_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2214_, 0, v_s_2210_);
    lean_ctor_set(v___x_2214_, 1, v_searcher_2212_);
    lean_ctor_set(v___x_2214_, 2, v___x_2213_);
    v___x_2215_ = lean_box(0);
    v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_posOfImpl_spec__0___redArg(
        v___x_2214_,
        v_s_2210_,
        v_c_2211_,
        v_searcher_2212_,
        v___x_2215_,
    );
    lean_dec_ref(v_s_2210_);
    lean_dec_ref_known(v___x_2214_, 3);
    if lean_obj_tag(v___x_2216_) == 0 {
        return v___x_2213_;
    } else {
        let mut v_val_2217_: *mut LeanObject = core::ptr::null_mut();
        v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
        lean_inc(v_val_2217_);
        lean_dec_ref_known(v___x_2216_, 1);
        return v_val_2217_;
    }
}
pub unsafe fn l_String_posOf___boxed(
    mut v_s_2218_: *mut LeanObject,
    mut v_c_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2220_: u32 = 0;
    let mut v_res_2221_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2220_ = lean_unbox_uint32(v_c_2219_);
    lean_dec(v_c_2219_);
    v_res_2221_ = l_String_posOf(v_s_2218_, v_c_boxed_2220_);
    return v_res_2221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(
    mut v_s_2222_: *mut LeanObject,
    mut v_c_2223_: u32,
    mut v_a_2224_: *mut LeanObject,
    mut v_b_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v_str_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u32 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2226_ = lean_unsigned_to_nat(0);
                v___x_2227_ = lean_nat_dec_eq(v_a_2224_, v___x_2226_);
                if v___x_2227_ == 0 {
                    v_str_2228_ = lean_ctor_get(v_s_2222_, 0);
                    v_startInclusive_2229_ = lean_ctor_get(v_s_2222_, 1);
                    v___x_2230_ = lean_nat_add(v_startInclusive_2229_, v_a_2224_);
                    lean_inc(v___x_2230_);
                    lean_inc(v_startInclusive_2229_);
                    lean_inc_ref(v_str_2228_);
                    v___x_2231_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2231_, 0, v_str_2228_);
                    lean_ctor_set(v___x_2231_, 1, v_startInclusive_2229_);
                    lean_ctor_set(v___x_2231_, 2, v___x_2230_);
                    v___x_2232_ = lean_nat_sub(v___x_2230_, v_startInclusive_2229_);
                    lean_dec(v___x_2230_);
                    v___x_2233_ = lean_unsigned_to_nat(1);
                    v___x_2234_ = lean_nat_sub(v___x_2232_, v___x_2233_);
                    lean_dec(v___x_2232_);
                    v___x_2235_ = l_String_Slice_posLE(v___x_2231_, v___x_2234_);
                    lean_dec_ref_known(v___x_2231_, 3);
                    v___x_2236_ = lean_nat_add(v_startInclusive_2229_, v___x_2235_);
                    v___x_2237_ = lean_string_utf8_get_fast(v_str_2228_, v___x_2236_);
                    lean_dec(v___x_2236_);
                    v___x_2238_ = lean_uint32_dec_eq(v___x_2237_, v_c_2223_);
                    if v___x_2238_ == 0 {
                        lean_dec(v___x_2235_);
                        v___x_2239_ = lean_box(0);
                        v___x_2240_ = lean_nat_sub(v_a_2224_, v___x_2233_);
                        lean_dec(v_a_2224_);
                        v___x_2241_ = l_String_Slice_posLE(v_s_2222_, v___x_2240_);
                        v_a_2224_ = v___x_2241_;
                        v_b_2225_ = v___x_2239_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_2224_);
                        v___x_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2243_, 0, v___x_2235_);
                        return v___x_2243_;
                    }
                } else {
                    lean_dec(v_a_2224_);
                    lean_inc(v_b_2225_);
                    return v_b_2225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2244_: *mut LeanObject,
    mut v_c_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_b_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2248_: u32 = 0;
    let mut v_res_2249_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2248_ = lean_unbox_uint32(v_c_2245_);
    lean_dec(v_c_2245_);
    v_res_2249_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2244_, v_c_boxed_2248_, v_a_2246_, v_b_2247_);
    lean_dec(v_b_2247_);
    lean_dec_ref(v_s_2244_);
    return v_res_2249_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
    mut v_c_2250_: u32,
    mut v_s_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_2252_ = lean_ctor_get(v_s_2251_, 1);
    v_endExclusive_2253_ = lean_ctor_get(v_s_2251_, 2);
    v_searcher_2254_ = lean_nat_sub(v_endExclusive_2253_, v_startInclusive_2252_);
    v___x_2255_ = lean_box(0);
    v___x_2256_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2251_, v_c_2250_, v_searcher_2254_, v___x_2255_);
    return v___x_2256_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0___boxed(
    mut v_c_2257_: *mut LeanObject,
    mut v_s_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2259_: u32 = 0;
    let mut v_res_2260_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2259_ = lean_unbox_uint32(v_c_2257_);
    lean_dec(v_c_2257_);
    v_res_2260_ =
        l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(v_c_boxed_2259_, v_s_2258_);
    lean_dec_ref(v_s_2258_);
    return v_res_2260_;
}
pub unsafe fn l_String_revPosOfAux(
    mut v_s_2261_: *mut LeanObject,
    mut v_c_2262_: u32,
    mut v_pos_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2264_ = lean_unsigned_to_nat(0);
                v___x_2265_ = lean_string_utf8_byte_size(v_s_2261_);
                lean_inc_ref(v_s_2261_);
                v___x_2266_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2266_, 0, v_s_2261_);
                lean_ctor_set(v___x_2266_, 1, v___x_2264_);
                lean_ctor_set(v___x_2266_, 2, v___x_2265_);
                v___x_2267_ = l_String_Slice_pos_x3f(v___x_2266_, v_pos_2263_);
                lean_dec_ref_known(v___x_2266_, 3);
                if lean_obj_tag(v___x_2267_) == 0 {
                    lean_dec_ref(v_s_2261_);
                    v___x_2268_ = lean_box(0);
                    return v___x_2268_;
                } else {
                    v_val_2269_ = lean_ctor_get(v___x_2267_, 0);
                    v_isSharedCheck_2288_ = (!lean_is_exclusive(v___x_2267_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2271_ = v___x_2267_;
                        v_isShared_2272_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2269_);
                        lean_dec(v___x_2267_);
                        v___x_2271_ = lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2273_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2273_, 0, v_s_2261_);
                lean_ctor_set(v___x_2273_, 1, v___x_2264_);
                lean_ctor_set(v___x_2273_, 2, v_val_2269_);
                v___x_2274_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
                    v_c_2262_,
                    v___x_2273_,
                );
                lean_dec_ref_known(v___x_2273_, 3);
                if lean_obj_tag(v___x_2274_) == 0 {
                    if lean_obj_tag(v___x_2274_) == 0 {
                        lean_del_object(v___x_2271_);
                        v___x_2275_ = lean_box(0);
                        return v___x_2275_;
                    } else {
                        v_val_2276_ = lean_ctor_get(v___x_2274_, 0);
                        lean_inc(v_val_2276_);
                        lean_dec_ref_known(v___x_2274_, 1);
                        if v_isShared_2272_ == 0 {
                            lean_ctor_set(v___x_2271_, 0, v_val_2276_);
                            v___x_2278_ = v___x_2271_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_val_2276_);
                            v___x_2278_ = v_reuseFailAlloc_2279_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2271_);
                    v_val_2280_ = lean_ctor_get(v___x_2274_, 0);
                    v_isSharedCheck_2287_ = (!lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2287_ == 0 {
                        v___x_2282_ = v___x_2274_;
                        v_isShared_2283_ = v_isSharedCheck_2287_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2280_);
                        lean_dec(v___x_2274_);
                        v___x_2282_ = lean_box(0);
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
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_val_2280_);
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
    mut v_s_2289_: *mut LeanObject,
    mut v_c_2290_: *mut LeanObject,
    mut v_pos_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2292_: u32 = 0;
    let mut v_res_2293_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2292_ = lean_unbox_uint32(v_c_2290_);
    lean_dec(v_c_2290_);
    v_res_2293_ = l_String_revPosOfAux(v_s_2289_, v_c_boxed_2292_, v_pos_2291_);
    return v_res_2293_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(
    mut v_s_2294_: *mut LeanObject,
    mut v_c_2295_: u32,
    mut v_inst_2296_: *mut LeanObject,
    mut v_R_2297_: *mut LeanObject,
    mut v_a_2298_: *mut LeanObject,
    mut v_b_2299_: *mut LeanObject,
    mut v_c_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___redArg(v_s_2294_, v_c_2295_, v_a_2298_, v_b_2299_);
    return v___x_2301_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0___boxed(
    mut v_s_2302_: *mut LeanObject,
    mut v_c_2303_: *mut LeanObject,
    mut v_inst_2304_: *mut LeanObject,
    mut v_R_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_b_2307_: *mut LeanObject,
    mut v_c_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2309_: u32 = 0;
    let mut v_res_2310_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2309_ = lean_unbox_uint32(v_c_2303_);
    lean_dec(v_c_2303_);
    v_res_2310_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0_spec__0(v_s_2302_, v_c_boxed_2309_, v_inst_2304_, v_R_2305_, v_a_2306_, v_b_2307_, v_c_2308_);
    lean_dec(v_b_2307_);
    lean_dec_ref(v_s_2302_);
    return v_res_2310_;
}
pub unsafe fn l_String_revPosOf(
    mut v_s_2311_: *mut LeanObject,
    mut v_c_2312_: u32,
) -> *mut LeanObject {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2313_ = lean_unsigned_to_nat(0);
                v___x_2314_ = lean_string_utf8_byte_size(v_s_2311_);
                v___x_2315_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2315_, 0, v_s_2311_);
                lean_ctor_set(v___x_2315_, 1, v___x_2313_);
                lean_ctor_set(v___x_2315_, 2, v___x_2314_);
                v___x_2316_ = l_String_Slice_revFind_x3f___at___00String_revPosOfAux_spec__0(
                    v_c_2312_,
                    v___x_2315_,
                );
                lean_dec_ref_known(v___x_2315_, 3);
                if lean_obj_tag(v___x_2316_) == 0 {
                    v___x_2317_ = lean_box(0);
                    return v___x_2317_;
                } else {
                    v_val_2318_ = lean_ctor_get(v___x_2316_, 0);
                    v_isSharedCheck_2325_ = (!lean_is_exclusive(v___x_2316_)) as u8;
                    if v_isSharedCheck_2325_ == 0 {
                        v___x_2320_ = v___x_2316_;
                        v_isShared_2321_ = v_isSharedCheck_2325_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2318_);
                        lean_dec(v___x_2316_);
                        v___x_2320_ = lean_box(0);
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
                    v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_val_2318_);
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
    mut v_s_2326_: *mut LeanObject,
    mut v_c_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2328_: u32 = 0;
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2328_ = lean_unbox_uint32(v_c_2327_);
    lean_dec(v_c_2327_);
    v_res_2329_ = l_String_revPosOf(v_s_2326_, v_c_boxed_2328_);
    return v_res_2329_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(
    mut v_s_2330_: *mut LeanObject,
    mut v_p_2331_: *mut LeanObject,
    mut v_a_2332_: *mut LeanObject,
    mut v_b_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v_str_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: u32 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = lean_unsigned_to_nat(0);
                v___x_2335_ = lean_nat_dec_eq(v_a_2332_, v___x_2334_);
                if v___x_2335_ == 0 {
                    v_str_2336_ = lean_ctor_get(v_s_2330_, 0);
                    v_startInclusive_2337_ = lean_ctor_get(v_s_2330_, 1);
                    v___x_2338_ = lean_nat_add(v_startInclusive_2337_, v_a_2332_);
                    lean_inc(v___x_2338_);
                    lean_inc(v_startInclusive_2337_);
                    lean_inc_ref(v_str_2336_);
                    v___x_2339_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2339_, 0, v_str_2336_);
                    lean_ctor_set(v___x_2339_, 1, v_startInclusive_2337_);
                    lean_ctor_set(v___x_2339_, 2, v___x_2338_);
                    v___x_2340_ = lean_nat_sub(v___x_2338_, v_startInclusive_2337_);
                    lean_dec(v___x_2338_);
                    v___x_2341_ = lean_unsigned_to_nat(1);
                    v___x_2342_ = lean_nat_sub(v___x_2340_, v___x_2341_);
                    lean_dec(v___x_2340_);
                    v___x_2343_ = l_String_Slice_posLE(v___x_2339_, v___x_2342_);
                    lean_dec_ref_known(v___x_2339_, 3);
                    v___x_2344_ = lean_nat_add(v_startInclusive_2337_, v___x_2343_);
                    v___x_2345_ = lean_string_utf8_get_fast(v_str_2336_, v___x_2344_);
                    lean_dec(v___x_2344_);
                    v___x_2346_ = lean_box_uint32(v___x_2345_);
                    lean_inc_ref(v_p_2331_);
                    v___x_2347_ = lean_apply_1(v_p_2331_, v___x_2346_);
                    v___x_2348_ = (lean_unbox(v___x_2347_) as u8);
                    if v___x_2348_ == 0 {
                        lean_dec(v___x_2343_);
                        v___x_2349_ = lean_box(0);
                        v___x_2350_ = lean_nat_sub(v_a_2332_, v___x_2341_);
                        lean_dec(v_a_2332_);
                        v___x_2351_ = l_String_Slice_posLE(v_s_2330_, v___x_2350_);
                        v_a_2332_ = v___x_2351_;
                        v_b_2333_ = v___x_2349_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_2332_);
                        lean_dec_ref(v_p_2331_);
                        v___x_2353_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2353_, 0, v___x_2343_);
                        return v___x_2353_;
                    }
                } else {
                    lean_dec(v_a_2332_);
                    lean_dec_ref(v_p_2331_);
                    lean_inc(v_b_2333_);
                    return v_b_2333_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2354_: *mut LeanObject,
    mut v_p_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
    mut v_b_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2354_, v_p_2355_, v_a_2356_, v_b_2357_);
    lean_dec(v_b_2357_);
    lean_dec_ref(v_s_2354_);
    return v_res_2358_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
    mut v_p_2359_: *mut LeanObject,
    mut v_s_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_2361_ = lean_ctor_get(v_s_2360_, 1);
    v_endExclusive_2362_ = lean_ctor_get(v_s_2360_, 2);
    v_searcher_2363_ = lean_nat_sub(v_endExclusive_2362_, v_startInclusive_2361_);
    v___x_2364_ = lean_box(0);
    v___x_2365_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2360_, v_p_2359_, v_searcher_2363_, v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0___boxed(
    mut v_p_2366_: *mut LeanObject,
    mut v_s_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2368_: *mut LeanObject = core::ptr::null_mut();
    v_res_2368_ =
        l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(v_p_2366_, v_s_2367_);
    lean_dec_ref(v_s_2367_);
    return v_res_2368_;
}
pub unsafe fn l_String_revFindAux(
    mut v_s_2369_: *mut LeanObject,
    mut v_p_2370_: *mut LeanObject,
    mut v_pos_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2372_ = lean_unsigned_to_nat(0);
                v___x_2373_ = lean_string_utf8_byte_size(v_s_2369_);
                lean_inc_ref(v_s_2369_);
                v___x_2374_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2374_, 0, v_s_2369_);
                lean_ctor_set(v___x_2374_, 1, v___x_2372_);
                lean_ctor_set(v___x_2374_, 2, v___x_2373_);
                v___x_2375_ = l_String_Slice_pos_x3f(v___x_2374_, v_pos_2371_);
                lean_dec_ref_known(v___x_2374_, 3);
                if lean_obj_tag(v___x_2375_) == 0 {
                    lean_dec_ref(v_p_2370_);
                    lean_dec_ref(v_s_2369_);
                    v___x_2376_ = lean_box(0);
                    return v___x_2376_;
                } else {
                    v_val_2377_ = lean_ctor_get(v___x_2375_, 0);
                    v_isSharedCheck_2396_ = (!lean_is_exclusive(v___x_2375_)) as u8;
                    if v_isSharedCheck_2396_ == 0 {
                        v___x_2379_ = v___x_2375_;
                        v_isShared_2380_ = v_isSharedCheck_2396_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2377_);
                        lean_dec(v___x_2375_);
                        v___x_2379_ = lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2396_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2381_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2381_, 0, v_s_2369_);
                lean_ctor_set(v___x_2381_, 1, v___x_2372_);
                lean_ctor_set(v___x_2381_, 2, v_val_2377_);
                v___x_2382_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
                    v_p_2370_,
                    v___x_2381_,
                );
                lean_dec_ref_known(v___x_2381_, 3);
                if lean_obj_tag(v___x_2382_) == 0 {
                    if lean_obj_tag(v___x_2382_) == 0 {
                        lean_del_object(v___x_2379_);
                        v___x_2383_ = lean_box(0);
                        return v___x_2383_;
                    } else {
                        v_val_2384_ = lean_ctor_get(v___x_2382_, 0);
                        lean_inc(v_val_2384_);
                        lean_dec_ref_known(v___x_2382_, 1);
                        if v_isShared_2380_ == 0 {
                            lean_ctor_set(v___x_2379_, 0, v_val_2384_);
                            v___x_2386_ = v___x_2379_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_val_2384_);
                            v___x_2386_ = v_reuseFailAlloc_2387_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2379_);
                    v_val_2388_ = lean_ctor_get(v___x_2382_, 0);
                    v_isSharedCheck_2395_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v___x_2390_ = v___x_2382_;
                        v_isShared_2391_ = v_isSharedCheck_2395_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2388_);
                        lean_dec(v___x_2382_);
                        v___x_2390_ = lean_box(0);
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
                    v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_val_2388_);
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
    mut v_s_2397_: *mut LeanObject,
    mut v_p_2398_: *mut LeanObject,
    mut v_inst_2399_: *mut LeanObject,
    mut v_R_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_b_2402_: *mut LeanObject,
    mut v_c_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_2404_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___redArg(v_s_2397_, v_p_2398_, v_a_2401_, v_b_2402_);
    return v___x_2404_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0___boxed(
    mut v_s_2405_: *mut LeanObject,
    mut v_p_2406_: *mut LeanObject,
    mut v_inst_2407_: *mut LeanObject,
    mut v_R_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
    mut v_b_2410_: *mut LeanObject,
    mut v_c_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2412_: *mut LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_revFindAux_spec__0_spec__0(v_s_2405_, v_p_2406_, v_inst_2407_, v_R_2408_, v_a_2409_, v_b_2410_, v_c_2411_);
    lean_dec(v_b_2410_);
    lean_dec_ref(v_s_2405_);
    return v_res_2412_;
}
pub unsafe fn l_String_revFind(
    mut v_s_2413_: *mut LeanObject,
    mut v_p_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2415_ = lean_unsigned_to_nat(0);
                v___x_2416_ = lean_string_utf8_byte_size(v_s_2413_);
                v___x_2417_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2417_, 0, v_s_2413_);
                lean_ctor_set(v___x_2417_, 1, v___x_2415_);
                lean_ctor_set(v___x_2417_, 2, v___x_2416_);
                v___x_2418_ = l_String_Slice_revFind_x3f___at___00String_revFindAux_spec__0(
                    v_p_2414_,
                    v___x_2417_,
                );
                lean_dec_ref_known(v___x_2417_, 3);
                if lean_obj_tag(v___x_2418_) == 0 {
                    v___x_2419_ = lean_box(0);
                    return v___x_2419_;
                } else {
                    v_val_2420_ = lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2422_ = v___x_2418_;
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2420_);
                        lean_dec(v___x_2418_);
                        v___x_2422_ = lean_box(0);
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
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_val_2420_);
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
    mut v_s_2428_: *mut LeanObject,
    mut v_a_2429_: *mut LeanObject,
    mut v_b_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v_str_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u32 = 0;
    let mut v___x_2443_: u32 = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2431_ = lean_unsigned_to_nat(0);
                v___x_2432_ = lean_nat_dec_eq(v_a_2429_, v___x_2431_);
                if v___x_2432_ == 0 {
                    v_str_2433_ = lean_ctor_get(v_s_2428_, 0);
                    v_startInclusive_2434_ = lean_ctor_get(v_s_2428_, 1);
                    v___x_2435_ = lean_nat_add(v_startInclusive_2434_, v_a_2429_);
                    lean_inc(v___x_2435_);
                    lean_inc(v_startInclusive_2434_);
                    lean_inc_ref(v_str_2433_);
                    v___x_2436_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2436_, 0, v_str_2433_);
                    lean_ctor_set(v___x_2436_, 1, v_startInclusive_2434_);
                    lean_ctor_set(v___x_2436_, 2, v___x_2435_);
                    v___x_2437_ = lean_nat_sub(v___x_2435_, v_startInclusive_2434_);
                    lean_dec(v___x_2435_);
                    v___x_2438_ = lean_unsigned_to_nat(1);
                    v___x_2439_ = lean_nat_sub(v___x_2437_, v___x_2438_);
                    lean_dec(v___x_2437_);
                    v___x_2440_ = l_String_Slice_posLE(v___x_2436_, v___x_2439_);
                    lean_dec_ref_known(v___x_2436_, 3);
                    v___x_2441_ = lean_nat_add(v_startInclusive_2434_, v___x_2440_);
                    v___x_2442_ = lean_string_utf8_get_fast(v_str_2433_, v___x_2441_);
                    lean_dec(v___x_2441_);
                    v___x_2443_ = 10;
                    v___x_2444_ = lean_uint32_dec_eq(v___x_2442_, v___x_2443_);
                    if v___x_2444_ == 0 {
                        lean_dec(v___x_2440_);
                        v___x_2445_ = lean_box(0);
                        v___x_2446_ = lean_nat_sub(v_a_2429_, v___x_2438_);
                        lean_dec(v_a_2429_);
                        v___x_2447_ = l_String_Slice_posLE(v_s_2428_, v___x_2446_);
                        v_a_2429_ = v___x_2447_;
                        v_b_2430_ = v___x_2445_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_2429_);
                        v___x_2449_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2449_, 0, v___x_2440_);
                        return v___x_2449_;
                    }
                } else {
                    lean_dec(v_a_2429_);
                    lean_inc(v_b_2430_);
                    return v_b_2430_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg___boxed(
    mut v_s_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
    mut v_b_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2453_: *mut LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2450_, v_a_2451_, v_b_2452_);
    lean_dec(v_b_2452_);
    lean_dec_ref(v_s_2450_);
    return v_res_2453_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(
    mut v_s_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_2455_ = lean_ctor_get(v_s_2454_, 1);
    v_endExclusive_2456_ = lean_ctor_get(v_s_2454_, 2);
    v_searcher_2457_ = lean_nat_sub(v_endExclusive_2456_, v_startInclusive_2455_);
    v___x_2458_ = lean_box(0);
    v___x_2459_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2454_, v_searcher_2457_, v___x_2458_);
    return v___x_2459_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0___boxed(
    mut v_s_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v_s_2460_);
    lean_dec_ref(v_s_2460_);
    return v_res_2461_;
}
pub unsafe fn l_String_findLineStart(
    mut v_s_2462_: *mut LeanObject,
    mut v_pos_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2464_ = lean_unsigned_to_nat(0);
    v___x_2465_ = lean_string_utf8_byte_size(v_s_2462_);
    lean_inc_ref(v_s_2462_);
    v___x_2466_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2466_, 0, v_s_2462_);
    lean_ctor_set(v___x_2466_, 1, v___x_2464_);
    lean_ctor_set(v___x_2466_, 2, v___x_2465_);
    v___x_2467_ = l_String_Slice_pos_x3f(v___x_2466_, v_pos_2463_);
    lean_dec_ref_known(v___x_2466_, 3);
    if lean_obj_tag(v___x_2467_) == 0 {
        lean_dec_ref(v_s_2462_);
        return v___x_2464_;
    } else {
        let mut v_val_2468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
        v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
        lean_inc(v_val_2468_);
        lean_dec_ref_known(v___x_2467_, 1);
        v___x_2469_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2469_, 0, v_s_2462_);
        lean_ctor_set(v___x_2469_, 1, v___x_2464_);
        lean_ctor_set(v___x_2469_, 2, v_val_2468_);
        v___x_2470_ = l_String_Slice_revFind_x3f___at___00String_findLineStart_spec__0(v___x_2469_);
        lean_dec_ref_known(v___x_2469_, 3);
        if lean_obj_tag(v___x_2470_) == 0 {
            if lean_obj_tag(v___x_2470_) == 0 {
                return v___x_2464_;
            } else {
                let mut v_val_2471_: *mut LeanObject = core::ptr::null_mut();
                v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
                lean_inc(v_val_2471_);
                lean_dec_ref_known(v___x_2470_, 1);
                return v_val_2471_;
            }
        } else {
            let mut v_val_2472_: *mut LeanObject = core::ptr::null_mut();
            v_val_2472_ = lean_ctor_get(v___x_2470_, 0);
            lean_inc(v_val_2472_);
            lean_dec_ref_known(v___x_2470_, 1);
            return v_val_2472_;
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(
    mut v_s_2473_: *mut LeanObject,
    mut v_inst_2474_: *mut LeanObject,
    mut v_R_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
    mut v_b_2477_: *mut LeanObject,
    mut v_c_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___redArg(v_s_2473_, v_a_2476_, v_b_2477_);
    return v___x_2479_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0___boxed(
    mut v_s_2480_: *mut LeanObject,
    mut v_inst_2481_: *mut LeanObject,
    mut v_R_2482_: *mut LeanObject,
    mut v_a_2483_: *mut LeanObject,
    mut v_b_2484_: *mut LeanObject,
    mut v_c_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2486_: *mut LeanObject = core::ptr::null_mut();
    v_res_2486_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00String_findLineStart_spec__0_spec__0(v_s_2480_, v_inst_2481_, v_R_2482_, v_a_2483_, v_b_2484_, v_c_2485_);
    lean_dec(v_b_2484_);
    lean_dec_ref(v_s_2480_);
    return v_res_2486_;
}
pub unsafe fn l_String_split___redArg(
    mut v_s_2487_: *mut LeanObject,
    mut v_inst_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = lean_unsigned_to_nat(0);
    v___x_2490_ = lean_string_utf8_byte_size(v_s_2487_);
    v___x_2491_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2491_, 0, v_s_2487_);
    lean_ctor_set(v___x_2491_, 1, v___x_2489_);
    lean_ctor_set(v___x_2491_, 2, v___x_2490_);
    v___x_2492_ = l_String_Slice_splitToSubslice___redArg(v___x_2491_, v_inst_2488_);
    return v___x_2492_;
}
pub unsafe fn l_String_split(
    mut v_00_u03c1_2493_: *mut LeanObject,
    mut v_00_u03c3_2494_: *mut LeanObject,
    mut v_inst_2495_: *mut LeanObject,
    mut v_s_2496_: *mut LeanObject,
    mut v_pat_2497_: *mut LeanObject,
    mut v_inst_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    v___x_2499_ = lean_unsigned_to_nat(0);
    v___x_2500_ = lean_string_utf8_byte_size(v_s_2496_);
    v___x_2501_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2501_, 0, v_s_2496_);
    lean_ctor_set(v___x_2501_, 1, v___x_2499_);
    lean_ctor_set(v___x_2501_, 2, v___x_2500_);
    v___x_2502_ = l_String_Slice_splitToSubslice___redArg(v___x_2501_, v_inst_2498_);
    return v___x_2502_;
}
pub unsafe fn l_String_split___boxed(
    mut v_00_u03c1_2503_: *mut LeanObject,
    mut v_00_u03c3_2504_: *mut LeanObject,
    mut v_inst_2505_: *mut LeanObject,
    mut v_s_2506_: *mut LeanObject,
    mut v_pat_2507_: *mut LeanObject,
    mut v_inst_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_String_split(
        v_00_u03c1_2503_,
        v_00_u03c3_2504_,
        v_inst_2505_,
        v_s_2506_,
        v_pat_2507_,
        v_inst_2508_,
    );
    lean_dec(v_pat_2507_);
    lean_dec(v_inst_2505_);
    return v_res_2509_;
}
pub unsafe fn l_String_splitInclusive___redArg(
    mut v_s_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v___x_2512_ = lean_unsigned_to_nat(0);
    v___x_2513_ = lean_string_utf8_byte_size(v_s_2510_);
    v___x_2514_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2514_, 0, v_s_2510_);
    lean_ctor_set(v___x_2514_, 1, v___x_2512_);
    lean_ctor_set(v___x_2514_, 2, v___x_2513_);
    v___x_2515_ = l_String_Slice_splitInclusive___redArg(v___x_2514_, v_inst_2511_);
    return v___x_2515_;
}
pub unsafe fn l_String_splitInclusive(
    mut v_00_u03c1_2516_: *mut LeanObject,
    mut v_00_u03c3_2517_: *mut LeanObject,
    mut v_s_2518_: *mut LeanObject,
    mut v_pat_2519_: *mut LeanObject,
    mut v_inst_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = lean_unsigned_to_nat(0);
    v___x_2522_ = lean_string_utf8_byte_size(v_s_2518_);
    v___x_2523_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2523_, 0, v_s_2518_);
    lean_ctor_set(v___x_2523_, 1, v___x_2521_);
    lean_ctor_set(v___x_2523_, 2, v___x_2522_);
    v___x_2524_ = l_String_Slice_splitInclusive___redArg(v___x_2523_, v_inst_2520_);
    return v___x_2524_;
}
pub unsafe fn l_String_splitInclusive___boxed(
    mut v_00_u03c1_2525_: *mut LeanObject,
    mut v_00_u03c3_2526_: *mut LeanObject,
    mut v_s_2527_: *mut LeanObject,
    mut v_pat_2528_: *mut LeanObject,
    mut v_inst_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2530_: *mut LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_String_splitInclusive(
        v_00_u03c1_2525_,
        v_00_u03c3_2526_,
        v_s_2527_,
        v_pat_2528_,
        v_inst_2529_,
    );
    lean_dec(v_pat_2528_);
    return v_res_2530_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
    mut v_f_2531_: *mut LeanObject,
    mut v___x_2532_: *mut LeanObject,
    mut v_a_2533_: *mut LeanObject,
    mut v_b_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u32 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2535_ = lean_ctor_get(v___x_2532_, 0);
                v_startInclusive_2536_ = lean_ctor_get(v___x_2532_, 1);
                v_endExclusive_2537_ = lean_ctor_get(v___x_2532_, 2);
                v___x_2538_ = lean_nat_sub(v_endExclusive_2537_, v_startInclusive_2536_);
                v___x_2539_ = lean_nat_dec_eq(v_a_2533_, v___x_2538_);
                lean_dec(v___x_2538_);
                if v___x_2539_ == 0 {
                    v___x_2540_ = lean_nat_add(v_startInclusive_2536_, v_a_2533_);
                    lean_dec(v_a_2533_);
                    v___x_2541_ = lean_string_utf8_next_fast(v_str_2535_, v___x_2540_);
                    v___x_2542_ = lean_nat_sub(v___x_2541_, v_startInclusive_2536_);
                    v___x_2543_ = lean_string_utf8_get_fast(v_str_2535_, v___x_2540_);
                    lean_dec(v___x_2540_);
                    v___x_2544_ = lean_box_uint32(v___x_2543_);
                    lean_inc(v_f_2531_);
                    v___x_2545_ = lean_apply_2(v_f_2531_, v_b_2534_, v___x_2544_);
                    v_a_2533_ = v___x_2542_;
                    v_b_2534_ = v___x_2545_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_2533_);
                    lean_dec(v_f_2531_);
                    return v_b_2534_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg___boxed(
    mut v_f_2547_: *mut LeanObject,
    mut v___x_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v_b_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2551_: *mut LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2547_,
        v___x_2548_,
        v_a_2549_,
        v_b_2550_,
    );
    lean_dec_ref(v___x_2548_);
    return v_res_2551_;
}
pub unsafe fn l_String_foldlAux___redArg(
    mut v_f_2552_: *mut LeanObject,
    mut v_s_2553_: *mut LeanObject,
    mut v_stopPos_2554_: *mut LeanObject,
    mut v_i_2555_: *mut LeanObject,
    mut v_a_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2557_ = lean_unsigned_to_nat(0);
    v___x_2558_ = lean_string_utf8_byte_size(v_s_2553_);
    lean_inc_ref(v_s_2553_);
    v___x_2559_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2559_, 0, v_s_2553_);
    lean_ctor_set(v___x_2559_, 1, v___x_2557_);
    lean_ctor_set(v___x_2559_, 2, v___x_2558_);
    v___x_2560_ = l_String_Slice_pos_x21(v___x_2559_, v_i_2555_);
    v___x_2561_ = l_String_Slice_pos_x21(v___x_2559_, v_stopPos_2554_);
    lean_dec_ref_known(v___x_2559_, 3);
    v___x_2562_ = l_String_slice_x21(v_s_2553_, v___x_2560_, v___x_2561_);
    lean_dec(v___x_2561_);
    lean_dec(v___x_2560_);
    v___x_2563_ = l_String_Slice_positions(v___x_2562_);
    v___x_2564_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2552_,
        v___x_2562_,
        v___x_2563_,
        v_a_2556_,
    );
    lean_dec_ref(v___x_2562_);
    return v___x_2564_;
}
pub unsafe fn l_String_foldlAux___redArg___boxed(
    mut v_f_2565_: *mut LeanObject,
    mut v_s_2566_: *mut LeanObject,
    mut v_stopPos_2567_: *mut LeanObject,
    mut v_i_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2570_: *mut LeanObject = core::ptr::null_mut();
    v_res_2570_ =
        l_String_foldlAux___redArg(v_f_2565_, v_s_2566_, v_stopPos_2567_, v_i_2568_, v_a_2569_);
    lean_dec(v_i_2568_);
    lean_dec(v_stopPos_2567_);
    return v_res_2570_;
}
pub unsafe fn l_String_foldlAux(
    mut v_00_u03b1_2571_: *mut LeanObject,
    mut v_f_2572_: *mut LeanObject,
    mut v_s_2573_: *mut LeanObject,
    mut v_stopPos_2574_: *mut LeanObject,
    mut v_i_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    v___x_2577_ =
        l_String_foldlAux___redArg(v_f_2572_, v_s_2573_, v_stopPos_2574_, v_i_2575_, v_a_2576_);
    return v___x_2577_;
}
pub unsafe fn l_String_foldlAux___boxed(
    mut v_00_u03b1_2578_: *mut LeanObject,
    mut v_f_2579_: *mut LeanObject,
    mut v_s_2580_: *mut LeanObject,
    mut v_stopPos_2581_: *mut LeanObject,
    mut v_i_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2584_: *mut LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_String_foldlAux(
        v_00_u03b1_2578_,
        v_f_2579_,
        v_s_2580_,
        v_stopPos_2581_,
        v_i_2582_,
        v_a_2583_,
    );
    lean_dec(v_i_2582_);
    lean_dec(v_stopPos_2581_);
    return v_res_2584_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0(
    mut v_00_u03b1_2585_: *mut LeanObject,
    mut v_f_2586_: *mut LeanObject,
    mut v___x_2587_: *mut LeanObject,
    mut v_inst_2588_: *mut LeanObject,
    mut v_R_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_b_2591_: *mut LeanObject,
    mut v_c_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___redArg(
        v_f_2586_,
        v___x_2587_,
        v_a_2590_,
        v_b_2591_,
    );
    return v___x_2593_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldlAux_spec__0___boxed(
    mut v_00_u03b1_2594_: *mut LeanObject,
    mut v_f_2595_: *mut LeanObject,
    mut v___x_2596_: *mut LeanObject,
    mut v_inst_2597_: *mut LeanObject,
    mut v_R_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_b_2600_: *mut LeanObject,
    mut v_c_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2602_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___x_2596_);
    return v_res_2602_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
    mut v_f_2603_: *mut LeanObject,
    mut v___x_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_b_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v_str_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prevPos_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u32 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = lean_unsigned_to_nat(0);
                v___x_2608_ = lean_nat_dec_eq(v_a_2605_, v___x_2607_);
                if v___x_2608_ == 0 {
                    v_str_2609_ = lean_ctor_get(v___x_2604_, 0);
                    v_startInclusive_2610_ = lean_ctor_get(v___x_2604_, 1);
                    v___x_2611_ = lean_unsigned_to_nat(1);
                    v___x_2612_ = lean_nat_sub(v_a_2605_, v___x_2611_);
                    lean_dec(v_a_2605_);
                    v_prevPos_2613_ = l_String_Slice_posLE(v___x_2604_, v___x_2612_);
                    v___x_2614_ = lean_nat_add(v_startInclusive_2610_, v_prevPos_2613_);
                    v___x_2615_ = lean_string_utf8_get_fast(v_str_2609_, v___x_2614_);
                    lean_dec(v___x_2614_);
                    v___x_2616_ = lean_box_uint32(v___x_2615_);
                    lean_inc(v_f_2603_);
                    v___x_2617_ = lean_apply_2(v_f_2603_, v___x_2616_, v_b_2606_);
                    v_a_2605_ = v_prevPos_2613_;
                    v_b_2606_ = v___x_2617_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_2605_);
                    lean_dec(v_f_2603_);
                    return v_b_2606_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg___boxed(
    mut v_f_2619_: *mut LeanObject,
    mut v___x_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_b_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2623_: *mut LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2619_,
        v___x_2620_,
        v_a_2621_,
        v_b_2622_,
    );
    lean_dec_ref(v___x_2620_);
    return v_res_2623_;
}
pub unsafe fn l_String_foldrAux___redArg(
    mut v_f_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_s_2626_: *mut LeanObject,
    mut v_i_2627_: *mut LeanObject,
    mut v_begPos_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2629_ = lean_unsigned_to_nat(0);
    v___x_2630_ = lean_string_utf8_byte_size(v_s_2626_);
    lean_inc_ref(v_s_2626_);
    v___x_2631_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2631_, 0, v_s_2626_);
    lean_ctor_set(v___x_2631_, 1, v___x_2629_);
    lean_ctor_set(v___x_2631_, 2, v___x_2630_);
    v___x_2632_ = l_String_Slice_pos_x21(v___x_2631_, v_begPos_2628_);
    v___x_2633_ = l_String_Slice_pos_x21(v___x_2631_, v_i_2627_);
    lean_dec_ref_known(v___x_2631_, 3);
    v___x_2634_ = l_String_slice_x21(v_s_2626_, v___x_2632_, v___x_2633_);
    lean_dec(v___x_2633_);
    lean_dec(v___x_2632_);
    v___x_2635_ = l_String_Slice_revPositions(v___x_2634_);
    v___x_2636_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2624_,
        v___x_2634_,
        v___x_2635_,
        v_a_2625_,
    );
    lean_dec_ref(v___x_2634_);
    return v___x_2636_;
}
pub unsafe fn l_String_foldrAux___redArg___boxed(
    mut v_f_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_s_2639_: *mut LeanObject,
    mut v_i_2640_: *mut LeanObject,
    mut v_begPos_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2642_: *mut LeanObject = core::ptr::null_mut();
    v_res_2642_ =
        l_String_foldrAux___redArg(v_f_2637_, v_a_2638_, v_s_2639_, v_i_2640_, v_begPos_2641_);
    lean_dec(v_begPos_2641_);
    lean_dec(v_i_2640_);
    return v_res_2642_;
}
pub unsafe fn l_String_foldrAux(
    mut v_00_u03b1_2643_: *mut LeanObject,
    mut v_f_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_s_2646_: *mut LeanObject,
    mut v_i_2647_: *mut LeanObject,
    mut v_begPos_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    v___x_2649_ =
        l_String_foldrAux___redArg(v_f_2644_, v_a_2645_, v_s_2646_, v_i_2647_, v_begPos_2648_);
    return v___x_2649_;
}
pub unsafe fn l_String_foldrAux___boxed(
    mut v_00_u03b1_2650_: *mut LeanObject,
    mut v_f_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_s_2653_: *mut LeanObject,
    mut v_i_2654_: *mut LeanObject,
    mut v_begPos_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2656_: *mut LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_String_foldrAux(
        v_00_u03b1_2650_,
        v_f_2651_,
        v_a_2652_,
        v_s_2653_,
        v_i_2654_,
        v_begPos_2655_,
    );
    lean_dec(v_begPos_2655_);
    lean_dec(v_i_2654_);
    return v_res_2656_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0(
    mut v_00_u03b1_2657_: *mut LeanObject,
    mut v_f_2658_: *mut LeanObject,
    mut v___x_2659_: *mut LeanObject,
    mut v_inst_2660_: *mut LeanObject,
    mut v_R_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
    mut v_b_2663_: *mut LeanObject,
    mut v_c_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___redArg(
        v_f_2658_,
        v___x_2659_,
        v_a_2662_,
        v_b_2663_,
    );
    return v___x_2665_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_foldrAux_spec__0___boxed(
    mut v_00_u03b1_2666_: *mut LeanObject,
    mut v_f_2667_: *mut LeanObject,
    mut v___x_2668_: *mut LeanObject,
    mut v_inst_2669_: *mut LeanObject,
    mut v_R_2670_: *mut LeanObject,
    mut v_a_2671_: *mut LeanObject,
    mut v_b_2672_: *mut LeanObject,
    mut v_c_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2674_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___x_2668_);
    return v_res_2674_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(
    mut v_s_2675_: *mut LeanObject,
    mut v_p_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_b_2678_: u8,
) -> u8 {
    let mut v_str_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u32 = 0;
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2679_ = lean_ctor_get(v_s_2675_, 0);
                v_startInclusive_2680_ = lean_ctor_get(v_s_2675_, 1);
                v_endExclusive_2681_ = lean_ctor_get(v_s_2675_, 2);
                v___x_2682_ = lean_nat_sub(v_endExclusive_2681_, v_startInclusive_2680_);
                v___x_2683_ = lean_nat_dec_eq(v_a_2677_, v___x_2682_);
                lean_dec(v___x_2682_);
                if v___x_2683_ == 0 {
                    v___x_2684_ = lean_nat_add(v_startInclusive_2680_, v_a_2677_);
                    lean_dec(v_a_2677_);
                    v___x_2685_ = lean_string_utf8_get_fast(v_str_2679_, v___x_2684_);
                    v___x_2686_ = lean_box_uint32(v___x_2685_);
                    lean_inc_ref(v_p_2676_);
                    v___x_2687_ = lean_apply_1(v_p_2676_, v___x_2686_);
                    v___x_2688_ = (lean_unbox(v___x_2687_) as u8);
                    if v___x_2688_ == 0 {
                        v___x_2689_ = lean_string_utf8_next_fast(v_str_2679_, v___x_2684_);
                        lean_dec(v___x_2684_);
                        v___x_2690_ = lean_nat_sub(v___x_2689_, v_startInclusive_2680_);
                        v___x_2691_ = (lean_unbox(v___x_2687_) as u8);
                        v_a_2677_ = v___x_2690_;
                        v_b_2678_ = v___x_2691_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2684_);
                        lean_dec_ref(v_p_2676_);
                        v___x_2693_ = (lean_unbox(v___x_2687_) as u8);
                        return v___x_2693_;
                    }
                } else {
                    lean_dec(v_a_2677_);
                    lean_dec_ref(v_p_2676_);
                    return v_b_2678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg___boxed(
    mut v_s_2694_: *mut LeanObject,
    mut v_p_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_b_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_2698_: u8 = 0;
    let mut v_res_2699_: u8 = 0;
    let mut v_r_2700_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2698_ = (lean_unbox(v_b_2697_) as u8);
    v_res_2699_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2694_, v_p_2695_, v_a_2696_, v_b_boxed_2698_);
    lean_dec_ref(v_s_2694_);
    v_r_2700_ = lean_box((v_res_2699_) as usize);
    return v_r_2700_;
}
pub unsafe fn l_String_Slice_contains___at___00String_anyAux_spec__0(
    mut v_p_2701_: *mut LeanObject,
    mut v_s_2702_: *mut LeanObject,
) -> u8 {
    let mut v_searcher_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: u8 = 0;
    let mut v___x_2705_: u8 = 0;
    v_searcher_2703_ = lean_unsigned_to_nat(0);
    v___x_2704_ = 0;
    v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2702_, v_p_2701_, v_searcher_2703_, v___x_2704_);
    return v___x_2705_;
}
pub unsafe fn l_String_Slice_contains___at___00String_anyAux_spec__0___boxed(
    mut v_p_2706_: *mut LeanObject,
    mut v_s_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: u8 = 0;
    let mut v_r_2709_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2706_, v_s_2707_);
    lean_dec_ref(v_s_2707_);
    v_r_2709_ = lean_box((v_res_2708_) as usize);
    return v_r_2709_;
}
pub unsafe fn l_String_anyAux(
    mut v_s_2710_: *mut LeanObject,
    mut v_stopPos_2711_: *mut LeanObject,
    mut v_p_2712_: *mut LeanObject,
    mut v_i_2713_: *mut LeanObject,
) -> u8 {
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    v___x_2714_ = lean_unsigned_to_nat(0);
    v___x_2715_ = lean_string_utf8_byte_size(v_s_2710_);
    lean_inc_ref(v_s_2710_);
    v___x_2716_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2716_, 0, v_s_2710_);
    lean_ctor_set(v___x_2716_, 1, v___x_2714_);
    lean_ctor_set(v___x_2716_, 2, v___x_2715_);
    v___x_2717_ = l_String_Slice_pos_x21(v___x_2716_, v_i_2713_);
    v___x_2718_ = l_String_Slice_pos_x21(v___x_2716_, v_stopPos_2711_);
    lean_dec_ref_known(v___x_2716_, 3);
    v___x_2719_ = l_String_slice_x21(v_s_2710_, v___x_2717_, v___x_2718_);
    lean_dec(v___x_2718_);
    lean_dec(v___x_2717_);
    v___x_2720_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2712_, v___x_2719_);
    lean_dec_ref(v___x_2719_);
    return v___x_2720_;
}
pub unsafe fn l_String_anyAux___boxed(
    mut v_s_2721_: *mut LeanObject,
    mut v_stopPos_2722_: *mut LeanObject,
    mut v_p_2723_: *mut LeanObject,
    mut v_i_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2725_: u8 = 0;
    let mut v_r_2726_: *mut LeanObject = core::ptr::null_mut();
    v_res_2725_ = l_String_anyAux(v_s_2721_, v_stopPos_2722_, v_p_2723_, v_i_2724_);
    lean_dec(v_i_2724_);
    lean_dec(v_stopPos_2722_);
    v_r_2726_ = lean_box((v_res_2725_) as usize);
    return v_r_2726_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(
    mut v_s_2727_: *mut LeanObject,
    mut v_p_2728_: *mut LeanObject,
    mut v_inst_2729_: *mut LeanObject,
    mut v_R_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_b_2732_: u8,
    mut v_c_2733_: *mut LeanObject,
) -> u8 {
    let mut v___x_2734_: u8 = 0;
    v___x_2734_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___redArg(v_s_2727_, v_p_2728_, v_a_2731_, v_b_2732_);
    return v___x_2734_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0___boxed(
    mut v_s_2735_: *mut LeanObject,
    mut v_p_2736_: *mut LeanObject,
    mut v_inst_2737_: *mut LeanObject,
    mut v_R_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
    mut v_b_2740_: *mut LeanObject,
    mut v_c_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_2742_: u8 = 0;
    let mut v_res_2743_: u8 = 0;
    let mut v_r_2744_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2742_ = (lean_unbox(v_b_2740_) as u8);
    v_res_2743_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_anyAux_spec__0_spec__0(v_s_2735_, v_p_2736_, v_inst_2737_, v_R_2738_, v_a_2739_, v_b_boxed_2742_, v_c_2741_);
    lean_dec_ref(v_s_2735_);
    v_r_2744_ = lean_box((v_res_2743_) as usize);
    return v_r_2744_;
}
pub unsafe fn l_String_contains___redArg(
    mut v_inst_2745_: *mut LeanObject,
    mut v_s_2746_: *mut LeanObject,
    mut v_inst_2747_: *mut LeanObject,
) -> u8 {
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    v___x_2748_ = lean_unsigned_to_nat(0);
    v___x_2749_ = lean_string_utf8_byte_size(v_s_2746_);
    v___x_2750_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2750_, 0, v_s_2746_);
    lean_ctor_set(v___x_2750_, 1, v___x_2748_);
    lean_ctor_set(v___x_2750_, 2, v___x_2749_);
    v___x_2751_ = l_String_Slice_contains___redArg(v_inst_2745_, v___x_2750_, v_inst_2747_);
    return v___x_2751_;
}
pub unsafe fn l_String_contains___redArg___boxed(
    mut v_inst_2752_: *mut LeanObject,
    mut v_s_2753_: *mut LeanObject,
    mut v_inst_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2755_: u8 = 0;
    let mut v_r_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2755_ = l_String_contains___redArg(v_inst_2752_, v_s_2753_, v_inst_2754_);
    v_r_2756_ = lean_box((v_res_2755_) as usize);
    return v_r_2756_;
}
pub unsafe fn l_String_contains(
    mut v_00_u03c1_2757_: *mut LeanObject,
    mut v_00_u03c3_2758_: *mut LeanObject,
    mut v_inst_2759_: *mut LeanObject,
    mut v_inst_2760_: *mut LeanObject,
    mut v_s_2761_: *mut LeanObject,
    mut v_pat_2762_: *mut LeanObject,
    mut v_inst_2763_: *mut LeanObject,
) -> u8 {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    v___x_2764_ = lean_unsigned_to_nat(0);
    v___x_2765_ = lean_string_utf8_byte_size(v_s_2761_);
    v___x_2766_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2766_, 0, v_s_2761_);
    lean_ctor_set(v___x_2766_, 1, v___x_2764_);
    lean_ctor_set(v___x_2766_, 2, v___x_2765_);
    v___x_2767_ = l_String_Slice_contains___redArg(v_inst_2760_, v___x_2766_, v_inst_2763_);
    return v___x_2767_;
}
pub unsafe fn l_String_contains___boxed(
    mut v_00_u03c1_2768_: *mut LeanObject,
    mut v_00_u03c3_2769_: *mut LeanObject,
    mut v_inst_2770_: *mut LeanObject,
    mut v_inst_2771_: *mut LeanObject,
    mut v_s_2772_: *mut LeanObject,
    mut v_pat_2773_: *mut LeanObject,
    mut v_inst_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2775_: u8 = 0;
    let mut v_r_2776_: *mut LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_String_contains(
        v_00_u03c1_2768_,
        v_00_u03c3_2769_,
        v_inst_2770_,
        v_inst_2771_,
        v_s_2772_,
        v_pat_2773_,
        v_inst_2774_,
    );
    lean_dec(v_pat_2773_);
    lean_dec(v_inst_2770_);
    v_r_2776_ = lean_box((v_res_2775_) as usize);
    return v_r_2776_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(
    mut v_s_2777_: *mut LeanObject,
    mut v_c_2778_: u32,
    mut v_a_2779_: *mut LeanObject,
    mut v_b_2780_: u8,
) -> u8 {
    let mut v_str_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u32 = 0;
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2781_ = lean_ctor_get(v_s_2777_, 0);
                v_startInclusive_2782_ = lean_ctor_get(v_s_2777_, 1);
                v_endExclusive_2783_ = lean_ctor_get(v_s_2777_, 2);
                v___x_2784_ = lean_nat_sub(v_endExclusive_2783_, v_startInclusive_2782_);
                v___x_2785_ = lean_nat_dec_eq(v_a_2779_, v___x_2784_);
                lean_dec(v___x_2784_);
                if v___x_2785_ == 0 {
                    v___x_2786_ = lean_nat_add(v_startInclusive_2782_, v_a_2779_);
                    lean_dec(v_a_2779_);
                    v___x_2787_ = lean_string_utf8_get_fast(v_str_2781_, v___x_2786_);
                    v___x_2788_ = lean_uint32_dec_eq(v___x_2787_, v_c_2778_);
                    if v___x_2788_ == 0 {
                        v___x_2789_ = lean_string_utf8_next_fast(v_str_2781_, v___x_2786_);
                        lean_dec(v___x_2786_);
                        v___x_2790_ = lean_nat_sub(v___x_2789_, v_startInclusive_2782_);
                        v_a_2779_ = v___x_2790_;
                        v_b_2780_ = v___x_2788_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2786_);
                        return v___x_2788_;
                    }
                } else {
                    lean_dec(v_a_2779_);
                    return v_b_2780_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg___boxed(
    mut v_s_2792_: *mut LeanObject,
    mut v_c_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
    mut v_b_2795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2796_: u32 = 0;
    let mut v_b_boxed_2797_: u8 = 0;
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2796_ = lean_unbox_uint32(v_c_2793_);
    lean_dec(v_c_2793_);
    v_b_boxed_2797_ = (lean_unbox(v_b_2795_) as u8);
    v_res_2798_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2792_, v_c_boxed_2796_, v_a_2794_, v_b_boxed_2797_);
    lean_dec_ref(v_s_2792_);
    v_r_2799_ = lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
    mut v_c_2800_: u32,
    mut v_s_2801_: *mut LeanObject,
) -> u8 {
    let mut v_searcher_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u8 = 0;
    let mut v___x_2804_: u8 = 0;
    v_searcher_2802_ = lean_unsigned_to_nat(0);
    v___x_2803_ = 0;
    v___x_2804_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2801_, v_c_2800_, v_searcher_2802_, v___x_2803_);
    return v___x_2804_;
}
pub unsafe fn l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0___boxed(
    mut v_c_2805_: *mut LeanObject,
    mut v_s_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2807_: u32 = 0;
    let mut v_res_2808_: u8 = 0;
    let mut v_r_2809_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2807_ = lean_unbox_uint32(v_c_2805_);
    lean_dec(v_c_2805_);
    v_res_2808_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
        v_c_boxed_2807_,
        v_s_2806_,
    );
    lean_dec_ref(v_s_2806_);
    v_r_2809_ = lean_box((v_res_2808_) as usize);
    return v_r_2809_;
}
pub unsafe fn lean_string_contains(mut v_s_2810_: *mut LeanObject, mut v_c_2811_: u32) -> u8 {
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    v___x_2812_ = lean_unsigned_to_nat(0);
    v___x_2813_ = lean_string_utf8_byte_size(v_s_2810_);
    v___x_2814_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2814_, 0, v_s_2810_);
    lean_ctor_set(v___x_2814_, 1, v___x_2812_);
    lean_ctor_set(v___x_2814_, 2, v___x_2813_);
    v___x_2815_ = l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
        v_c_2811_,
        v___x_2814_,
    );
    lean_dec_ref_known(v___x_2814_, 3);
    return v___x_2815_;
}
pub unsafe fn l_String_Internal_containsImpl___boxed(
    mut v_s_2816_: *mut LeanObject,
    mut v_c_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2818_: u32 = 0;
    let mut v_res_2819_: u8 = 0;
    let mut v_r_2820_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2818_ = lean_unbox_uint32(v_c_2817_);
    lean_dec(v_c_2817_);
    v_res_2819_ = lean_string_contains(v_s_2816_, v_c_boxed_2818_);
    v_r_2820_ = lean_box((v_res_2819_) as usize);
    return v_r_2820_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(
    mut v_s_2821_: *mut LeanObject,
    mut v_c_2822_: u32,
    mut v_inst_2823_: *mut LeanObject,
    mut v_R_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_b_2826_: u8,
    mut v_c_2827_: *mut LeanObject,
) -> u8 {
    let mut v___x_2828_: u8 = 0;
    v___x_2828_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___redArg(v_s_2821_, v_c_2822_, v_a_2825_, v_b_2826_);
    return v___x_2828_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0___boxed(
    mut v_s_2829_: *mut LeanObject,
    mut v_c_2830_: *mut LeanObject,
    mut v_inst_2831_: *mut LeanObject,
    mut v_R_2832_: *mut LeanObject,
    mut v_a_2833_: *mut LeanObject,
    mut v_b_2834_: *mut LeanObject,
    mut v_c_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2836_: u32 = 0;
    let mut v_b_boxed_2837_: u8 = 0;
    let mut v_res_2838_: u8 = 0;
    let mut v_r_2839_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2836_ = lean_unbox_uint32(v_c_2830_);
    lean_dec(v_c_2830_);
    v_b_boxed_2837_ = (lean_unbox(v_b_2834_) as u8);
    v_res_2838_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00String_Internal_containsImpl_spec__0_spec__0(v_s_2829_, v_c_boxed_2836_, v_inst_2831_, v_R_2832_, v_a_2833_, v_b_boxed_2837_, v_c_2835_);
    lean_dec_ref(v_s_2829_);
    v_r_2839_ = lean_box((v_res_2838_) as usize);
    return v_r_2839_;
}
pub unsafe fn l_String_any___redArg(
    mut v_inst_2840_: *mut LeanObject,
    mut v_s_2841_: *mut LeanObject,
    mut v_inst_2842_: *mut LeanObject,
) -> u8 {
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    v___x_2843_ = lean_unsigned_to_nat(0);
    v___x_2844_ = lean_string_utf8_byte_size(v_s_2841_);
    v___x_2845_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2845_, 0, v_s_2841_);
    lean_ctor_set(v___x_2845_, 1, v___x_2843_);
    lean_ctor_set(v___x_2845_, 2, v___x_2844_);
    v___x_2846_ = l_String_Slice_contains___redArg(v_inst_2840_, v___x_2845_, v_inst_2842_);
    return v___x_2846_;
}
pub unsafe fn l_String_any___redArg___boxed(
    mut v_inst_2847_: *mut LeanObject,
    mut v_s_2848_: *mut LeanObject,
    mut v_inst_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2850_: u8 = 0;
    let mut v_r_2851_: *mut LeanObject = core::ptr::null_mut();
    v_res_2850_ = l_String_any___redArg(v_inst_2847_, v_s_2848_, v_inst_2849_);
    v_r_2851_ = lean_box((v_res_2850_) as usize);
    return v_r_2851_;
}
pub unsafe fn l_String_any(
    mut v_00_u03c1_2852_: *mut LeanObject,
    mut v_00_u03c3_2853_: *mut LeanObject,
    mut v_inst_2854_: *mut LeanObject,
    mut v_inst_2855_: *mut LeanObject,
    mut v_s_2856_: *mut LeanObject,
    mut v_pat_2857_: *mut LeanObject,
    mut v_inst_2858_: *mut LeanObject,
) -> u8 {
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    v___x_2859_ = lean_unsigned_to_nat(0);
    v___x_2860_ = lean_string_utf8_byte_size(v_s_2856_);
    v___x_2861_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2861_, 0, v_s_2856_);
    lean_ctor_set(v___x_2861_, 1, v___x_2859_);
    lean_ctor_set(v___x_2861_, 2, v___x_2860_);
    v___x_2862_ = l_String_Slice_contains___redArg(v_inst_2855_, v___x_2861_, v_inst_2858_);
    return v___x_2862_;
}
pub unsafe fn l_String_any___boxed(
    mut v_00_u03c1_2863_: *mut LeanObject,
    mut v_00_u03c3_2864_: *mut LeanObject,
    mut v_inst_2865_: *mut LeanObject,
    mut v_inst_2866_: *mut LeanObject,
    mut v_s_2867_: *mut LeanObject,
    mut v_pat_2868_: *mut LeanObject,
    mut v_inst_2869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2870_: u8 = 0;
    let mut v_r_2871_: *mut LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_String_any(
        v_00_u03c1_2863_,
        v_00_u03c3_2864_,
        v_inst_2865_,
        v_inst_2866_,
        v_s_2867_,
        v_pat_2868_,
        v_inst_2869_,
    );
    lean_dec(v_pat_2868_);
    lean_dec(v_inst_2865_);
    v_r_2871_ = lean_box((v_res_2870_) as usize);
    return v_r_2871_;
}
pub unsafe fn lean_string_any(
    mut v_s_2872_: *mut LeanObject,
    mut v_p_2873_: *mut LeanObject,
) -> u8 {
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    v___x_2874_ = lean_unsigned_to_nat(0);
    v___x_2875_ = lean_string_utf8_byte_size(v_s_2872_);
    v___x_2876_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2876_, 0, v_s_2872_);
    lean_ctor_set(v___x_2876_, 1, v___x_2874_);
    lean_ctor_set(v___x_2876_, 2, v___x_2875_);
    v___x_2877_ = l_String_Slice_contains___at___00String_anyAux_spec__0(v_p_2873_, v___x_2876_);
    lean_dec_ref_known(v___x_2876_, 3);
    return v___x_2877_;
}
pub unsafe fn l_String_Internal_anyImpl___boxed(
    mut v_s_2878_: *mut LeanObject,
    mut v_p_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2880_: u8 = 0;
    let mut v_r_2881_: *mut LeanObject = core::ptr::null_mut();
    v_res_2880_ = lean_string_any(v_s_2878_, v_p_2879_);
    v_r_2881_ = lean_box((v_res_2880_) as usize);
    return v_r_2881_;
}
pub unsafe fn l_String_isNat(mut v_s_2882_: *mut LeanObject) -> u8 {
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    v___x_2883_ = lean_unsigned_to_nat(0);
    v___x_2884_ = lean_string_utf8_byte_size(v_s_2882_);
    v___x_2885_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2885_, 0, v_s_2882_);
    lean_ctor_set(v___x_2885_, 1, v___x_2883_);
    lean_ctor_set(v___x_2885_, 2, v___x_2884_);
    v___x_2886_ = l_String_Slice_isNat(v___x_2885_);
    lean_dec_ref_known(v___x_2885_, 3);
    return v___x_2886_;
}
pub unsafe fn l_String_isNat___boxed(mut v_s_2887_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2888_: u8 = 0;
    let mut v_r_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_String_isNat(v_s_2887_);
    v_r_2889_ = lean_box((v_res_2888_) as usize);
    return v_r_2889_;
}
pub unsafe fn l_String_toNat_x3f(mut v_s_2890_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = lean_unsigned_to_nat(0);
    v___x_2892_ = lean_string_utf8_byte_size(v_s_2890_);
    v___x_2893_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2893_, 0, v_s_2890_);
    lean_ctor_set(v___x_2893_, 1, v___x_2891_);
    lean_ctor_set(v___x_2893_, 2, v___x_2892_);
    v___x_2894_ = l_String_Slice_toNat_x3f(v___x_2893_);
    lean_dec_ref_known(v___x_2893_, 3);
    return v___x_2894_;
}
pub unsafe fn l_String_toNat_x21(mut v_s_2895_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    v___x_2896_ = lean_unsigned_to_nat(0);
    v___x_2897_ = lean_string_utf8_byte_size(v_s_2895_);
    v___x_2898_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2898_, 0, v_s_2895_);
    lean_ctor_set(v___x_2898_, 1, v___x_2896_);
    lean_ctor_set(v___x_2898_, 2, v___x_2897_);
    v___x_2899_ = l_String_Slice_toNat_x21(v___x_2898_);
    lean_dec_ref_known(v___x_2898_, 3);
    return v___x_2899_;
}
pub unsafe fn l_String_toInt_x3f(mut v_s_2900_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    v___x_2901_ = lean_unsigned_to_nat(0);
    v___x_2902_ = lean_string_utf8_byte_size(v_s_2900_);
    v___x_2903_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2903_, 0, v_s_2900_);
    lean_ctor_set(v___x_2903_, 1, v___x_2901_);
    lean_ctor_set(v___x_2903_, 2, v___x_2902_);
    v___x_2904_ = l_String_Slice_toInt_x3f(v___x_2903_);
    return v___x_2904_;
}
pub unsafe fn l_String_isInt(mut v_s_2905_: *mut LeanObject) -> u8 {
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: u8 = 0;
    v___x_2906_ = lean_unsigned_to_nat(0);
    v___x_2907_ = lean_string_utf8_byte_size(v_s_2905_);
    v___x_2908_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2908_, 0, v_s_2905_);
    lean_ctor_set(v___x_2908_, 1, v___x_2906_);
    lean_ctor_set(v___x_2908_, 2, v___x_2907_);
    v___x_2909_ = l_String_Slice_isInt(v___x_2908_);
    return v___x_2909_;
}
pub unsafe fn l_String_isInt___boxed(mut v_s_2910_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2911_: u8 = 0;
    let mut v_r_2912_: *mut LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_String_isInt(v_s_2910_);
    v_r_2912_ = lean_box((v_res_2911_) as usize);
    return v_r_2912_;
}
pub unsafe fn l_String_toInt_x21(mut v_s_2914_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    v___x_2915_ = lean_unsigned_to_nat(0);
    v___x_2916_ = lean_string_utf8_byte_size(v_s_2914_);
    v___x_2917_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2917_, 0, v_s_2914_);
    lean_ctor_set(v___x_2917_, 1, v___x_2915_);
    lean_ctor_set(v___x_2917_, 2, v___x_2916_);
    v___x_2918_ = l_String_Slice_toInt_x3f(v___x_2917_);
    if lean_obj_tag(v___x_2918_) == 0 {
        let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
        v___x_2919_ = l_Int_instInhabited;
        v___x_2920_ = l_String_toInt_x21___closed__0;
        v___x_2921_ = l_panic___redArg(v___x_2919_, v___x_2920_);
        return v___x_2921_;
    } else {
        let mut v_val_2922_: *mut LeanObject = core::ptr::null_mut();
        v_val_2922_ = lean_ctor_get(v___x_2918_, 0);
        lean_inc(v_val_2922_);
        lean_dec_ref_known(v___x_2918_, 1);
        return v_val_2922_;
    }
}
pub unsafe fn l_String_front_x3f(mut v_s_2923_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = lean_unsigned_to_nat(0);
    v___x_2925_ = lean_string_utf8_byte_size(v_s_2923_);
    v___x_2926_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2926_, 0, v_s_2923_);
    lean_ctor_set(v___x_2926_, 1, v___x_2924_);
    lean_ctor_set(v___x_2926_, 2, v___x_2925_);
    v___x_2927_ = l_String_Slice_Pos_get_x3f(v___x_2926_, v___x_2924_);
    lean_dec_ref_known(v___x_2926_, 3);
    return v___x_2927_;
}
pub unsafe fn l_String_front(mut v_s_2928_: *mut LeanObject) -> u32 {
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    v___x_2929_ = lean_unsigned_to_nat(0);
    v___x_2930_ = lean_string_utf8_byte_size(v_s_2928_);
    v___x_2931_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2931_, 0, v_s_2928_);
    lean_ctor_set(v___x_2931_, 1, v___x_2929_);
    lean_ctor_set(v___x_2931_, 2, v___x_2930_);
    v___x_2932_ = l_String_Slice_Pos_get_x3f(v___x_2931_, v___x_2929_);
    lean_dec_ref_known(v___x_2931_, 3);
    if lean_obj_tag(v___x_2932_) == 0 {
        let mut v___x_2933_: u32 = 0;
        v___x_2933_ = 65;
        return v___x_2933_;
    } else {
        let mut v_val_2934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2935_: u32 = 0;
        v_val_2934_ = lean_ctor_get(v___x_2932_, 0);
        lean_inc(v_val_2934_);
        lean_dec_ref_known(v___x_2932_, 1);
        v___x_2935_ = lean_unbox_uint32(v_val_2934_);
        lean_dec(v_val_2934_);
        return v___x_2935_;
    }
}
pub unsafe fn l_String_front___boxed(mut v_s_2936_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2937_: u32 = 0;
    let mut v_r_2938_: *mut LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_String_front(v_s_2936_);
    v_r_2938_ = lean_box_uint32(v_res_2937_);
    return v_r_2938_;
}
pub unsafe fn lean_string_front(mut v_s_2939_: *mut LeanObject) -> u32 {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = lean_unsigned_to_nat(0);
    v___x_2941_ = lean_string_utf8_byte_size(v_s_2939_);
    v___x_2942_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2942_, 0, v_s_2939_);
    lean_ctor_set(v___x_2942_, 1, v___x_2940_);
    lean_ctor_set(v___x_2942_, 2, v___x_2941_);
    v___x_2943_ = l_String_Slice_Pos_get_x3f(v___x_2942_, v___x_2940_);
    lean_dec_ref_known(v___x_2942_, 3);
    if lean_obj_tag(v___x_2943_) == 0 {
        let mut v___x_2944_: u32 = 0;
        v___x_2944_ = 65;
        return v___x_2944_;
    } else {
        let mut v_val_2945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: u32 = 0;
        v_val_2945_ = lean_ctor_get(v___x_2943_, 0);
        lean_inc(v_val_2945_);
        lean_dec_ref_known(v___x_2943_, 1);
        v___x_2946_ = lean_unbox_uint32(v_val_2945_);
        lean_dec(v_val_2945_);
        return v___x_2946_;
    }
}
pub unsafe fn l_String_Internal_frontImpl___boxed(
    mut v_s_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2948_: u32 = 0;
    let mut v_r_2949_: *mut LeanObject = core::ptr::null_mut();
    v_res_2948_ = lean_string_front(v_s_2947_);
    v_r_2949_ = lean_box_uint32(v_res_2948_);
    return v_r_2949_;
}
pub unsafe fn l_String_back_x3f(mut v_s_2950_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    v___x_2951_ = lean_unsigned_to_nat(0);
    v___x_2952_ = lean_string_utf8_byte_size(v_s_2950_);
    v___x_2953_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2953_, 0, v_s_2950_);
    lean_ctor_set(v___x_2953_, 1, v___x_2951_);
    lean_ctor_set(v___x_2953_, 2, v___x_2952_);
    v___x_2954_ = l_String_Slice_Pos_prev_x3f(v___x_2953_, v___x_2952_);
    if lean_obj_tag(v___x_2954_) == 0 {
        let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2953_, 3);
        v___x_2955_ = lean_box(0);
        return v___x_2955_;
    } else {
        let mut v_val_2956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
        v_val_2956_ = lean_ctor_get(v___x_2954_, 0);
        lean_inc(v_val_2956_);
        lean_dec_ref_known(v___x_2954_, 1);
        v___x_2957_ = l_String_Slice_Pos_get_x3f(v___x_2953_, v_val_2956_);
        lean_dec(v_val_2956_);
        lean_dec_ref_known(v___x_2953_, 3);
        return v___x_2957_;
    }
}
pub unsafe fn l_String_back(mut v_s_2958_: *mut LeanObject) -> u32 {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = lean_unsigned_to_nat(0);
    v___x_2960_ = lean_string_utf8_byte_size(v_s_2958_);
    v___x_2961_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2961_, 0, v_s_2958_);
    lean_ctor_set(v___x_2961_, 1, v___x_2959_);
    lean_ctor_set(v___x_2961_, 2, v___x_2960_);
    v___x_2962_ = l_String_Slice_Pos_prev_x3f(v___x_2961_, v___x_2960_);
    if lean_obj_tag(v___x_2962_) == 0 {
        let mut v___x_2963_: u32 = 0;
        lean_dec_ref_known(v___x_2961_, 3);
        v___x_2963_ = 65;
        return v___x_2963_;
    } else {
        let mut v_val_2964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
        v_val_2964_ = lean_ctor_get(v___x_2962_, 0);
        lean_inc(v_val_2964_);
        lean_dec_ref_known(v___x_2962_, 1);
        v___x_2965_ = l_String_Slice_Pos_get_x3f(v___x_2961_, v_val_2964_);
        lean_dec(v_val_2964_);
        lean_dec_ref_known(v___x_2961_, 3);
        if lean_obj_tag(v___x_2965_) == 0 {
            let mut v___x_2966_: u32 = 0;
            v___x_2966_ = 65;
            return v___x_2966_;
        } else {
            let mut v_val_2967_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2968_: u32 = 0;
            v_val_2967_ = lean_ctor_get(v___x_2965_, 0);
            lean_inc(v_val_2967_);
            lean_dec_ref_known(v___x_2965_, 1);
            v___x_2968_ = lean_unbox_uint32(v_val_2967_);
            lean_dec(v_val_2967_);
            return v___x_2968_;
        }
    }
}
pub unsafe fn l_String_back___boxed(mut v_s_2969_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2970_: u32 = 0;
    let mut v_r_2971_: *mut LeanObject = core::ptr::null_mut();
    v_res_2970_ = l_String_back(v_s_2969_);
    v_r_2971_ = lean_box_uint32(v_res_2970_);
    return v_r_2971_;
}
pub unsafe fn l_String_lines(mut v_s_2972_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = lean_unsigned_to_nat(0);
    v___x_2974_ = lean_string_utf8_byte_size(v_s_2972_);
    v___x_2975_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2975_, 0, v_s_2972_);
    lean_ctor_set(v___x_2975_, 1, v___x_2973_);
    lean_ctor_set(v___x_2975_, 2, v___x_2974_);
    v___x_2976_ = l_String_Slice_lines(v___x_2975_);
    lean_dec_ref_known(v___x_2975_, 3);
    return v___x_2976_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Search(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Search(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Search(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Search(builtin);
}
