// Lean compiler output
// Module: Std.Time.Zoned
// Imports: Std.Time.Zoned.DateTime Std.Time.Zoned.ZoneRules Std.Time.Zoned.ZonedDateTime Std.Time.Zoned.Database
use crate::ffi::{
    lean_get_current_time, lean_int_add, lean_int_mul, lean_int_neg, lean_mk_thunk,
    lean_nat_to_int, lean_thunk_get_own,
};
use crate::r#gen::Std::Time::DateTime::PlainDateTime::{
    l_Std_Time_PlainDateTime_ofWallTime, l_Std_Time_PlainDateTime_toWallTime,
};
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Time::PlainTime::l_Std_Time_PlainTime_midnight;
use crate::r#gen::Std::Time::Zoned::Database::{
    initialize_Std_Time_Zoned_Database, l_Std_Time_Database_defaultGetLocalZoneRules,
    l_Std_Time_Database_defaultGetZoneRules, runtime_initialize_Std_Time_Zoned_Database,
};
use crate::r#gen::Std::Time::Zoned::DateTime::{
    initialize_Std_Time_Zoned_DateTime, runtime_initialize_Std_Time_Zoned_DateTime,
};
use crate::r#gen::Std::Time::Zoned::ZoneRules::{
    initialize_Std_Time_Zoned_ZoneRules, l_Std_Time_TimeZone_LocalTimeType_getTimeZone,
    l_Std_Time_TimeZone_Transition_findTransitionForTimestamp,
    l_Std_Time_TimeZone_Transition_timezoneAt,
    l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime,
    runtime_initialize_Std_Time_Zoned_ZoneRules,
};
use crate::r#gen::Std::Time::Zoned::ZonedDateTime::{
    initialize_Std_Time_Zoned_ZonedDateTime, runtime_initialize_Std_Time_Zoned_ZonedDateTime,
};
static mut l_Std_Time_PlainDateTime_now___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_now___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_now___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_now___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofLocalDate___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_ofLocalDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_PlainDateTime_now___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_580_ = lean_nat_to_int(v___x_579_);
    return v___x_580_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_now___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_582_ = lean_nat_to_int(v___x_581_);
    return v___x_582_;
}
pub unsafe fn l_Std_Time_PlainDateTime_now() -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_590_: u8 = 0;
    let mut v___y_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localTimeType_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_a_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_a_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_584_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_584_) == 0 {
                    v_a_585_ = crate::leanh::lean_ctor_get(v___x_584_, 0);
                    crate::leanh::lean_inc(v_a_585_);
                    crate::leanh::lean_dec_ref_known(v___x_584_, 1);
                    v___x_586_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                    if crate::leanh::lean_obj_tag(v___x_586_) == 0 {
                        v_a_587_ = crate::leanh::lean_ctor_get(v___x_586_, 0);
                        v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v___x_586_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v___x_589_ = v___x_586_;
                            v_isShared_590_ = v_isSharedCheck_614_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_587_);
                            crate::leanh::lean_dec(v___x_586_);
                            v___x_589_ = crate::leanh::lean_box(0);
                            v_isShared_590_ = v_isSharedCheck_614_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_585_);
                        v_a_615_ = crate::leanh::lean_ctor_get(v___x_586_, 0);
                        v_isSharedCheck_622_ = (!crate::leanh::lean_is_exclusive(v___x_586_)) as u8;
                        if v_isSharedCheck_622_ == 0 {
                            v___x_617_ = v___x_586_;
                            v_isShared_618_ = v_isSharedCheck_622_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_615_);
                            crate::leanh::lean_dec(v___x_586_);
                            v___x_617_ = crate::leanh::lean_box(0);
                            v_isShared_618_ = v_isSharedCheck_622_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_623_ = crate::leanh::lean_ctor_get(v___x_584_, 0);
                    v_isSharedCheck_630_ = (!crate::leanh::lean_is_exclusive(v___x_584_)) as u8;
                    if v_isSharedCheck_630_ == 0 {
                        v___x_625_ = v___x_584_;
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_623_);
                        crate::leanh::lean_dec(v___x_584_);
                        v___x_625_ = crate::leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_initialLocalTimeType_609_ = crate::leanh::lean_ctor_get(v_a_587_, 0);
                crate::leanh::lean_inc_ref(v_initialLocalTimeType_609_);
                v_transitions_610_ = crate::leanh::lean_ctor_get(v_a_587_, 1);
                crate::leanh::lean_inc_ref(v_transitions_610_);
                crate::leanh::lean_dec(v_a_587_);
                v___x_611_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
                    v_transitions_610_,
                    v_a_585_,
                );
                crate::leanh::lean_dec_ref(v_transitions_610_);
                if crate::leanh::lean_obj_tag(v___x_611_) == 0 {
                    v___y_592_ = v_initialLocalTimeType_609_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_initialLocalTimeType_609_);
                    v_val_612_ = crate::leanh::lean_ctor_get(v___x_611_, 0);
                    crate::leanh::lean_inc(v_val_612_);
                    crate::leanh::lean_dec_ref_known(v___x_611_, 1);
                    v_localTimeType_613_ = crate::leanh::lean_ctor_get(v_val_612_, 1);
                    crate::leanh::lean_inc_ref(v_localTimeType_613_);
                    crate::leanh::lean_dec(v_val_612_);
                    v___y_592_ = v_localTimeType_613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_593_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_592_);
                crate::leanh::lean_dec_ref(v___y_592_);
                v_offset_594_ = crate::leanh::lean_ctor_get(v___x_593_, 0);
                crate::leanh::lean_inc(v_offset_594_);
                crate::leanh::lean_dec_ref(v___x_593_);
                v_second_595_ = crate::leanh::lean_ctor_get(v_a_585_, 0);
                crate::leanh::lean_inc(v_second_595_);
                v_nano_596_ = crate::leanh::lean_ctor_get(v_a_585_, 1);
                crate::leanh::lean_inc(v_nano_596_);
                crate::leanh::lean_dec(v_a_585_);
                v___x_597_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__0,
                );
                v___x_598_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__1,
                );
                v___x_599_ = lean_int_mul(v_second_595_, v___x_598_);
                crate::leanh::lean_dec(v_second_595_);
                v___x_600_ = lean_int_add(v___x_599_, v_nano_596_);
                crate::leanh::lean_dec(v_nano_596_);
                crate::leanh::lean_dec(v___x_599_);
                v___x_601_ = lean_int_mul(v_offset_594_, v___x_598_);
                crate::leanh::lean_dec(v_offset_594_);
                v___x_602_ = lean_int_add(v___x_601_, v___x_597_);
                crate::leanh::lean_dec(v___x_601_);
                v___x_603_ = lean_int_add(v___x_600_, v___x_602_);
                crate::leanh::lean_dec(v___x_602_);
                crate::leanh::lean_dec(v___x_600_);
                v___x_604_ = l_Std_Time_Duration_ofNanoseconds(v___x_603_);
                crate::leanh::lean_dec(v___x_603_);
                v___x_605_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_604_);
                if v_isShared_590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_589_, 0, v___x_605_);
                    v___x_607_ = v___x_589_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
                    v___x_607_ = v_reuseFailAlloc_608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_607_;
            }
            4 => {
                if v_isShared_618_ == 0 {
                    v___x_620_ = v___x_617_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_620_;
            }
            6 => {
                if v_isShared_626_ == 0 {
                    v___x_628_ = v___x_625_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
                    v___x_628_ = v_reuseFailAlloc_629_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_now___boxed(
    mut v_a_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Std_Time_PlainDateTime_now();
    return v_res_632_;
}
pub unsafe fn l_Std_Time_PlainDate_now() -> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___y_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localTimeType_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut v_a_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_a_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_634_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_634_) == 0 {
                    v_a_635_ = crate::leanh::lean_ctor_get(v___x_634_, 0);
                    crate::leanh::lean_inc(v_a_635_);
                    crate::leanh::lean_dec_ref_known(v___x_634_, 1);
                    v___x_636_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                    if crate::leanh::lean_obj_tag(v___x_636_) == 0 {
                        v_a_637_ = crate::leanh::lean_ctor_get(v___x_636_, 0);
                        v_isSharedCheck_665_ = (!crate::leanh::lean_is_exclusive(v___x_636_)) as u8;
                        if v_isSharedCheck_665_ == 0 {
                            v___x_639_ = v___x_636_;
                            v_isShared_640_ = v_isSharedCheck_665_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_637_);
                            crate::leanh::lean_dec(v___x_636_);
                            v___x_639_ = crate::leanh::lean_box(0);
                            v_isShared_640_ = v_isSharedCheck_665_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_635_);
                        v_a_666_ = crate::leanh::lean_ctor_get(v___x_636_, 0);
                        v_isSharedCheck_673_ = (!crate::leanh::lean_is_exclusive(v___x_636_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_668_ = v___x_636_;
                            v_isShared_669_ = v_isSharedCheck_673_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_666_);
                            crate::leanh::lean_dec(v___x_636_);
                            v___x_668_ = crate::leanh::lean_box(0);
                            v_isShared_669_ = v_isSharedCheck_673_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_674_ = crate::leanh::lean_ctor_get(v___x_634_, 0);
                    v_isSharedCheck_681_ = (!crate::leanh::lean_is_exclusive(v___x_634_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v___x_676_ = v___x_634_;
                        v_isShared_677_ = v_isSharedCheck_681_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_674_);
                        crate::leanh::lean_dec(v___x_634_);
                        v___x_676_ = crate::leanh::lean_box(0);
                        v_isShared_677_ = v_isSharedCheck_681_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_initialLocalTimeType_660_ = crate::leanh::lean_ctor_get(v_a_637_, 0);
                crate::leanh::lean_inc_ref(v_initialLocalTimeType_660_);
                v_transitions_661_ = crate::leanh::lean_ctor_get(v_a_637_, 1);
                crate::leanh::lean_inc_ref(v_transitions_661_);
                crate::leanh::lean_dec(v_a_637_);
                v___x_662_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
                    v_transitions_661_,
                    v_a_635_,
                );
                crate::leanh::lean_dec_ref(v_transitions_661_);
                if crate::leanh::lean_obj_tag(v___x_662_) == 0 {
                    v___y_642_ = v_initialLocalTimeType_660_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_initialLocalTimeType_660_);
                    v_val_663_ = crate::leanh::lean_ctor_get(v___x_662_, 0);
                    crate::leanh::lean_inc(v_val_663_);
                    crate::leanh::lean_dec_ref_known(v___x_662_, 1);
                    v_localTimeType_664_ = crate::leanh::lean_ctor_get(v_val_663_, 1);
                    crate::leanh::lean_inc_ref(v_localTimeType_664_);
                    crate::leanh::lean_dec(v_val_663_);
                    v___y_642_ = v_localTimeType_664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_643_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_642_);
                crate::leanh::lean_dec_ref(v___y_642_);
                v_offset_644_ = crate::leanh::lean_ctor_get(v___x_643_, 0);
                crate::leanh::lean_inc(v_offset_644_);
                crate::leanh::lean_dec_ref(v___x_643_);
                v_second_645_ = crate::leanh::lean_ctor_get(v_a_635_, 0);
                crate::leanh::lean_inc(v_second_645_);
                v_nano_646_ = crate::leanh::lean_ctor_get(v_a_635_, 1);
                crate::leanh::lean_inc(v_nano_646_);
                crate::leanh::lean_dec(v_a_635_);
                v___x_647_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__0,
                );
                v___x_648_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__1,
                );
                v___x_649_ = lean_int_mul(v_second_645_, v___x_648_);
                crate::leanh::lean_dec(v_second_645_);
                v___x_650_ = lean_int_add(v___x_649_, v_nano_646_);
                crate::leanh::lean_dec(v_nano_646_);
                crate::leanh::lean_dec(v___x_649_);
                v___x_651_ = lean_int_mul(v_offset_644_, v___x_648_);
                crate::leanh::lean_dec(v_offset_644_);
                v___x_652_ = lean_int_add(v___x_651_, v___x_647_);
                crate::leanh::lean_dec(v___x_651_);
                v___x_653_ = lean_int_add(v___x_650_, v___x_652_);
                crate::leanh::lean_dec(v___x_652_);
                crate::leanh::lean_dec(v___x_650_);
                v___x_654_ = l_Std_Time_Duration_ofNanoseconds(v___x_653_);
                crate::leanh::lean_dec(v___x_653_);
                v___x_655_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_654_);
                v_date_656_ = crate::leanh::lean_ctor_get(v___x_655_, 0);
                crate::leanh::lean_inc_ref(v_date_656_);
                crate::leanh::lean_dec_ref(v___x_655_);
                if v_isShared_640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_639_, 0, v_date_656_);
                    v___x_658_ = v___x_639_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v_date_656_);
                    v___x_658_ = v_reuseFailAlloc_659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_658_;
            }
            4 => {
                if v_isShared_669_ == 0 {
                    v___x_671_ = v___x_668_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
                    v___x_671_ = v_reuseFailAlloc_672_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_671_;
            }
            6 => {
                if v_isShared_677_ == 0 {
                    v___x_679_ = v___x_676_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
                    v___x_679_ = v_reuseFailAlloc_680_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_now___boxed(
    mut v_a_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Std_Time_PlainDate_now();
    return v_res_683_;
}
pub unsafe fn l_Std_Time_PlainTime_now() -> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___y_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localTimeType_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut v_a_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_a_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_728_: u8 = 0;
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_685_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_685_) == 0 {
                    v_a_686_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                    crate::leanh::lean_inc(v_a_686_);
                    crate::leanh::lean_dec_ref_known(v___x_685_, 1);
                    v___x_687_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                    if crate::leanh::lean_obj_tag(v___x_687_) == 0 {
                        v_a_688_ = crate::leanh::lean_ctor_get(v___x_687_, 0);
                        v_isSharedCheck_716_ = (!crate::leanh::lean_is_exclusive(v___x_687_)) as u8;
                        if v_isSharedCheck_716_ == 0 {
                            v___x_690_ = v___x_687_;
                            v_isShared_691_ = v_isSharedCheck_716_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_688_);
                            crate::leanh::lean_dec(v___x_687_);
                            v___x_690_ = crate::leanh::lean_box(0);
                            v_isShared_691_ = v_isSharedCheck_716_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_686_);
                        v_a_717_ = crate::leanh::lean_ctor_get(v___x_687_, 0);
                        v_isSharedCheck_724_ = (!crate::leanh::lean_is_exclusive(v___x_687_)) as u8;
                        if v_isSharedCheck_724_ == 0 {
                            v___x_719_ = v___x_687_;
                            v_isShared_720_ = v_isSharedCheck_724_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_717_);
                            crate::leanh::lean_dec(v___x_687_);
                            v___x_719_ = crate::leanh::lean_box(0);
                            v_isShared_720_ = v_isSharedCheck_724_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_725_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                    v_isSharedCheck_732_ = (!crate::leanh::lean_is_exclusive(v___x_685_)) as u8;
                    if v_isSharedCheck_732_ == 0 {
                        v___x_727_ = v___x_685_;
                        v_isShared_728_ = v_isSharedCheck_732_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_725_);
                        crate::leanh::lean_dec(v___x_685_);
                        v___x_727_ = crate::leanh::lean_box(0);
                        v_isShared_728_ = v_isSharedCheck_732_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_initialLocalTimeType_711_ = crate::leanh::lean_ctor_get(v_a_688_, 0);
                crate::leanh::lean_inc_ref(v_initialLocalTimeType_711_);
                v_transitions_712_ = crate::leanh::lean_ctor_get(v_a_688_, 1);
                crate::leanh::lean_inc_ref(v_transitions_712_);
                crate::leanh::lean_dec(v_a_688_);
                v___x_713_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
                    v_transitions_712_,
                    v_a_686_,
                );
                crate::leanh::lean_dec_ref(v_transitions_712_);
                if crate::leanh::lean_obj_tag(v___x_713_) == 0 {
                    v___y_693_ = v_initialLocalTimeType_711_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_initialLocalTimeType_711_);
                    v_val_714_ = crate::leanh::lean_ctor_get(v___x_713_, 0);
                    crate::leanh::lean_inc(v_val_714_);
                    crate::leanh::lean_dec_ref_known(v___x_713_, 1);
                    v_localTimeType_715_ = crate::leanh::lean_ctor_get(v_val_714_, 1);
                    crate::leanh::lean_inc_ref(v_localTimeType_715_);
                    crate::leanh::lean_dec(v_val_714_);
                    v___y_693_ = v_localTimeType_715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_694_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_693_);
                crate::leanh::lean_dec_ref(v___y_693_);
                v_offset_695_ = crate::leanh::lean_ctor_get(v___x_694_, 0);
                crate::leanh::lean_inc(v_offset_695_);
                crate::leanh::lean_dec_ref(v___x_694_);
                v_second_696_ = crate::leanh::lean_ctor_get(v_a_686_, 0);
                crate::leanh::lean_inc(v_second_696_);
                v_nano_697_ = crate::leanh::lean_ctor_get(v_a_686_, 1);
                crate::leanh::lean_inc(v_nano_697_);
                crate::leanh::lean_dec(v_a_686_);
                v___x_698_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__0,
                );
                v___x_699_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__1,
                );
                v___x_700_ = lean_int_mul(v_second_696_, v___x_699_);
                crate::leanh::lean_dec(v_second_696_);
                v___x_701_ = lean_int_add(v___x_700_, v_nano_697_);
                crate::leanh::lean_dec(v_nano_697_);
                crate::leanh::lean_dec(v___x_700_);
                v___x_702_ = lean_int_mul(v_offset_695_, v___x_699_);
                crate::leanh::lean_dec(v_offset_695_);
                v___x_703_ = lean_int_add(v___x_702_, v___x_698_);
                crate::leanh::lean_dec(v___x_702_);
                v___x_704_ = lean_int_add(v___x_701_, v___x_703_);
                crate::leanh::lean_dec(v___x_703_);
                crate::leanh::lean_dec(v___x_701_);
                v___x_705_ = l_Std_Time_Duration_ofNanoseconds(v___x_704_);
                crate::leanh::lean_dec(v___x_704_);
                v___x_706_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_705_);
                v_time_707_ = crate::leanh::lean_ctor_get(v___x_706_, 1);
                crate::leanh::lean_inc_ref(v_time_707_);
                crate::leanh::lean_dec_ref(v___x_706_);
                if v_isShared_691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_690_, 0, v_time_707_);
                    v___x_709_ = v___x_690_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_710_, 0, v_time_707_);
                    v___x_709_ = v_reuseFailAlloc_710_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_709_;
            }
            4 => {
                if v_isShared_720_ == 0 {
                    v___x_722_ = v___x_719_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
                    v___x_722_ = v_reuseFailAlloc_723_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_722_;
            }
            6 => {
                if v_isShared_728_ == 0 {
                    v___x_730_ = v___x_727_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
                    v___x_730_ = v_reuseFailAlloc_731_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_now___boxed(
    mut v_a_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Std_Time_PlainTime_now();
    return v_res_734_;
}
pub unsafe fn l_Std_Time_DateTime_ofLocalDate___lam__0(
    mut v___x_735_: *mut crate::leanh::LeanObject,
    mut v_x_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___x_735_);
    return v___x_735_;
}
pub unsafe fn l_Std_Time_DateTime_ofLocalDate___lam__0___boxed(
    mut v___x_737_: *mut crate::leanh::LeanObject,
    mut v_x_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Std_Time_DateTime_ofLocalDate___lam__0(v___x_737_, v_x_738_);
    crate::leanh::lean_dec_ref(v___x_737_);
    return v_res_739_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofLocalDate___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
        _init_l_Std_Time_PlainDateTime_now___closed__0,
    );
    v___x_741_ = lean_int_neg(v___x_740_);
    return v___x_741_;
}
pub unsafe fn l_Std_Time_DateTime_ofLocalDate(
    mut v_pd_742_: *mut crate::leanh::LeanObject,
    mut v_tz_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___f_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_744_ = crate::leanh::lean_ctor_get(v_tz_743_, 0);
                v___x_745_ = l_Std_Time_PlainTime_midnight;
                v___x_746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_746_, 0, v_pd_742_);
                crate::leanh::lean_ctor_set(v___x_746_, 1, v___x_745_);
                crate::leanh::lean_inc_ref(v___x_746_);
                v___x_747_ = l_Std_Time_PlainDateTime_toWallTime(v___x_746_);
                v_second_748_ = crate::leanh::lean_ctor_get(v___x_747_, 0);
                v_nano_749_ = crate::leanh::lean_ctor_get(v___x_747_, 1);
                v_isSharedCheck_767_ = (!crate::leanh::lean_is_exclusive(v___x_747_)) as u8;
                if v_isSharedCheck_767_ == 0 {
                    v___x_751_ = v___x_747_;
                    v_isShared_752_ = v_isSharedCheck_767_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_749_);
                    crate::leanh::lean_inc(v_second_748_);
                    crate::leanh::lean_dec(v___x_747_);
                    v___x_751_ = crate::leanh::lean_box(0);
                    v_isShared_752_ = v_isSharedCheck_767_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_753_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_ofLocalDate___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_753_, 0, v___x_746_);
                v___x_754_ = lean_int_neg(v_offset_744_);
                v___x_755_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
                    _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
                );
                v___x_756_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__1,
                );
                v___x_757_ = lean_int_mul(v_second_748_, v___x_756_);
                crate::leanh::lean_dec(v_second_748_);
                v___x_758_ = lean_int_add(v___x_757_, v_nano_749_);
                crate::leanh::lean_dec(v_nano_749_);
                crate::leanh::lean_dec(v___x_757_);
                v___x_759_ = lean_int_mul(v___x_754_, v___x_756_);
                crate::leanh::lean_dec(v___x_754_);
                v___x_760_ = lean_int_add(v___x_759_, v___x_755_);
                crate::leanh::lean_dec(v___x_759_);
                v___x_761_ = lean_int_add(v___x_758_, v___x_760_);
                crate::leanh::lean_dec(v___x_760_);
                crate::leanh::lean_dec(v___x_758_);
                v_tm_762_ = l_Std_Time_Duration_ofNanoseconds(v___x_761_);
                crate::leanh::lean_dec(v___x_761_);
                v___x_763_ = lean_mk_thunk(v___f_753_);
                if v_isShared_752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_763_);
                    crate::leanh::lean_ctor_set(v___x_751_, 0, v_tm_762_);
                    v___x_765_ = v___x_751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 0, v_tm_762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_763_);
                    v___x_765_ = v_reuseFailAlloc_766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_ofLocalDate___boxed(
    mut v_pd_768_: *mut crate::leanh::LeanObject,
    mut v_tz_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Std_Time_DateTime_ofLocalDate(v_pd_768_, v_tz_769_);
    crate::leanh::lean_dec_ref(v_tz_769_);
    return v_res_770_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDate___redArg(
    mut v_dt_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_772_ = crate::leanh::lean_ctor_get(v_dt_771_, 1);
    v___x_773_ = lean_thunk_get_own(v_date_772_);
    v_date_774_ = crate::leanh::lean_ctor_get(v___x_773_, 0);
    crate::leanh::lean_inc_ref(v_date_774_);
    crate::leanh::lean_dec(v___x_773_);
    return v_date_774_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDate___redArg___boxed(
    mut v_dt_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_776_ = l_Std_Time_DateTime_toPlainDate___redArg(v_dt_775_);
    crate::leanh::lean_dec_ref(v_dt_775_);
    return v_res_776_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDate(
    mut v_tz_777_: *mut crate::leanh::LeanObject,
    mut v_dt_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_779_ = crate::leanh::lean_ctor_get(v_dt_778_, 1);
    v___x_780_ = lean_thunk_get_own(v_date_779_);
    v_date_781_ = crate::leanh::lean_ctor_get(v___x_780_, 0);
    crate::leanh::lean_inc_ref(v_date_781_);
    crate::leanh::lean_dec(v___x_780_);
    return v_date_781_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDate___boxed(
    mut v_tz_782_: *mut crate::leanh::LeanObject,
    mut v_dt_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Std_Time_DateTime_toPlainDate(v_tz_782_, v_dt_783_);
    crate::leanh::lean_dec_ref(v_dt_783_);
    crate::leanh::lean_dec_ref(v_tz_782_);
    return v_res_784_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainTime___redArg(
    mut v_dt_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_786_ = crate::leanh::lean_ctor_get(v_dt_785_, 1);
    v___x_787_ = lean_thunk_get_own(v_date_786_);
    v_time_788_ = crate::leanh::lean_ctor_get(v___x_787_, 1);
    crate::leanh::lean_inc_ref(v_time_788_);
    crate::leanh::lean_dec(v___x_787_);
    return v_time_788_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainTime___redArg___boxed(
    mut v_dt_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Std_Time_DateTime_toPlainTime___redArg(v_dt_789_);
    crate::leanh::lean_dec_ref(v_dt_789_);
    return v_res_790_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainTime(
    mut v_tz_791_: *mut crate::leanh::LeanObject,
    mut v_dt_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_793_ = crate::leanh::lean_ctor_get(v_dt_792_, 1);
    v___x_794_ = lean_thunk_get_own(v_date_793_);
    v_time_795_ = crate::leanh::lean_ctor_get(v___x_794_, 1);
    crate::leanh::lean_inc_ref(v_time_795_);
    crate::leanh::lean_dec(v___x_794_);
    return v_time_795_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainTime___boxed(
    mut v_tz_796_: *mut crate::leanh::LeanObject,
    mut v_dt_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Std_Time_DateTime_toPlainTime(v_tz_796_, v_dt_797_);
    crate::leanh::lean_dec_ref(v_dt_797_);
    crate::leanh::lean_dec_ref(v_tz_796_);
    return v_res_798_;
}
pub unsafe fn l_Std_Time_DateTime_now___lam__0(
    mut v_tz_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_x_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_802_ = crate::leanh::lean_ctor_get(v_tz_799_, 0);
    v_second_803_ = crate::leanh::lean_ctor_get(v_a_800_, 0);
    v_nano_804_ = crate::leanh::lean_ctor_get(v_a_800_, 1);
    v___x_805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
        _init_l_Std_Time_PlainDateTime_now___closed__0,
    );
    v___x_806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_807_ = lean_int_mul(v_second_803_, v___x_806_);
    v___x_808_ = lean_int_add(v___x_807_, v_nano_804_);
    crate::leanh::lean_dec(v___x_807_);
    v___x_809_ = lean_int_mul(v_offset_802_, v___x_806_);
    v___x_810_ = lean_int_add(v___x_809_, v___x_805_);
    crate::leanh::lean_dec(v___x_809_);
    v___x_811_ = lean_int_add(v___x_808_, v___x_810_);
    crate::leanh::lean_dec(v___x_810_);
    crate::leanh::lean_dec(v___x_808_);
    v___x_812_ = l_Std_Time_Duration_ofNanoseconds(v___x_811_);
    crate::leanh::lean_dec(v___x_811_);
    v___x_813_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_812_);
    return v___x_813_;
}
pub unsafe fn l_Std_Time_DateTime_now___lam__0___boxed(
    mut v_tz_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_x_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_817_ = l_Std_Time_DateTime_now___lam__0(v_tz_814_, v_a_815_, v_x_816_);
    crate::leanh::lean_dec_ref(v_a_815_);
    crate::leanh::lean_dec_ref(v_tz_814_);
    return v_res_817_;
}
pub unsafe fn l_Std_Time_DateTime_now(
    mut v_tz_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_824_: u8 = 0;
    let mut v___f_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v_a_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_820_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_820_) == 0 {
                    v_a_821_ = crate::leanh::lean_ctor_get(v___x_820_, 0);
                    v_isSharedCheck_831_ = (!crate::leanh::lean_is_exclusive(v___x_820_)) as u8;
                    if v_isSharedCheck_831_ == 0 {
                        v___x_823_ = v___x_820_;
                        v_isShared_824_ = v_isSharedCheck_831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_821_);
                        crate::leanh::lean_dec(v___x_820_);
                        v___x_823_ = crate::leanh::lean_box(0);
                        v_isShared_824_ = v_isSharedCheck_831_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tz_818_);
                    v_a_832_ = crate::leanh::lean_ctor_get(v___x_820_, 0);
                    v_isSharedCheck_839_ = (!crate::leanh::lean_is_exclusive(v___x_820_)) as u8;
                    if v_isSharedCheck_839_ == 0 {
                        v___x_834_ = v___x_820_;
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_832_);
                        crate::leanh::lean_dec(v___x_820_);
                        v___x_834_ = crate::leanh::lean_box(0);
                        v_isShared_835_ = v_isSharedCheck_839_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_821_);
                v___f_825_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_now___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_825_, 0, v_tz_818_);
                crate::leanh::lean_closure_set(v___f_825_, 1, v_a_821_);
                v___x_826_ = lean_mk_thunk(v___f_825_);
                v___x_827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_827_, 0, v_a_821_);
                crate::leanh::lean_ctor_set(v___x_827_, 1, v___x_826_);
                if v_isShared_824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_823_, 0, v___x_827_);
                    v___x_829_ = v___x_823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
                    v___x_829_ = v_reuseFailAlloc_830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_829_;
            }
            3 => {
                if v_isShared_835_ == 0 {
                    v___x_837_ = v___x_834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
                    v___x_837_ = v_reuseFailAlloc_838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_now___boxed(
    mut v_tz_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Std_Time_DateTime_now(v_tz_840_);
    return v_res_842_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_now___lam__0(
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_x_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_846_ = crate::leanh::lean_ctor_get(v___y_843_, 0);
    v_second_847_ = crate::leanh::lean_ctor_get(v_a_844_, 0);
    v_nano_848_ = crate::leanh::lean_ctor_get(v_a_844_, 1);
    v___x_849_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__0_once),
        _init_l_Std_Time_PlainDateTime_now___closed__0,
    );
    v___x_850_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_851_ = lean_int_mul(v_second_847_, v___x_850_);
    v___x_852_ = lean_int_add(v___x_851_, v_nano_848_);
    crate::leanh::lean_dec(v___x_851_);
    v___x_853_ = lean_int_mul(v_offset_846_, v___x_850_);
    v___x_854_ = lean_int_add(v___x_853_, v___x_849_);
    crate::leanh::lean_dec(v___x_853_);
    v___x_855_ = lean_int_add(v___x_852_, v___x_854_);
    crate::leanh::lean_dec(v___x_854_);
    crate::leanh::lean_dec(v___x_852_);
    v___x_856_ = l_Std_Time_Duration_ofNanoseconds(v___x_855_);
    crate::leanh::lean_dec(v___x_855_);
    v___x_857_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_856_);
    return v___x_857_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_now___lam__0___boxed(
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_x_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_Time_ZonedDateTime_now___lam__0(v___y_858_, v_a_859_, v_x_860_);
    crate::leanh::lean_dec_ref(v_a_859_);
    crate::leanh::lean_dec_ref(v___y_858_);
    return v_res_861_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_now() -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___y_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v_a_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_895_: u8 = 0;
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_863_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_863_) == 0 {
                    v_a_864_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                    crate::leanh::lean_inc(v_a_864_);
                    crate::leanh::lean_dec_ref_known(v___x_863_, 1);
                    v___x_865_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                    if crate::leanh::lean_obj_tag(v___x_865_) == 0 {
                        v_a_866_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                        v_isSharedCheck_883_ = (!crate::leanh::lean_is_exclusive(v___x_865_)) as u8;
                        if v_isSharedCheck_883_ == 0 {
                            v___x_868_ = v___x_865_;
                            v_isShared_869_ = v_isSharedCheck_883_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_866_);
                            crate::leanh::lean_dec(v___x_865_);
                            v___x_868_ = crate::leanh::lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_883_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_864_);
                        v_a_884_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                        v_isSharedCheck_891_ = (!crate::leanh::lean_is_exclusive(v___x_865_)) as u8;
                        if v_isSharedCheck_891_ == 0 {
                            v___x_886_ = v___x_865_;
                            v_isShared_887_ = v_isSharedCheck_891_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_884_);
                            crate::leanh::lean_dec(v___x_865_);
                            v___x_886_ = crate::leanh::lean_box(0);
                            v_isShared_887_ = v_isSharedCheck_891_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_892_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                    v_isSharedCheck_899_ = (!crate::leanh::lean_is_exclusive(v___x_863_)) as u8;
                    if v_isSharedCheck_899_ == 0 {
                        v___x_894_ = v___x_863_;
                        v_isShared_895_ = v_isSharedCheck_899_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_892_);
                        crate::leanh::lean_dec(v___x_863_);
                        v___x_894_ = crate::leanh::lean_box(0);
                        v_isShared_895_ = v_isSharedCheck_899_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_initialLocalTimeType_878_ = crate::leanh::lean_ctor_get(v_a_866_, 0);
                v_transitions_879_ = crate::leanh::lean_ctor_get(v_a_866_, 1);
                v___x_880_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_879_, v_a_864_);
                if crate::leanh::lean_obj_tag(v___x_880_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_880_, 1);
                    v___x_881_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_878_);
                    v___y_871_ = v___x_881_;
                    state = 2;
                    continue;
                } else {
                    v_a_882_ = crate::leanh::lean_ctor_get(v___x_880_, 0);
                    crate::leanh::lean_inc(v_a_882_);
                    crate::leanh::lean_dec_ref_known(v___x_880_, 1);
                    v___y_871_ = v_a_882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_864_);
                crate::leanh::lean_inc_ref(v___y_871_);
                v___f_872_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_now___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_872_, 0, v___y_871_);
                crate::leanh::lean_closure_set(v___f_872_, 1, v_a_864_);
                v___x_873_ = lean_mk_thunk(v___f_872_);
                v___x_874_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
                crate::leanh::lean_ctor_set(v___x_874_, 1, v_a_864_);
                crate::leanh::lean_ctor_set(v___x_874_, 2, v_a_866_);
                crate::leanh::lean_ctor_set(v___x_874_, 3, v___y_871_);
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_874_);
                    v___x_876_ = v___x_868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
                    v___x_876_ = v_reuseFailAlloc_877_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_876_;
            }
            4 => {
                if v_isShared_887_ == 0 {
                    v___x_889_ = v___x_886_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_889_;
            }
            6 => {
                if v_isShared_895_ == 0 {
                    v___x_897_ = v___x_894_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
                    v___x_897_ = v_reuseFailAlloc_898_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_now___boxed(
    mut v_a_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_901_ = l_Std_Time_ZonedDateTime_now();
    return v_res_901_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nowAt(
    mut v_id_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_910_: u8 = 0;
    let mut v___y_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_924_: u8 = 0;
    let mut v_a_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_928_: u8 = 0;
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut v_a_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_904_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_904_) == 0 {
                    v_a_905_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                    crate::leanh::lean_inc(v_a_905_);
                    crate::leanh::lean_dec_ref_known(v___x_904_, 1);
                    v___x_906_ = l_Std_Time_Database_defaultGetZoneRules(v_id_902_);
                    if crate::leanh::lean_obj_tag(v___x_906_) == 0 {
                        v_a_907_ = crate::leanh::lean_ctor_get(v___x_906_, 0);
                        v_isSharedCheck_924_ = (!crate::leanh::lean_is_exclusive(v___x_906_)) as u8;
                        if v_isSharedCheck_924_ == 0 {
                            v___x_909_ = v___x_906_;
                            v_isShared_910_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_907_);
                            crate::leanh::lean_dec(v___x_906_);
                            v___x_909_ = crate::leanh::lean_box(0);
                            v_isShared_910_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_905_);
                        v_a_925_ = crate::leanh::lean_ctor_get(v___x_906_, 0);
                        v_isSharedCheck_932_ = (!crate::leanh::lean_is_exclusive(v___x_906_)) as u8;
                        if v_isSharedCheck_932_ == 0 {
                            v___x_927_ = v___x_906_;
                            v_isShared_928_ = v_isSharedCheck_932_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_925_);
                            crate::leanh::lean_dec(v___x_906_);
                            v___x_927_ = crate::leanh::lean_box(0);
                            v_isShared_928_ = v_isSharedCheck_932_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_id_902_);
                    v_a_933_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                    v_isSharedCheck_940_ = (!crate::leanh::lean_is_exclusive(v___x_904_)) as u8;
                    if v_isSharedCheck_940_ == 0 {
                        v___x_935_ = v___x_904_;
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_933_);
                        crate::leanh::lean_dec(v___x_904_);
                        v___x_935_ = crate::leanh::lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_initialLocalTimeType_919_ = crate::leanh::lean_ctor_get(v_a_907_, 0);
                v_transitions_920_ = crate::leanh::lean_ctor_get(v_a_907_, 1);
                v___x_921_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_920_, v_a_905_);
                if crate::leanh::lean_obj_tag(v___x_921_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_921_, 1);
                    v___x_922_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_919_);
                    v___y_912_ = v___x_922_;
                    state = 2;
                    continue;
                } else {
                    v_a_923_ = crate::leanh::lean_ctor_get(v___x_921_, 0);
                    crate::leanh::lean_inc(v_a_923_);
                    crate::leanh::lean_dec_ref_known(v___x_921_, 1);
                    v___y_912_ = v_a_923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_905_);
                crate::leanh::lean_inc_ref(v___y_912_);
                v___f_913_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_now___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_913_, 0, v___y_912_);
                crate::leanh::lean_closure_set(v___f_913_, 1, v_a_905_);
                v___x_914_ = lean_mk_thunk(v___f_913_);
                v___x_915_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_914_);
                crate::leanh::lean_ctor_set(v___x_915_, 1, v_a_905_);
                crate::leanh::lean_ctor_set(v___x_915_, 2, v_a_907_);
                crate::leanh::lean_ctor_set(v___x_915_, 3, v___y_912_);
                if v_isShared_910_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_915_);
                    v___x_917_ = v___x_909_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
                    v___x_917_ = v_reuseFailAlloc_918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_917_;
            }
            4 => {
                if v_isShared_928_ == 0 {
                    v___x_930_ = v___x_927_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_930_;
            }
            6 => {
                if v_isShared_936_ == 0 {
                    v___x_938_ = v___x_935_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
                    v___x_938_ = v_reuseFailAlloc_939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_nowAt___boxed(
    mut v_id_941_: *mut crate::leanh::LeanObject,
    mut v_a_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Std_Time_ZonedDateTime_nowAt(v_id_941_);
    return v_res_943_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofLocalDate(
    mut v_pd_944_: *mut crate::leanh::LeanObject,
    mut v_zr_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Std_Time_PlainTime_midnight;
    v___x_947_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_947_, 0, v_pd_944_);
    crate::leanh::lean_ctor_set(v___x_947_, 1, v___x_946_);
    crate::leanh::lean_inc_ref(v___x_947_);
    v_wt_948_ = l_Std_Time_PlainDateTime_toWallTime(v___x_947_);
    crate::leanh::lean_inc_ref(v_zr_945_);
    v_ltt_949_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_945_, v_wt_948_);
    v_tz_950_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_949_);
    crate::leanh::lean_dec_ref(v_ltt_949_);
    v_offset_951_ = crate::leanh::lean_ctor_get(v_tz_950_, 0);
    crate::leanh::lean_inc(v_offset_951_);
    v_second_952_ = crate::leanh::lean_ctor_get(v_wt_948_, 0);
    crate::leanh::lean_inc(v_second_952_);
    v_nano_953_ = crate::leanh::lean_ctor_get(v_wt_948_, 1);
    crate::leanh::lean_inc(v_nano_953_);
    crate::leanh::lean_dec_ref(v_wt_948_);
    v___f_954_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_ofLocalDate___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_954_, 0, v___x_947_);
    v___x_955_ = lean_mk_thunk(v___f_954_);
    v___x_956_ = lean_int_neg(v_offset_951_);
    crate::leanh::lean_dec(v_offset_951_);
    v___x_957_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_959_ = lean_int_mul(v_second_952_, v___x_958_);
    crate::leanh::lean_dec(v_second_952_);
    v___x_960_ = lean_int_add(v___x_959_, v_nano_953_);
    crate::leanh::lean_dec(v_nano_953_);
    crate::leanh::lean_dec(v___x_959_);
    v___x_961_ = lean_int_mul(v___x_956_, v___x_958_);
    crate::leanh::lean_dec(v___x_956_);
    v___x_962_ = lean_int_add(v___x_961_, v___x_957_);
    crate::leanh::lean_dec(v___x_961_);
    v___x_963_ = lean_int_add(v___x_960_, v___x_962_);
    crate::leanh::lean_dec(v___x_962_);
    crate::leanh::lean_dec(v___x_960_);
    v___x_964_ = l_Std_Time_Duration_ofNanoseconds(v___x_963_);
    crate::leanh::lean_dec(v___x_963_);
    v___x_965_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_965_, 0, v___x_955_);
    crate::leanh::lean_ctor_set(v___x_965_, 1, v___x_964_);
    crate::leanh::lean_ctor_set(v___x_965_, 2, v_zr_945_);
    crate::leanh::lean_ctor_set(v___x_965_, 3, v_tz_950_);
    return v___x_965_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofLocalDateWithZone(
    mut v_pd_968_: *mut crate::leanh::LeanObject,
    mut v_zr_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_973_: u8 = 0;
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v___x_977_: u8 = 0;
    let mut v_ltt_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_970_ = crate::leanh::lean_ctor_get(v_zr_969_, 0);
    v_name_971_ = crate::leanh::lean_ctor_get(v_zr_969_, 1);
    v_abbreviation_972_ = crate::leanh::lean_ctor_get(v_zr_969_, 2);
    v_isDST_973_ = crate::leanh::lean_ctor_get_uint8(
        v_zr_969_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_974_ = l_Std_Time_PlainTime_midnight;
    v___x_975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_975_, 0, v_pd_968_);
    crate::leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
    v___x_976_ = 0;
    v___x_977_ = 1;
    crate::leanh::lean_inc_ref(v_name_971_);
    crate::leanh::lean_inc_ref(v_abbreviation_972_);
    crate::leanh::lean_inc(v_offset_970_);
    v_ltt_978_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
    crate::leanh::lean_ctor_set(v_ltt_978_, 0, v_offset_970_);
    crate::leanh::lean_ctor_set(v_ltt_978_, 1, v_abbreviation_972_);
    crate::leanh::lean_ctor_set(v_ltt_978_, 2, v_name_971_);
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_978_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isDST_973_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_978_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_976_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_978_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v___x_977_,
    );
    v___x_979_ = l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0;
    v___x_980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_980_, 0, v_ltt_978_);
    crate::leanh::lean_ctor_set(v___x_980_, 1, v___x_979_);
    crate::leanh::lean_inc_ref(v___x_975_);
    v_wt_981_ = l_Std_Time_PlainDateTime_toWallTime(v___x_975_);
    crate::leanh::lean_inc_ref(v___x_980_);
    v_ltt_982_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_980_, v_wt_981_);
    v_tz_983_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_982_);
    crate::leanh::lean_dec_ref(v_ltt_982_);
    v_offset_984_ = crate::leanh::lean_ctor_get(v_tz_983_, 0);
    crate::leanh::lean_inc(v_offset_984_);
    v_second_985_ = crate::leanh::lean_ctor_get(v_wt_981_, 0);
    crate::leanh::lean_inc(v_second_985_);
    v_nano_986_ = crate::leanh::lean_ctor_get(v_wt_981_, 1);
    crate::leanh::lean_inc(v_nano_986_);
    crate::leanh::lean_dec_ref(v_wt_981_);
    v___f_987_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_ofLocalDate___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_987_, 0, v___x_975_);
    v___x_988_ = lean_mk_thunk(v___f_987_);
    v___x_989_ = lean_int_neg(v_offset_984_);
    crate::leanh::lean_dec(v_offset_984_);
    v___x_990_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_991_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_992_ = lean_int_mul(v_second_985_, v___x_991_);
    crate::leanh::lean_dec(v_second_985_);
    v___x_993_ = lean_int_add(v___x_992_, v_nano_986_);
    crate::leanh::lean_dec(v_nano_986_);
    crate::leanh::lean_dec(v___x_992_);
    v___x_994_ = lean_int_mul(v___x_989_, v___x_991_);
    crate::leanh::lean_dec(v___x_989_);
    v___x_995_ = lean_int_add(v___x_994_, v___x_990_);
    crate::leanh::lean_dec(v___x_994_);
    v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
    crate::leanh::lean_dec(v___x_995_);
    crate::leanh::lean_dec(v___x_993_);
    v___x_997_ = l_Std_Time_Duration_ofNanoseconds(v___x_996_);
    crate::leanh::lean_dec(v___x_996_);
    v___x_998_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_988_);
    crate::leanh::lean_ctor_set(v___x_998_, 1, v___x_997_);
    crate::leanh::lean_ctor_set(v___x_998_, 2, v___x_980_);
    crate::leanh::lean_ctor_set(v___x_998_, 3, v_tz_983_);
    return v___x_998_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofLocalDateWithZone___boxed(
    mut v_pd_999_: *mut crate::leanh::LeanObject,
    mut v_zr_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Std_Time_ZonedDateTime_ofLocalDateWithZone(v_pd_999_, v_zr_1000_);
    crate::leanh::lean_dec_ref(v_zr_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDate(
    mut v_dt_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_1003_ = crate::leanh::lean_ctor_get(v_dt_1002_, 0);
    v___x_1004_ = lean_thunk_get_own(v_date_1003_);
    v_date_1005_ = crate::leanh::lean_ctor_get(v___x_1004_, 0);
    crate::leanh::lean_inc_ref(v_date_1005_);
    crate::leanh::lean_dec(v___x_1004_);
    return v_date_1005_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDate___boxed(
    mut v_dt_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Std_Time_ZonedDateTime_toPlainDate(v_dt_1006_);
    crate::leanh::lean_dec_ref(v_dt_1006_);
    return v_res_1007_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainTime(
    mut v_dt_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_1009_ = crate::leanh::lean_ctor_get(v_dt_1008_, 0);
    v___x_1010_ = lean_thunk_get_own(v_date_1009_);
    v_time_1011_ = crate::leanh::lean_ctor_get(v___x_1010_, 1);
    crate::leanh::lean_inc_ref(v_time_1011_);
    crate::leanh::lean_dec(v___x_1010_);
    return v_time_1011_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainTime___boxed(
    mut v_dt_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Std_Time_ZonedDateTime_toPlainTime(v_dt_1012_);
    crate::leanh::lean_dec_ref(v_dt_1012_);
    return v_res_1013_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_of___lam__0(
    mut v_pdt_1014_: *mut crate::leanh::LeanObject,
    mut v_x_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_pdt_1014_);
    return v_pdt_1014_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_of___lam__0___boxed(
    mut v_pdt_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Time_ZonedDateTime_of___lam__0(v_pdt_1016_, v_x_1017_);
    crate::leanh::lean_dec_ref(v_pdt_1016_);
    return v_res_1018_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_of(
    mut v_pdt_1019_: *mut crate::leanh::LeanObject,
    mut v_id_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v_wt_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1022_ = l_Std_Time_Database_defaultGetZoneRules(v_id_1020_);
                if crate::leanh::lean_obj_tag(v___x_1022_) == 0 {
                    v_a_1023_ = crate::leanh::lean_ctor_get(v___x_1022_, 0);
                    v_isSharedCheck_1048_ = (!crate::leanh::lean_is_exclusive(v___x_1022_)) as u8;
                    if v_isSharedCheck_1048_ == 0 {
                        v___x_1025_ = v___x_1022_;
                        v_isShared_1026_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1023_);
                        crate::leanh::lean_dec(v___x_1022_);
                        v___x_1025_ = crate::leanh::lean_box(0);
                        v_isShared_1026_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pdt_1019_);
                    v_a_1049_ = crate::leanh::lean_ctor_get(v___x_1022_, 0);
                    v_isSharedCheck_1056_ = (!crate::leanh::lean_is_exclusive(v___x_1022_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1022_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1049_);
                        crate::leanh::lean_dec(v___x_1022_);
                        v___x_1051_ = crate::leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_pdt_1019_);
                v_wt_1027_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1019_);
                crate::leanh::lean_inc(v_a_1023_);
                v_ltt_1028_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_a_1023_, v_wt_1027_,
                );
                v_tz_1029_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1028_);
                crate::leanh::lean_dec_ref(v_ltt_1028_);
                v_offset_1030_ = crate::leanh::lean_ctor_get(v_tz_1029_, 0);
                crate::leanh::lean_inc(v_offset_1030_);
                v_second_1031_ = crate::leanh::lean_ctor_get(v_wt_1027_, 0);
                crate::leanh::lean_inc(v_second_1031_);
                v_nano_1032_ = crate::leanh::lean_ctor_get(v_wt_1027_, 1);
                crate::leanh::lean_inc(v_nano_1032_);
                crate::leanh::lean_dec_ref(v_wt_1027_);
                v___f_1033_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_of___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1033_, 0, v_pdt_1019_);
                v___x_1034_ = lean_mk_thunk(v___f_1033_);
                v___x_1035_ = lean_int_neg(v_offset_1030_);
                crate::leanh::lean_dec(v_offset_1030_);
                v___x_1036_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
                    _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
                );
                v___x_1037_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_now___closed__1,
                );
                v___x_1038_ = lean_int_mul(v_second_1031_, v___x_1037_);
                crate::leanh::lean_dec(v_second_1031_);
                v___x_1039_ = lean_int_add(v___x_1038_, v_nano_1032_);
                crate::leanh::lean_dec(v_nano_1032_);
                crate::leanh::lean_dec(v___x_1038_);
                v___x_1040_ = lean_int_mul(v___x_1035_, v___x_1037_);
                crate::leanh::lean_dec(v___x_1035_);
                v___x_1041_ = lean_int_add(v___x_1040_, v___x_1036_);
                crate::leanh::lean_dec(v___x_1040_);
                v___x_1042_ = lean_int_add(v___x_1039_, v___x_1041_);
                crate::leanh::lean_dec(v___x_1041_);
                crate::leanh::lean_dec(v___x_1039_);
                v___x_1043_ = l_Std_Time_Duration_ofNanoseconds(v___x_1042_);
                crate::leanh::lean_dec(v___x_1042_);
                v___x_1044_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1044_, 0, v___x_1034_);
                crate::leanh::lean_ctor_set(v___x_1044_, 1, v___x_1043_);
                crate::leanh::lean_ctor_set(v___x_1044_, 2, v_a_1023_);
                crate::leanh::lean_ctor_set(v___x_1044_, 3, v_tz_1029_);
                if v_isShared_1026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1025_, 0, v___x_1044_);
                    v___x_1046_ = v___x_1025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
                    v___x_1046_ = v_reuseFailAlloc_1047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1046_;
            }
            3 => {
                if v_isShared_1052_ == 0 {
                    v___x_1054_ = v___x_1051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_of___boxed(
    mut v_pdt_1057_: *mut crate::leanh::LeanObject,
    mut v_id_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Std_Time_ZonedDateTime_of(v_pdt_1057_, v_id_1058_);
    return v_res_1060_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toTimestamp(
    mut v_pdt_1061_: *mut crate::leanh::LeanObject,
    mut v_zr_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_wt_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_wt_1063_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1061_);
    v_ltt_1064_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_1062_, v_wt_1063_);
    v_tz_1065_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1064_);
    crate::leanh::lean_dec_ref(v_ltt_1064_);
    v_offset_1066_ = crate::leanh::lean_ctor_get(v_tz_1065_, 0);
    crate::leanh::lean_inc(v_offset_1066_);
    crate::leanh::lean_dec_ref(v_tz_1065_);
    v_second_1067_ = crate::leanh::lean_ctor_get(v_wt_1063_, 0);
    crate::leanh::lean_inc(v_second_1067_);
    v_nano_1068_ = crate::leanh::lean_ctor_get(v_wt_1063_, 1);
    crate::leanh::lean_inc(v_nano_1068_);
    crate::leanh::lean_dec_ref(v_wt_1063_);
    v___x_1069_ = lean_int_neg(v_offset_1066_);
    crate::leanh::lean_dec(v_offset_1066_);
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_1072_ = lean_int_mul(v_second_1067_, v___x_1071_);
    crate::leanh::lean_dec(v_second_1067_);
    v___x_1073_ = lean_int_add(v___x_1072_, v_nano_1068_);
    crate::leanh::lean_dec(v_nano_1068_);
    crate::leanh::lean_dec(v___x_1072_);
    v___x_1074_ = lean_int_mul(v___x_1069_, v___x_1071_);
    crate::leanh::lean_dec(v___x_1069_);
    v___x_1075_ = lean_int_add(v___x_1074_, v___x_1070_);
    crate::leanh::lean_dec(v___x_1074_);
    v___x_1076_ = lean_int_add(v___x_1073_, v___x_1075_);
    crate::leanh::lean_dec(v___x_1075_);
    crate::leanh::lean_dec(v___x_1073_);
    v___x_1077_ = l_Std_Time_Duration_ofNanoseconds(v___x_1076_);
    crate::leanh::lean_dec(v___x_1076_);
    return v___x_1077_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toTimestampWithZone(
    mut v_pdt_1078_: *mut crate::leanh::LeanObject,
    mut v_tz_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_1083_: u8 = 0;
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v_ltt_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_1080_ = crate::leanh::lean_ctor_get(v_tz_1079_, 0);
    v_name_1081_ = crate::leanh::lean_ctor_get(v_tz_1079_, 1);
    v_abbreviation_1082_ = crate::leanh::lean_ctor_get(v_tz_1079_, 2);
    v_isDST_1083_ = crate::leanh::lean_ctor_get_uint8(
        v_tz_1079_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_1084_ = 0;
    v___x_1085_ = 1;
    crate::leanh::lean_inc_ref(v_name_1081_);
    crate::leanh::lean_inc_ref(v_abbreviation_1082_);
    crate::leanh::lean_inc(v_offset_1080_);
    v_ltt_1086_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
    crate::leanh::lean_ctor_set(v_ltt_1086_, 0, v_offset_1080_);
    crate::leanh::lean_ctor_set(v_ltt_1086_, 1, v_abbreviation_1082_);
    crate::leanh::lean_ctor_set(v_ltt_1086_, 2, v_name_1081_);
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1086_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isDST_1083_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1086_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1084_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1086_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1085_,
    );
    v___x_1087_ = l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0;
    v___x_1088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1088_, 0, v_ltt_1086_);
    crate::leanh::lean_ctor_set(v___x_1088_, 1, v___x_1087_);
    v_wt_1089_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1078_);
    v_ltt_1090_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1088_, v_wt_1089_);
    v_tz_1091_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1090_);
    crate::leanh::lean_dec_ref(v_ltt_1090_);
    v_offset_1092_ = crate::leanh::lean_ctor_get(v_tz_1091_, 0);
    crate::leanh::lean_inc(v_offset_1092_);
    crate::leanh::lean_dec_ref(v_tz_1091_);
    v_second_1093_ = crate::leanh::lean_ctor_get(v_wt_1089_, 0);
    crate::leanh::lean_inc(v_second_1093_);
    v_nano_1094_ = crate::leanh::lean_ctor_get(v_wt_1089_, 1);
    crate::leanh::lean_inc(v_nano_1094_);
    crate::leanh::lean_dec_ref(v_wt_1089_);
    v___x_1095_ = lean_int_neg(v_offset_1092_);
    crate::leanh::lean_dec(v_offset_1092_);
    v___x_1096_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_1097_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_1098_ = lean_int_mul(v_second_1093_, v___x_1097_);
    crate::leanh::lean_dec(v_second_1093_);
    v___x_1099_ = lean_int_add(v___x_1098_, v_nano_1094_);
    crate::leanh::lean_dec(v_nano_1094_);
    crate::leanh::lean_dec(v___x_1098_);
    v___x_1100_ = lean_int_mul(v___x_1095_, v___x_1097_);
    crate::leanh::lean_dec(v___x_1095_);
    v___x_1101_ = lean_int_add(v___x_1100_, v___x_1096_);
    crate::leanh::lean_dec(v___x_1100_);
    v___x_1102_ = lean_int_add(v___x_1099_, v___x_1101_);
    crate::leanh::lean_dec(v___x_1101_);
    crate::leanh::lean_dec(v___x_1099_);
    v___x_1103_ = l_Std_Time_Duration_ofNanoseconds(v___x_1102_);
    crate::leanh::lean_dec(v___x_1102_);
    return v___x_1103_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(
    mut v_pdt_1104_: *mut crate::leanh::LeanObject,
    mut v_tz_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Std_Time_PlainDateTime_toTimestampWithZone(v_pdt_1104_, v_tz_1105_);
    crate::leanh::lean_dec_ref(v_tz_1105_);
    return v_res_1106_;
}
pub unsafe fn l_Std_Time_PlainDate_toTimestamp(
    mut v_dt_1107_: *mut crate::leanh::LeanObject,
    mut v_zr_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Std_Time_PlainTime_midnight;
    v___x_1110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1110_, 0, v_dt_1107_);
    crate::leanh::lean_ctor_set(v___x_1110_, 1, v___x_1109_);
    v_wt_1111_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1110_);
    v_ltt_1112_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_1108_, v_wt_1111_);
    v_tz_1113_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1112_);
    crate::leanh::lean_dec_ref(v_ltt_1112_);
    v_offset_1114_ = crate::leanh::lean_ctor_get(v_tz_1113_, 0);
    crate::leanh::lean_inc(v_offset_1114_);
    crate::leanh::lean_dec_ref(v_tz_1113_);
    v_second_1115_ = crate::leanh::lean_ctor_get(v_wt_1111_, 0);
    crate::leanh::lean_inc(v_second_1115_);
    v_nano_1116_ = crate::leanh::lean_ctor_get(v_wt_1111_, 1);
    crate::leanh::lean_inc(v_nano_1116_);
    crate::leanh::lean_dec_ref(v_wt_1111_);
    v___x_1117_ = lean_int_neg(v_offset_1114_);
    crate::leanh::lean_dec(v_offset_1114_);
    v___x_1118_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_1119_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_1120_ = lean_int_mul(v_second_1115_, v___x_1119_);
    crate::leanh::lean_dec(v_second_1115_);
    v___x_1121_ = lean_int_add(v___x_1120_, v_nano_1116_);
    crate::leanh::lean_dec(v_nano_1116_);
    crate::leanh::lean_dec(v___x_1120_);
    v___x_1122_ = lean_int_mul(v___x_1117_, v___x_1119_);
    crate::leanh::lean_dec(v___x_1117_);
    v___x_1123_ = lean_int_add(v___x_1122_, v___x_1118_);
    crate::leanh::lean_dec(v___x_1122_);
    v___x_1124_ = lean_int_add(v___x_1121_, v___x_1123_);
    crate::leanh::lean_dec(v___x_1123_);
    crate::leanh::lean_dec(v___x_1121_);
    v___x_1125_ = l_Std_Time_Duration_ofNanoseconds(v___x_1124_);
    crate::leanh::lean_dec(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Std_Time_PlainDate_toTimestampWithZone(
    mut v_dt_1126_: *mut crate::leanh::LeanObject,
    mut v_tz_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_1131_: u8 = 0;
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1135_: u8 = 0;
    let mut v_ltt_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_1128_ = crate::leanh::lean_ctor_get(v_tz_1127_, 0);
    v_name_1129_ = crate::leanh::lean_ctor_get(v_tz_1127_, 1);
    v_abbreviation_1130_ = crate::leanh::lean_ctor_get(v_tz_1127_, 2);
    v_isDST_1131_ = crate::leanh::lean_ctor_get_uint8(
        v_tz_1127_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_1132_ = l_Std_Time_PlainTime_midnight;
    v___x_1133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1133_, 0, v_dt_1126_);
    crate::leanh::lean_ctor_set(v___x_1133_, 1, v___x_1132_);
    v___x_1134_ = 0;
    v___x_1135_ = 1;
    crate::leanh::lean_inc_ref(v_name_1129_);
    crate::leanh::lean_inc_ref(v_abbreviation_1130_);
    crate::leanh::lean_inc(v_offset_1128_);
    v_ltt_1136_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
    crate::leanh::lean_ctor_set(v_ltt_1136_, 0, v_offset_1128_);
    crate::leanh::lean_ctor_set(v_ltt_1136_, 1, v_abbreviation_1130_);
    crate::leanh::lean_ctor_set(v_ltt_1136_, 2, v_name_1129_);
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1136_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isDST_1131_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1136_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1134_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_1136_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1135_,
    );
    v___x_1137_ = l_Std_Time_ZonedDateTime_ofLocalDateWithZone___closed__0;
    v___x_1138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1138_, 0, v_ltt_1136_);
    crate::leanh::lean_ctor_set(v___x_1138_, 1, v___x_1137_);
    v_wt_1139_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1133_);
    v_ltt_1140_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1138_, v_wt_1139_);
    v_tz_1141_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1140_);
    crate::leanh::lean_dec_ref(v_ltt_1140_);
    v_offset_1142_ = crate::leanh::lean_ctor_get(v_tz_1141_, 0);
    crate::leanh::lean_inc(v_offset_1142_);
    crate::leanh::lean_dec_ref(v_tz_1141_);
    v_second_1143_ = crate::leanh::lean_ctor_get(v_wt_1139_, 0);
    crate::leanh::lean_inc(v_second_1143_);
    v_nano_1144_ = crate::leanh::lean_ctor_get(v_wt_1139_, 1);
    crate::leanh::lean_inc(v_nano_1144_);
    crate::leanh::lean_dec_ref(v_wt_1139_);
    v___x_1145_ = lean_int_neg(v_offset_1142_);
    crate::leanh::lean_dec(v_offset_1142_);
    v___x_1146_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofLocalDate___closed__0_once),
        _init_l_Std_Time_DateTime_ofLocalDate___closed__0,
    );
    v___x_1147_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_now___closed__1_once),
        _init_l_Std_Time_PlainDateTime_now___closed__1,
    );
    v___x_1148_ = lean_int_mul(v_second_1143_, v___x_1147_);
    crate::leanh::lean_dec(v_second_1143_);
    v___x_1149_ = lean_int_add(v___x_1148_, v_nano_1144_);
    crate::leanh::lean_dec(v_nano_1144_);
    crate::leanh::lean_dec(v___x_1148_);
    v___x_1150_ = lean_int_mul(v___x_1145_, v___x_1147_);
    crate::leanh::lean_dec(v___x_1145_);
    v___x_1151_ = lean_int_add(v___x_1150_, v___x_1146_);
    crate::leanh::lean_dec(v___x_1150_);
    v___x_1152_ = lean_int_add(v___x_1149_, v___x_1151_);
    crate::leanh::lean_dec(v___x_1151_);
    crate::leanh::lean_dec(v___x_1149_);
    v___x_1153_ = l_Std_Time_Duration_ofNanoseconds(v___x_1152_);
    crate::leanh::lean_dec(v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Std_Time_PlainDate_toTimestampWithZone___boxed(
    mut v_dt_1154_: *mut crate::leanh::LeanObject,
    mut v_tz_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_Std_Time_PlainDate_toTimestampWithZone(v_dt_1154_, v_tz_1155_);
    crate::leanh::lean_dec_ref(v_tz_1155_);
    return v_res_1156_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_ZoneRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned(builtin);
}
