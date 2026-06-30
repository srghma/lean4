// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Util
// Imports: Lean.Meta.Tactic.Grind.Order.OrderM Lean.Meta.Tactic.Grind.Arith.Util
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int, lean_string_append,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util, l_Lean_Meta_Grind_Arith_quoteIfArithTerm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::OrderM::{
    initialize_Lean_Meta_Tactic_Grind_Order_OrderM, l_Lean_Meta_Grind_Order_getExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM,
};
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 43, 32, 0],
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 137, 164, 0],
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [60, 0],
    };
static mut l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Order_Weight_compare___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Order_instOrdWeight___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Order_instOrdWeight: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Order_instLEWeight: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Order_instLTWeight: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Order_Weight_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Order_instAddWeight___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Order_instAddWeight: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 2,
    m_data: [45, 206, 181, 0],
};
static mut l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Order_instToStringWeight___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Order_instToStringWeight: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 113, 84, 114, 117, 101, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 113, 70, 97, 108, 115, 101, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 113, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_unsigned_to_nat(0);
    v___x_429_ = lean_nat_to_int(v___x_428_);
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1;
    v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
    return v___x_432_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3;
    v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
    return v___x_435_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_pp(
    mut v_c_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_a_441_: *mut leanh::LeanObject,
    mut v_a_442_: *mut leanh::LeanObject,
    mut v_a_443_: *mut leanh::LeanObject,
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_a_446_: *mut leanh::LeanObject,
    mut v_a_447_: *mut leanh::LeanObject,
    mut v_a_448_: *mut leanh::LeanObject,
    mut v_a_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_451_: u8 = 0;
    let mut v_u_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_461_: u8 = 0;
    let mut v___y_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_a_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_504_: u8 = 0;
    let mut v_a_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_508_: u8 = 0;
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_451_ = leanh::lean_ctor_get_uint8(
                    v_c_438_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_u_452_ = leanh::lean_ctor_get(v_c_438_, 0);
                v_v_453_ = leanh::lean_ctor_get(v_c_438_, 1);
                v_k_454_ = leanh::lean_ctor_get(v_c_438_, 2);
                v___x_455_ = l_Lean_Meta_Grind_Order_getExpr(
                    v_u_452_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
                    v_a_446_, v_a_447_, v_a_448_, v_a_449_,
                );
                if leanh::lean_obj_tag(v___x_455_) == 0 {
                    v_a_456_ = leanh::lean_ctor_get(v___x_455_, 0);
                    leanh::lean_inc(v_a_456_);
                    leanh::lean_dec_ref_known(v___x_455_, 1);
                    v___x_457_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_v_453_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_,
                        v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_,
                    );
                    if leanh::lean_obj_tag(v___x_457_) == 0 {
                        v_a_458_ = leanh::lean_ctor_get(v___x_457_, 0);
                        v_isSharedCheck_496_ = (!leanh::lean_is_exclusive(v___x_457_)) as u8;
                        if v_isSharedCheck_496_ == 0 {
                            v___x_460_ = v___x_457_;
                            v_isShared_461_ = v_isSharedCheck_496_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_458_);
                            leanh::lean_dec(v___x_457_);
                            v___x_460_ = leanh::lean_box(0);
                            v_isShared_461_ = v_isSharedCheck_496_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_456_);
                        v_a_497_ = leanh::lean_ctor_get(v___x_457_, 0);
                        v_isSharedCheck_504_ = (!leanh::lean_is_exclusive(v___x_457_)) as u8;
                        if v_isSharedCheck_504_ == 0 {
                            v___x_499_ = v___x_457_;
                            v_isShared_500_ = v_isSharedCheck_504_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_497_);
                            leanh::lean_dec(v___x_457_);
                            v___x_499_ = leanh::lean_box(0);
                            v_isShared_500_ = v_isSharedCheck_504_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_505_ = leanh::lean_ctor_get(v___x_455_, 0);
                    v_isSharedCheck_512_ = (!leanh::lean_is_exclusive(v___x_455_)) as u8;
                    if v_isSharedCheck_512_ == 0 {
                        v___x_507_ = v___x_455_;
                        v_isShared_508_ = v_isSharedCheck_512_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_505_);
                        leanh::lean_dec(v___x_455_);
                        v___x_507_ = leanh::lean_box(0);
                        v_isShared_508_ = v_isSharedCheck_512_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_kind_451_ == 0 {
                    v___x_494_ = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5;
                    v___y_463_ = v___x_494_;
                    state = 2;
                    continue;
                } else {
                    v___x_495_ = l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6;
                    v___y_463_ = v___x_495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_464_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once),
                    _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0,
                );
                v___x_465_ = lean_int_dec_eq(v_k_454_, v___x_464_);
                if v___x_465_ == 0 {
                    v___x_466_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_456_);
                    v___x_467_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once),
                        _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2,
                    );
                    v___x_468_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_468_, 0, v___x_466_);
                    leanh::lean_ctor_set(v___x_468_, 1, v___x_467_);
                    leanh::lean_inc_ref(v___y_463_);
                    v___x_469_ = l_Lean_stringToMessageData(v___y_463_);
                    v___x_470_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_470_, 0, v___x_468_);
                    leanh::lean_ctor_set(v___x_470_, 1, v___x_469_);
                    v___x_471_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_471_, 0, v___x_470_);
                    leanh::lean_ctor_set(v___x_471_, 1, v___x_467_);
                    v___x_472_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_458_);
                    v___x_473_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_473_, 0, v___x_471_);
                    leanh::lean_ctor_set(v___x_473_, 1, v___x_472_);
                    v___x_474_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once),
                        _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4,
                    );
                    v___x_475_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_475_, 0, v___x_473_);
                    leanh::lean_ctor_set(v___x_475_, 1, v___x_474_);
                    v___x_476_ = l_Int_repr(v_k_454_);
                    v___x_477_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
                    v___x_478_ = l_Lean_MessageData_ofFormat(v___x_477_);
                    v___x_479_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_479_, 0, v___x_475_);
                    leanh::lean_ctor_set(v___x_479_, 1, v___x_478_);
                    if v_isShared_461_ == 0 {
                        leanh::lean_ctor_set(v___x_460_, 0, v___x_479_);
                        v___x_481_ = v___x_460_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
                        v___x_481_ = v_reuseFailAlloc_482_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_483_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_456_);
                    v___x_484_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once),
                        _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2,
                    );
                    v___x_485_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_485_, 0, v___x_483_);
                    leanh::lean_ctor_set(v___x_485_, 1, v___x_484_);
                    leanh::lean_inc_ref(v___y_463_);
                    v___x_486_ = l_Lean_stringToMessageData(v___y_463_);
                    v___x_487_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_487_, 0, v___x_485_);
                    leanh::lean_ctor_set(v___x_487_, 1, v___x_486_);
                    v___x_488_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_488_, 0, v___x_487_);
                    leanh::lean_ctor_set(v___x_488_, 1, v___x_484_);
                    v___x_489_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_458_);
                    v___x_490_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_490_, 0, v___x_488_);
                    leanh::lean_ctor_set(v___x_490_, 1, v___x_489_);
                    if v_isShared_461_ == 0 {
                        leanh::lean_ctor_set(v___x_460_, 0, v___x_490_);
                        v___x_492_ = v___x_460_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
                        v___x_492_ = v_reuseFailAlloc_493_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_481_;
            }
            4 => {
                return v___x_492_;
            }
            5 => {
                if v_isShared_500_ == 0 {
                    v___x_502_ = v___x_499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
                    v___x_502_ = v_reuseFailAlloc_503_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_502_;
            }
            7 => {
                if v_isShared_508_ == 0 {
                    v___x_510_ = v___x_507_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
                    v___x_510_ = v_reuseFailAlloc_511_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(
    mut v_c_513_: *mut leanh::LeanObject,
    mut v_a_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
    mut v_a_522_: *mut leanh::LeanObject,
    mut v_a_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
    mut v_a_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Lean_Meta_Grind_Order_Cnstr_pp(
        v_c_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_,
        v_a_522_, v_a_523_, v_a_524_,
    );
    leanh::lean_dec(v_a_524_);
    leanh::lean_dec_ref(v_a_523_);
    leanh::lean_dec(v_a_522_);
    leanh::lean_dec_ref(v_a_521_);
    leanh::lean_dec(v_a_520_);
    leanh::lean_dec_ref(v_a_519_);
    leanh::lean_dec(v_a_518_);
    leanh::lean_dec_ref(v_a_517_);
    leanh::lean_dec(v_a_516_);
    leanh::lean_dec(v_a_515_);
    leanh::lean_dec(v_a_514_);
    leanh::lean_dec_ref(v_c_513_);
    return v_res_526_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_compare(
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_b_528_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_530_: u8 = 0;
    let mut v_k_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_532_: u8 = 0;
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: u8 = 0;
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: u8 = 0;
    let mut v___x_542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_529_ = leanh::lean_ctor_get(v_a_527_, 0);
                v_strict_530_ = leanh::lean_ctor_get_uint8(
                    v_a_527_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_k_531_ = leanh::lean_ctor_get(v_b_528_, 0);
                v_strict_532_ = leanh::lean_ctor_get_uint8(
                    v_b_528_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_537_ = lean_int_dec_lt(v_k_529_, v_k_531_);
                if v___x_537_ == 0 {
                    v___x_538_ = lean_int_dec_lt(v_k_531_, v_k_529_);
                    if v___x_538_ == 0 {
                        if v_strict_530_ == 0 {
                            if v_strict_532_ == 0 {
                                v___x_539_ = 1;
                                return v___x_539_;
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            if v_strict_532_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_540_ = 1;
                                return v___x_540_;
                            }
                        }
                    } else {
                        v___x_541_ = 2;
                        return v___x_541_;
                    }
                } else {
                    v___x_542_ = 0;
                    return v___x_542_;
                }
            }
            1 => {
                if v_strict_530_ == 0 {
                    v___x_534_ = 2;
                    return v___x_534_;
                } else {
                    if v_strict_532_ == 0 {
                        v___x_535_ = 0;
                        return v___x_535_;
                    } else {
                        v___x_536_ = 2;
                        return v___x_536_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_compare___boxed(
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_b_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_545_: u8 = 0;
    let mut v_r_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_543_, v_b_544_);
    leanh::lean_dec_ref(v_b_544_);
    leanh::lean_dec_ref(v_a_543_);
    v_r_546_ = leanh::lean_box((v_res_545_) as usize);
    return v_r_546_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instLEWeight() -> *mut leanh::LeanObject {
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_549_ = leanh::lean_box(0);
    return v___x_549_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_instLTWeight() -> *mut leanh::LeanObject {
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = leanh::lean_box(0);
    return v___x_550_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instDecidableLEWeight(
    mut v_a_551_: *mut leanh::LeanObject,
    mut v_b_552_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: u8 = 0;
    v___x_553_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_551_, v_b_552_);
    v___x_554_ = 2;
    v___x_555_ = l_instDecidableEqOrdering(v___x_553_, v___x_554_);
    if v___x_555_ == 0 {
        let mut v___x_556_: u8 = 0;
        v___x_556_ = 1;
        return v___x_556_;
    } else {
        let mut v___x_557_: u8 = 0;
        v___x_557_ = 0;
        return v___x_557_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(
    mut v_a_558_: *mut leanh::LeanObject,
    mut v_b_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: u8 = 0;
    let mut v_r_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_558_, v_b_559_);
    leanh::lean_dec_ref(v_b_559_);
    leanh::lean_dec_ref(v_a_558_);
    v_r_561_ = leanh::lean_box((v_res_560_) as usize);
    return v_r_561_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instDecidableLTWeight(
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_b_563_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_564_: u8 = 0;
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    v___x_564_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_562_, v_b_563_);
    v___x_565_ = 0;
    v___x_566_ = l_instDecidableEqOrdering(v___x_564_, v___x_565_);
    return v___x_566_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(
    mut v_a_567_: *mut leanh::LeanObject,
    mut v_b_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_569_: u8 = 0;
    let mut v_r_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_567_, v_b_568_);
    leanh::lean_dec_ref(v_b_568_);
    leanh::lean_dec_ref(v_a_567_);
    v_r_570_ = leanh::lean_box((v_res_569_) as usize);
    return v_r_570_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_add(
    mut v_a_571_: *mut leanh::LeanObject,
    mut v_b_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_574_: u8 = 0;
    let mut v_k_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_576_: u8 = 0;
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_k_573_ = leanh::lean_ctor_get(v_a_571_, 0);
                v_strict_574_ = leanh::lean_ctor_get_uint8(
                    v_a_571_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_k_575_ = leanh::lean_ctor_get(v_b_572_, 0);
                v_strict_576_ = leanh::lean_ctor_get_uint8(
                    v_b_572_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_587_ = (!leanh::lean_is_exclusive(v_b_572_)) as u8;
                if v_isSharedCheck_587_ == 0 {
                    v___x_578_ = v_b_572_;
                    v_isShared_579_ = v_isSharedCheck_587_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_k_575_);
                    leanh::lean_dec(v_b_572_);
                    v___x_578_ = leanh::lean_box(0);
                    v_isShared_579_ = v_isSharedCheck_587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_580_ = lean_int_add(v_k_573_, v_k_575_);
                leanh::lean_dec(v_k_575_);
                if v_strict_574_ == 0 {
                    if v_isShared_579_ == 0 {
                        leanh::lean_ctor_set(v___x_578_, 0, v___x_580_);
                        v___x_582_ = v___x_578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_583_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_583_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_strict_576_,
                        );
                        v___x_582_ = v_reuseFailAlloc_583_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_579_ == 0 {
                        leanh::lean_ctor_set(v___x_578_, 0, v___x_580_);
                        v___x_585_ = v___x_578_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_586_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_580_);
                        v___x_585_ = v_reuseFailAlloc_586_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_582_;
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_585_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_strict_574_,
                );
                return v___x_585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_add___boxed(
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_b_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_588_, v_b_589_);
    leanh::lean_dec_ref(v_a_588_);
    return v_res_590_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_isNeg(
    mut v_a_593_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_595_: u8 = 0;
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    v_k_594_ = leanh::lean_ctor_get(v_a_593_, 0);
    v_strict_595_ = leanh::lean_ctor_get_uint8(
        v_a_593_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v___x_596_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once),
        _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0,
    );
    v___x_597_ = lean_int_dec_lt(v_k_594_, v___x_596_);
    if v___x_597_ == 0 {
        let mut v___x_598_: u8 = 0;
        v___x_598_ = lean_int_dec_eq(v_k_594_, v___x_596_);
        if v___x_598_ == 0 {
            return v___x_598_;
        } else {
            return v_strict_595_;
        }
    } else {
        return v___x_597_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(
    mut v_a_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: u8 = 0;
    let mut v_r_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_599_);
    leanh::lean_dec_ref(v_a_599_);
    v_r_601_ = leanh::lean_box((v_res_600_) as usize);
    return v_r_601_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_isZero(
    mut v_a_602_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_604_: u8 = 0;
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    v_k_603_ = leanh::lean_ctor_get(v_a_602_, 0);
    v_strict_604_ = leanh::lean_ctor_get_uint8(
        v_a_602_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v___x_605_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once),
        _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0,
    );
    v___x_606_ = lean_int_dec_eq(v_k_603_, v___x_605_);
    if v___x_606_ == 0 {
        return v___x_606_;
    } else {
        if v_strict_604_ == 0 {
            return v___x_606_;
        } else {
            let mut v___x_607_: u8 = 0;
            v___x_607_ = 0;
            return v___x_607_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Weight_isZero___boxed(
    mut v_a_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_608_);
    leanh::lean_dec_ref(v_a_608_);
    v_r_610_ = leanh::lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(
    mut v_a_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_strict_613_: u8 = 0;
    v_strict_613_ = leanh::lean_ctor_get_uint8(
        v_a_612_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_strict_613_ == 0 {
        let mut v_k_614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_614_ = leanh::lean_ctor_get(v_a_612_, 0);
        v___x_615_ = l_Int_repr(v_k_614_);
        return v___x_615_;
    } else {
        let mut v_k_616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_616_ = leanh::lean_ctor_get(v_a_612_, 0);
        v___x_617_ = l_Int_repr(v_k_616_);
        v___x_618_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
        v___x_619_ = lean_string_append(v___x_617_, v___x_618_);
        return v___x_619_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_620_);
    leanh::lean_dec_ref(v_a_620_);
    return v_res_621_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0;
    v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
    return v___x_626_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2;
    v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
    return v___x_629_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4;
    v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6;
    v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
    return v___x_635_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_pp(
    mut v_todo_636_: *mut leanh::LeanObject,
    mut v_a_637_: *mut leanh::LeanObject,
    mut v_a_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
    mut v_a_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
    mut v_a_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___y_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_676_: u8 = 0;
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_686_: u8 = 0;
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v_a_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_707_: u8 = 0;
    let mut v_a_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v_e_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_727_: u8 = 0;
    let mut v___y_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_743_: u8 = 0;
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_753_: u8 = 0;
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v_a_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut v_a_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_782_: u8 = 0;
    let mut v_u_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_794_: u8 = 0;
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_807_: u8 = 0;
    let mut v_a_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_811_: u8 = 0;
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_a_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_todo_636_) {
                0 => {
                    v_e_649_ = leanh::lean_ctor_get(v_todo_636_, 1);
                    leanh::lean_inc_ref(v_e_649_);
                    v_u_650_ = leanh::lean_ctor_get(v_todo_636_, 2);
                    leanh::lean_inc(v_u_650_);
                    v_v_651_ = leanh::lean_ctor_get(v_todo_636_, 3);
                    leanh::lean_inc(v_v_651_);
                    v_k_652_ = leanh::lean_ctor_get(v_todo_636_, 4);
                    leanh::lean_inc_ref(v_k_652_);
                    v_k_x27_653_ = leanh::lean_ctor_get(v_todo_636_, 5);
                    leanh::lean_inc_ref(v_k_x27_653_);
                    leanh::lean_dec_ref_known(v_todo_636_, 6);
                    v___x_654_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_u_650_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_,
                        v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                    );
                    leanh::lean_dec(v_u_650_);
                    if leanh::lean_obj_tag(v___x_654_) == 0 {
                        v_a_655_ = leanh::lean_ctor_get(v___x_654_, 0);
                        leanh::lean_inc(v_a_655_);
                        leanh::lean_dec_ref_known(v___x_654_, 1);
                        v___x_656_ = l_Lean_Meta_Grind_Order_getExpr(
                            v_v_651_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_,
                            v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                        );
                        leanh::lean_dec(v_v_651_);
                        if leanh::lean_obj_tag(v___x_656_) == 0 {
                            v_a_657_ = leanh::lean_ctor_get(v___x_656_, 0);
                            v_isSharedCheck_699_ =
                                (!leanh::lean_is_exclusive(v___x_656_)) as u8;
                            if v_isSharedCheck_699_ == 0 {
                                v___x_659_ = v___x_656_;
                                v_isShared_660_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_657_);
                                leanh::lean_dec(v___x_656_);
                                v___x_659_ = leanh::lean_box(0);
                                v_isShared_660_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_655_);
                            leanh::lean_dec_ref(v_k_x27_653_);
                            leanh::lean_dec_ref(v_k_652_);
                            leanh::lean_dec_ref(v_e_649_);
                            v_a_700_ = leanh::lean_ctor_get(v___x_656_, 0);
                            v_isSharedCheck_707_ =
                                (!leanh::lean_is_exclusive(v___x_656_)) as u8;
                            if v_isSharedCheck_707_ == 0 {
                                v___x_702_ = v___x_656_;
                                v_isShared_703_ = v_isSharedCheck_707_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_700_);
                                leanh::lean_dec(v___x_656_);
                                v___x_702_ = leanh::lean_box(0);
                                v_isShared_703_ = v_isSharedCheck_707_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_x27_653_);
                        leanh::lean_dec_ref(v_k_652_);
                        leanh::lean_dec(v_v_651_);
                        leanh::lean_dec_ref(v_e_649_);
                        v_a_708_ = leanh::lean_ctor_get(v___x_654_, 0);
                        v_isSharedCheck_715_ = (!leanh::lean_is_exclusive(v___x_654_)) as u8;
                        if v_isSharedCheck_715_ == 0 {
                            v___x_710_ = v___x_654_;
                            v_isShared_711_ = v_isSharedCheck_715_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_708_);
                            leanh::lean_dec(v___x_654_);
                            v___x_710_ = leanh::lean_box(0);
                            v_isShared_711_ = v_isSharedCheck_715_;
                            state = 7;
                            continue;
                        }
                    }
                }
                1 => {
                    v_e_716_ = leanh::lean_ctor_get(v_todo_636_, 1);
                    leanh::lean_inc_ref(v_e_716_);
                    v_u_717_ = leanh::lean_ctor_get(v_todo_636_, 2);
                    leanh::lean_inc(v_u_717_);
                    v_v_718_ = leanh::lean_ctor_get(v_todo_636_, 3);
                    leanh::lean_inc(v_v_718_);
                    v_k_719_ = leanh::lean_ctor_get(v_todo_636_, 4);
                    leanh::lean_inc_ref(v_k_719_);
                    v_k_x27_720_ = leanh::lean_ctor_get(v_todo_636_, 5);
                    leanh::lean_inc_ref(v_k_x27_720_);
                    leanh::lean_dec_ref_known(v_todo_636_, 6);
                    v___x_721_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_u_717_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_,
                        v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                    );
                    leanh::lean_dec(v_u_717_);
                    if leanh::lean_obj_tag(v___x_721_) == 0 {
                        v_a_722_ = leanh::lean_ctor_get(v___x_721_, 0);
                        leanh::lean_inc(v_a_722_);
                        leanh::lean_dec_ref_known(v___x_721_, 1);
                        v___x_723_ = l_Lean_Meta_Grind_Order_getExpr(
                            v_v_718_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_,
                            v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                        );
                        leanh::lean_dec(v_v_718_);
                        if leanh::lean_obj_tag(v___x_723_) == 0 {
                            v_a_724_ = leanh::lean_ctor_get(v___x_723_, 0);
                            v_isSharedCheck_766_ =
                                (!leanh::lean_is_exclusive(v___x_723_)) as u8;
                            if v_isSharedCheck_766_ == 0 {
                                v___x_726_ = v___x_723_;
                                v_isShared_727_ = v_isSharedCheck_766_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_724_);
                                leanh::lean_dec(v___x_723_);
                                v___x_726_ = leanh::lean_box(0);
                                v_isShared_727_ = v_isSharedCheck_766_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_722_);
                            leanh::lean_dec_ref(v_k_x27_720_);
                            leanh::lean_dec_ref(v_k_719_);
                            leanh::lean_dec_ref(v_e_716_);
                            v_a_767_ = leanh::lean_ctor_get(v___x_723_, 0);
                            v_isSharedCheck_774_ =
                                (!leanh::lean_is_exclusive(v___x_723_)) as u8;
                            if v_isSharedCheck_774_ == 0 {
                                v___x_769_ = v___x_723_;
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_767_);
                                leanh::lean_dec(v___x_723_);
                                v___x_769_ = leanh::lean_box(0);
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_x27_720_);
                        leanh::lean_dec_ref(v_k_719_);
                        leanh::lean_dec(v_v_718_);
                        leanh::lean_dec_ref(v_e_716_);
                        v_a_775_ = leanh::lean_ctor_get(v___x_721_, 0);
                        v_isSharedCheck_782_ = (!leanh::lean_is_exclusive(v___x_721_)) as u8;
                        if v_isSharedCheck_782_ == 0 {
                            v___x_777_ = v___x_721_;
                            v_isShared_778_ = v_isSharedCheck_782_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_775_);
                            leanh::lean_dec(v___x_721_);
                            v___x_777_ = leanh::lean_box(0);
                            v_isShared_778_ = v_isSharedCheck_782_;
                            state = 15;
                            continue;
                        }
                    }
                }
                _ => {
                    v_u_783_ = leanh::lean_ctor_get(v_todo_636_, 0);
                    v_v_784_ = leanh::lean_ctor_get(v_todo_636_, 1);
                    v_isSharedCheck_824_ = (!leanh::lean_is_exclusive(v_todo_636_)) as u8;
                    if v_isSharedCheck_824_ == 0 {
                        v___x_786_ = v_todo_636_;
                        v_isShared_787_ = v_isSharedCheck_824_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_784_);
                        leanh::lean_inc(v_u_783_);
                        leanh::lean_dec(v_todo_636_);
                        v___x_786_ = leanh::lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_824_;
                        state = 17;
                        continue;
                    }
                }
            },
            1 => {
                v___x_670_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1,
                );
                v___x_671_ = l_Lean_MessageData_ofExpr(v_e_649_);
                v___x_672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_672_, 0, v___x_670_);
                leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
                v___x_673_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3,
                );
                v___x_674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_674_, 0, v___x_672_);
                leanh::lean_ctor_set(v___x_674_, 1, v___x_673_);
                v_k_675_ = leanh::lean_ctor_get(v_k_652_, 0);
                leanh::lean_inc(v_k_675_);
                v_strict_676_ = leanh::lean_ctor_get_uint8(
                    v_k_652_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_k_652_);
                v___x_677_ = l_Lean_MessageData_ofExpr(v_a_655_);
                v___x_678_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_678_, 0, v___x_674_);
                leanh::lean_ctor_set(v___x_678_, 1, v___x_677_);
                v___x_679_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_679_, 0, v___x_678_);
                leanh::lean_ctor_set(v___x_679_, 1, v___x_673_);
                v___x_680_ = l_Lean_MessageData_ofExpr(v_a_657_);
                v___x_681_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_681_, 0, v___x_679_);
                leanh::lean_ctor_set(v___x_681_, 1, v___x_680_);
                v___x_682_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_682_, 0, v___x_681_);
                leanh::lean_ctor_set(v___x_682_, 1, v___x_673_);
                if v_strict_676_ == 0 {
                    v___x_695_ = l_Int_repr(v_k_675_);
                    leanh::lean_dec(v_k_675_);
                    v___y_684_ = v___x_695_;
                    state = 4;
                    continue;
                } else {
                    v___x_696_ = l_Int_repr(v_k_675_);
                    leanh::lean_dec(v_k_675_);
                    v___x_697_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
                    v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
                    v___y_684_ = v___x_698_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_664_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_664_, 0, v___y_663_);
                v___x_665_ = l_Lean_MessageData_ofFormat(v___x_664_);
                v___x_666_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_666_, 0, v___y_662_);
                leanh::lean_ctor_set(v___x_666_, 1, v___x_665_);
                if v_isShared_660_ == 0 {
                    leanh::lean_ctor_set(v___x_659_, 0, v___x_666_);
                    v___x_668_ = v___x_659_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
                    v___x_668_ = v_reuseFailAlloc_669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_668_;
            }
            4 => {
                v_k_685_ = leanh::lean_ctor_get(v_k_x27_653_, 0);
                leanh::lean_inc(v_k_685_);
                v_strict_686_ = leanh::lean_ctor_get_uint8(
                    v_k_x27_653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_k_x27_653_);
                v___x_687_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_687_, 0, v___y_684_);
                v___x_688_ = l_Lean_MessageData_ofFormat(v___x_687_);
                v___x_689_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_689_, 0, v___x_682_);
                leanh::lean_ctor_set(v___x_689_, 1, v___x_688_);
                v___x_690_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_690_, 0, v___x_689_);
                leanh::lean_ctor_set(v___x_690_, 1, v___x_673_);
                if v_strict_686_ == 0 {
                    v___x_691_ = l_Int_repr(v_k_685_);
                    leanh::lean_dec(v_k_685_);
                    v___y_662_ = v___x_690_;
                    v___y_663_ = v___x_691_;
                    state = 2;
                    continue;
                } else {
                    v___x_692_ = l_Int_repr(v_k_685_);
                    leanh::lean_dec(v_k_685_);
                    v___x_693_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
                    v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
                    v___y_662_ = v___x_690_;
                    v___y_663_ = v___x_694_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_703_ == 0 {
                    v___x_705_ = v___x_702_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
                    v___x_705_ = v_reuseFailAlloc_706_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_705_;
            }
            7 => {
                if v_isShared_711_ == 0 {
                    v___x_713_ = v___x_710_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_713_;
            }
            9 => {
                v___x_737_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5,
                );
                v___x_738_ = l_Lean_MessageData_ofExpr(v_e_716_);
                v___x_739_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_739_, 0, v___x_737_);
                leanh::lean_ctor_set(v___x_739_, 1, v___x_738_);
                v___x_740_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3,
                );
                v___x_741_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_741_, 0, v___x_739_);
                leanh::lean_ctor_set(v___x_741_, 1, v___x_740_);
                v_k_742_ = leanh::lean_ctor_get(v_k_719_, 0);
                leanh::lean_inc(v_k_742_);
                v_strict_743_ = leanh::lean_ctor_get_uint8(
                    v_k_719_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_k_719_);
                v___x_744_ = l_Lean_MessageData_ofExpr(v_a_722_);
                v___x_745_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_745_, 0, v___x_741_);
                leanh::lean_ctor_set(v___x_745_, 1, v___x_744_);
                v___x_746_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_746_, 0, v___x_745_);
                leanh::lean_ctor_set(v___x_746_, 1, v___x_740_);
                v___x_747_ = l_Lean_MessageData_ofExpr(v_a_724_);
                v___x_748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_748_, 0, v___x_746_);
                leanh::lean_ctor_set(v___x_748_, 1, v___x_747_);
                v___x_749_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
                leanh::lean_ctor_set(v___x_749_, 1, v___x_740_);
                if v_strict_743_ == 0 {
                    v___x_762_ = l_Int_repr(v_k_742_);
                    leanh::lean_dec(v_k_742_);
                    v___y_751_ = v___x_762_;
                    state = 12;
                    continue;
                } else {
                    v___x_763_ = l_Int_repr(v_k_742_);
                    leanh::lean_dec(v_k_742_);
                    v___x_764_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
                    v___x_765_ = lean_string_append(v___x_763_, v___x_764_);
                    v___y_751_ = v___x_765_;
                    state = 12;
                    continue;
                }
            }
            10 => {
                v___x_731_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_731_, 0, v___y_730_);
                v___x_732_ = l_Lean_MessageData_ofFormat(v___x_731_);
                v___x_733_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_733_, 0, v___y_729_);
                leanh::lean_ctor_set(v___x_733_, 1, v___x_732_);
                if v_isShared_727_ == 0 {
                    leanh::lean_ctor_set(v___x_726_, 0, v___x_733_);
                    v___x_735_ = v___x_726_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
                    v___x_735_ = v_reuseFailAlloc_736_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_735_;
            }
            12 => {
                v_k_752_ = leanh::lean_ctor_get(v_k_x27_720_, 0);
                leanh::lean_inc(v_k_752_);
                v_strict_753_ = leanh::lean_ctor_get_uint8(
                    v_k_x27_720_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_k_x27_720_);
                v___x_754_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_754_, 0, v___y_751_);
                v___x_755_ = l_Lean_MessageData_ofFormat(v___x_754_);
                v___x_756_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_756_, 0, v___x_749_);
                leanh::lean_ctor_set(v___x_756_, 1, v___x_755_);
                v___x_757_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_757_, 0, v___x_756_);
                leanh::lean_ctor_set(v___x_757_, 1, v___x_740_);
                if v_strict_753_ == 0 {
                    v___x_758_ = l_Int_repr(v_k_752_);
                    leanh::lean_dec(v_k_752_);
                    v___y_729_ = v___x_757_;
                    v___y_730_ = v___x_758_;
                    state = 10;
                    continue;
                } else {
                    v___x_759_ = l_Int_repr(v_k_752_);
                    leanh::lean_dec(v_k_752_);
                    v___x_760_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0;
                    v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
                    v___y_729_ = v___x_757_;
                    v___y_730_ = v___x_761_;
                    state = 10;
                    continue;
                }
            }
            13 => {
                if v_isShared_770_ == 0 {
                    v___x_772_ = v___x_769_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
                    v___x_772_ = v_reuseFailAlloc_773_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_772_;
            }
            15 => {
                if v_isShared_778_ == 0 {
                    v___x_780_ = v___x_777_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
                    v___x_780_ = v_reuseFailAlloc_781_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_780_;
            }
            17 => {
                v___x_788_ = l_Lean_Meta_Grind_Order_getExpr(
                    v_u_783_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_,
                    v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                );
                leanh::lean_dec(v_u_783_);
                if leanh::lean_obj_tag(v___x_788_) == 0 {
                    v_a_789_ = leanh::lean_ctor_get(v___x_788_, 0);
                    leanh::lean_inc(v_a_789_);
                    leanh::lean_dec_ref_known(v___x_788_, 1);
                    v___x_790_ = l_Lean_Meta_Grind_Order_getExpr(
                        v_v_784_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_,
                        v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
                    );
                    leanh::lean_dec(v_v_784_);
                    if leanh::lean_obj_tag(v___x_790_) == 0 {
                        v_a_791_ = leanh::lean_ctor_get(v___x_790_, 0);
                        v_isSharedCheck_807_ = (!leanh::lean_is_exclusive(v___x_790_)) as u8;
                        if v_isSharedCheck_807_ == 0 {
                            v___x_793_ = v___x_790_;
                            v_isShared_794_ = v_isSharedCheck_807_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_791_);
                            leanh::lean_dec(v___x_790_);
                            v___x_793_ = leanh::lean_box(0);
                            v_isShared_794_ = v_isSharedCheck_807_;
                            state = 18;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_789_);
                        leanh::lean_del_object(v___x_786_);
                        v_a_808_ = leanh::lean_ctor_get(v___x_790_, 0);
                        v_isSharedCheck_815_ = (!leanh::lean_is_exclusive(v___x_790_)) as u8;
                        if v_isSharedCheck_815_ == 0 {
                            v___x_810_ = v___x_790_;
                            v_isShared_811_ = v_isSharedCheck_815_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_808_);
                            leanh::lean_dec(v___x_790_);
                            v___x_810_ = leanh::lean_box(0);
                            v_isShared_811_ = v_isSharedCheck_815_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_786_);
                    leanh::lean_dec(v_v_784_);
                    v_a_816_ = leanh::lean_ctor_get(v___x_788_, 0);
                    v_isSharedCheck_823_ = (!leanh::lean_is_exclusive(v___x_788_)) as u8;
                    if v_isSharedCheck_823_ == 0 {
                        v___x_818_ = v___x_788_;
                        v_isShared_819_ = v_isSharedCheck_823_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_816_);
                        leanh::lean_dec(v___x_788_);
                        v___x_818_ = leanh::lean_box(0);
                        v_isShared_819_ = v_isSharedCheck_823_;
                        state = 23;
                        continue;
                    }
                }
            }
            18 => {
                v___x_795_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7,
                );
                v___x_796_ = l_Lean_MessageData_ofExpr(v_a_789_);
                if v_isShared_787_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_786_, 7);
                    leanh::lean_ctor_set(v___x_786_, 1, v___x_796_);
                    leanh::lean_ctor_set(v___x_786_, 0, v___x_795_);
                    v___x_798_ = v___x_786_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_806_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_796_);
                    v___x_798_ = v_reuseFailAlloc_806_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_799_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3,
                );
                v___x_800_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_800_, 0, v___x_798_);
                leanh::lean_ctor_set(v___x_800_, 1, v___x_799_);
                v___x_801_ = l_Lean_MessageData_ofExpr(v_a_791_);
                v___x_802_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_802_, 0, v___x_800_);
                leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
                if v_isShared_794_ == 0 {
                    leanh::lean_ctor_set(v___x_793_, 0, v___x_802_);
                    v___x_804_ = v___x_793_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
                    v___x_804_ = v_reuseFailAlloc_805_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_804_;
            }
            21 => {
                if v_isShared_811_ == 0 {
                    v___x_813_ = v___x_810_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
                    v___x_813_ = v_reuseFailAlloc_814_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_813_;
            }
            23 => {
                if v_isShared_819_ == 0 {
                    v___x_821_ = v___x_818_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
                    v___x_821_ = v_reuseFailAlloc_822_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(
    mut v_todo_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
    mut v_a_827_: *mut leanh::LeanObject,
    mut v_a_828_: *mut leanh::LeanObject,
    mut v_a_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
    mut v_a_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
    mut v_a_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(
        v_todo_825_,
        v_a_826_,
        v_a_827_,
        v_a_828_,
        v_a_829_,
        v_a_830_,
        v_a_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
        v_a_835_,
        v_a_836_,
    );
    leanh::lean_dec(v_a_836_);
    leanh::lean_dec_ref(v_a_835_);
    leanh::lean_dec(v_a_834_);
    leanh::lean_dec_ref(v_a_833_);
    leanh::lean_dec(v_a_832_);
    leanh::lean_dec_ref(v_a_831_);
    leanh::lean_dec(v_a_830_);
    leanh::lean_dec_ref(v_a_829_);
    leanh::lean_dec(v_a_828_);
    leanh::lean_dec(v_a_827_);
    leanh::lean_dec(v_a_826_);
    return v_res_838_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(
    mut v_c_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_840_: u8 = 0;
    v_kind_840_ = leanh::lean_ctor_get_uint8(
        v_c_839_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
    );
    if v_kind_840_ == 0 {
        let mut v_k_841_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_842_: u8 = 0;
        let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_841_ = leanh::lean_ctor_get(v_c_839_, 2);
        v___x_842_ = 0;
        leanh::lean_inc(v_k_841_);
        v___x_843_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_843_, 0, v_k_841_);
        leanh::lean_ctor_set_uint8(
            v___x_843_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_842_,
        );
        return v___x_843_;
    } else {
        let mut v_k_844_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_845_: u8 = 0;
        let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_844_ = leanh::lean_ctor_get(v_c_839_, 2);
        v___x_845_ = 1;
        leanh::lean_inc(v_k_844_);
        v___x_846_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_846_, 0, v_k_844_);
        leanh::lean_ctor_set_uint8(
            v___x_846_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_845_,
        );
        return v___x_846_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(
    mut v_c_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_847_);
    leanh::lean_dec_ref(v_c_847_);
    return v_res_848_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_getWeight(
    mut v_00_u03b1_849_: *mut leanh::LeanObject,
    mut v_c_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_850_);
    return v___x_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(
    mut v_00_u03b1_852_: *mut leanh::LeanObject,
    mut v_c_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_852_, v_c_853_);
    leanh::lean_dec_ref(v_c_853_);
    return v_res_854_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Order_instLEWeight = _init_l_Lean_Meta_Grind_Order_instLEWeight();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instLEWeight);
    l_Lean_Meta_Grind_Order_instLTWeight = _init_l_Lean_Meta_Grind_Order_instLTWeight();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Order_instLTWeight);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Order_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Order_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
}