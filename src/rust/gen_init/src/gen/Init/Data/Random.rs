// Lean compiler output
// Module: Init.Data.Random
// Imports: Init.System.IO Init.Data.ByteArray.Extra
use crate::ffi::{
    lean_int_add, lean_int_dec_lt, lean_int_mul, lean_int_sub, lean_io_get_random_bytes,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul,
    lean_nat_sub, lean_nat_to_int, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_string_length, lean_uint64_to_nat,
};
use crate::r#gen::Init::Data::ByteArray::Extra::{
    initialize_Init_Data_ByteArray_Extra, l_ByteArray_toUInt64LE_x21,
    runtime_initialize_Init_Data_ByteArray_Extra,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
static mut l_instInhabitedStdGen___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedStdGen___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedStdGen: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_stdRange___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((2147483562 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_stdRange___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_stdRange___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_stdRange: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_stdRange___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprStdGen___lam__0___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [226, 159, 168, 0],
    };
static mut l_instReprStdGen___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprStdGen___lam__0___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
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
static mut l_instReprStdGen___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprStdGen___lam__0___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprStdGen___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_instReprStdGen___lam__0___closed__3_value: leanh::LeanStringObject<4> =
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
        m_data: [226, 159, 169, 0],
    };
static mut l_instReprStdGen___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_instReprStdGen___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprStdGen___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instReprStdGen___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprStdGen___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprStdGen___lam__0___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprStdGen___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_instReprStdGen___lam__0___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprStdGen___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_instReprStdGen___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprStdGen___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprStdGen___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprStdGen: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprStdGen___closed__0_value) as *mut leanh::LeanObject;
static mut l_stdNext___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_stdNext___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_stdNext___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instRandomGenStdGen___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instRandomGenStdGen___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instRandomGenStdGen___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instRandomGenStdGen___closed__0_value) as *mut leanh::LeanObject;
pub static l_instRandomGenStdGen___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_stdNext as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instRandomGenStdGen___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instRandomGenStdGen___closed__1_value) as *mut leanh::LeanObject;
pub static l_instRandomGenStdGen___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_stdSplit as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instRandomGenStdGen___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instRandomGenStdGen___closed__2_value) as *mut leanh::LeanObject;
pub static l_instRandomGenStdGen___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instRandomGenStdGen___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instRandomGenStdGen___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instRandomGenStdGen___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instRandomGenStdGen___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instRandomGenStdGen___closed__3_value) as *mut leanh::LeanObject;
pub static mut l_instRandomGenStdGen: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instRandomGenStdGen___closed__3_value) as *mut leanh::LeanObject;
pub static mut l_IO_stdGenRef: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_mkStdGen(
    mut v_s_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s1_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = leanh::lean_unsigned_to_nat(2147483562);
    v_q_434_ = lean_nat_div(v_s_432_, v___x_433_);
    v_s1_435_ = lean_nat_mod(v_s_432_, v___x_433_);
    v___x_436_ = leanh::lean_unsigned_to_nat(2147483398);
    v_s2_437_ = lean_nat_mod(v_q_434_, v___x_436_);
    leanh::lean_dec(v_q_434_);
    v___x_438_ = leanh::lean_unsigned_to_nat(1);
    v___x_439_ = lean_nat_add(v_s1_435_, v___x_438_);
    leanh::lean_dec(v_s1_435_);
    v___x_440_ = lean_nat_add(v_s2_437_, v___x_438_);
    leanh::lean_dec(v_s2_437_);
    v___x_441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_441_, 0, v___x_439_);
    leanh::lean_ctor_set(v___x_441_, 1, v___x_440_);
    return v___x_441_;
}
pub unsafe fn l_mkStdGen___boxed(
    mut v_s_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_mkStdGen(v_s_442_);
    leanh::lean_dec(v_s_442_);
    return v_res_443_;
}
pub unsafe fn _init_l_instInhabitedStdGen___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = leanh::lean_unsigned_to_nat(0);
    v___x_445_ = l_mkStdGen(v___x_444_);
    return v___x_445_;
}
pub unsafe fn _init_l_instInhabitedStdGen() -> *mut leanh::LeanObject {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instInhabitedStdGen___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedStdGen___closed__0_once),
        _init_l_instInhabitedStdGen___closed__0,
    );
    return v___x_446_;
}
pub unsafe fn _init_l_instReprStdGen___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_instReprStdGen___lam__0___closed__0;
    v___x_457_ = lean_string_length(v___x_456_);
    return v___x_457_;
}
pub unsafe fn _init_l_instReprStdGen___lam__0___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprStdGen___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_instReprStdGen___lam__0___closed__4_once),
        _init_l_instReprStdGen___lam__0___closed__4,
    );
    v___x_459_ = lean_nat_to_int(v___x_458_);
    return v___x_459_;
}
pub unsafe fn l_instReprStdGen___lam__0(
    mut v_x_464_: *mut leanh::LeanObject,
    mut v_x_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s1_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: u8 = 0;
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s1_466_ = leanh::lean_ctor_get(v_x_464_, 0);
                v_s2_467_ = leanh::lean_ctor_get(v_x_464_, 1);
                v_isSharedCheck_488_ = (!leanh::lean_is_exclusive(v_x_464_)) as u8;
                if v_isSharedCheck_488_ == 0 {
                    v___x_469_ = v_x_464_;
                    v_isShared_470_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_s2_467_);
                    leanh::lean_inc(v_s1_466_);
                    leanh::lean_dec(v_x_464_);
                    v___x_469_ = leanh::lean_box(0);
                    v_isShared_470_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_471_ = l_Nat_reprFast(v_s1_466_);
                v___x_472_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_472_, 0, v___x_471_);
                v___x_473_ = l_instReprStdGen___lam__0___closed__2;
                if v_isShared_470_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_469_, 5);
                    leanh::lean_ctor_set(v___x_469_, 1, v___x_473_);
                    leanh::lean_ctor_set(v___x_469_, 0, v___x_472_);
                    v___x_475_ = v___x_469_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_473_);
                    v___x_475_ = v_reuseFailAlloc_487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_476_ = l_Nat_reprFast(v_s2_467_);
                v___x_477_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
                v___x_478_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_478_, 0, v___x_475_);
                leanh::lean_ctor_set(v___x_478_, 1, v___x_477_);
                v___x_479_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_instReprStdGen___lam__0___closed__5),
                    core::ptr::addr_of_mut!(l_instReprStdGen___lam__0___closed__5_once),
                    _init_l_instReprStdGen___lam__0___closed__5,
                );
                v___x_480_ = l_instReprStdGen___lam__0___closed__6;
                v___x_481_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_481_, 0, v___x_480_);
                leanh::lean_ctor_set(v___x_481_, 1, v___x_478_);
                v___x_482_ = l_instReprStdGen___lam__0___closed__7;
                v___x_483_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_483_, 0, v___x_481_);
                leanh::lean_ctor_set(v___x_483_, 1, v___x_482_);
                v___x_484_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_484_, 0, v___x_479_);
                leanh::lean_ctor_set(v___x_484_, 1, v___x_483_);
                v___x_485_ = 0;
                v___x_486_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_486_, 0, v___x_484_);
                leanh::lean_ctor_set_uint8(
                    v___x_486_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_485_,
                );
                return v___x_486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprStdGen___lam__0___boxed(
    mut v_x_489_: *mut leanh::LeanObject,
    mut v_x_490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_491_ = l_instReprStdGen___lam__0(v_x_489_, v_x_490_);
    leanh::lean_dec(v_x_490_);
    return v_res_491_;
}
pub unsafe fn _init_l_stdNext___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = leanh::lean_unsigned_to_nat(1);
    v___x_495_ = lean_nat_to_int(v___x_494_);
    return v___x_495_;
}
pub unsafe fn _init_l_stdNext___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = leanh::lean_unsigned_to_nat(2147483562);
    v___x_497_ = lean_nat_to_int(v___x_496_);
    return v___x_497_;
}
pub unsafe fn _init_l_stdNext___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = leanh::lean_unsigned_to_nat(40014);
    v___x_499_ = lean_nat_to_int(v___x_498_);
    return v___x_499_;
}
pub unsafe fn _init_l_stdNext___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = leanh::lean_unsigned_to_nat(53668);
    v___x_501_ = lean_nat_to_int(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l_stdNext___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = leanh::lean_unsigned_to_nat(12211);
    v___x_503_ = lean_nat_to_int(v___x_502_);
    return v___x_503_;
}
pub unsafe fn _init_l_stdNext___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = leanh::lean_unsigned_to_nat(0);
    v___x_505_ = lean_nat_to_int(v___x_504_);
    return v___x_505_;
}
pub unsafe fn _init_l_stdNext___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = leanh::lean_unsigned_to_nat(40692);
    v___x_507_ = lean_nat_to_int(v___x_506_);
    return v___x_507_;
}
pub unsafe fn _init_l_stdNext___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ = leanh::lean_unsigned_to_nat(52774);
    v___x_509_ = lean_nat_to_int(v___x_508_);
    return v___x_509_;
}
pub unsafe fn _init_l_stdNext___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = leanh::lean_unsigned_to_nat(3791);
    v___x_511_ = lean_nat_to_int(v___x_510_);
    return v___x_511_;
}
pub unsafe fn _init_l_stdNext___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = leanh::lean_unsigned_to_nat(2147483399);
    v___x_513_ = lean_nat_to_int(v___x_512_);
    return v___x_513_;
}
pub unsafe fn _init_l_stdNext___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = leanh::lean_unsigned_to_nat(2147483563);
    v___x_515_ = lean_nat_to_int(v___x_514_);
    return v___x_515_;
}
pub unsafe fn l_stdNext(
    mut v_x_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u8 = 0;
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s1_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s1_x27_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_x27_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s1_537_ = leanh::lean_ctor_get(v_x_516_, 0);
                leanh::lean_inc(v_s1_537_);
                v_s2_538_ = leanh::lean_ctor_get(v_x_516_, 1);
                leanh::lean_inc(v_s2_538_);
                leanh::lean_dec_ref(v_x_516_);
                v___x_539_ = leanh::lean_unsigned_to_nat(53668);
                v___x_540_ = lean_nat_div(v_s1_537_, v___x_539_);
                v_k_541_ = lean_nat_to_int(v___x_540_);
                v___x_542_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__2),
                    core::ptr::addr_of_mut!(l_stdNext___closed__2_once),
                    _init_l_stdNext___closed__2,
                );
                v___x_543_ = lean_nat_to_int(v_s1_537_);
                v___x_544_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__3),
                    core::ptr::addr_of_mut!(l_stdNext___closed__3_once),
                    _init_l_stdNext___closed__3,
                );
                v___x_545_ = lean_int_mul(v_k_541_, v___x_544_);
                v___x_546_ = lean_int_sub(v___x_543_, v___x_545_);
                leanh::lean_dec(v___x_545_);
                leanh::lean_dec(v___x_543_);
                v___x_547_ = lean_int_mul(v___x_542_, v___x_546_);
                leanh::lean_dec(v___x_546_);
                v___x_548_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__4),
                    core::ptr::addr_of_mut!(l_stdNext___closed__4_once),
                    _init_l_stdNext___closed__4,
                );
                v___x_549_ = lean_int_mul(v_k_541_, v___x_548_);
                leanh::lean_dec(v_k_541_);
                v_s1_x27_550_ = lean_int_sub(v___x_547_, v___x_549_);
                leanh::lean_dec(v___x_549_);
                leanh::lean_dec(v___x_547_);
                v___x_551_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__5),
                    core::ptr::addr_of_mut!(l_stdNext___closed__5_once),
                    _init_l_stdNext___closed__5,
                );
                v___x_571_ = lean_int_dec_lt(v_s1_x27_550_, v___x_551_);
                if v___x_571_ == 0 {
                    v___x_572_ = l_Int_toNat(v_s1_x27_550_);
                    leanh::lean_dec(v_s1_x27_550_);
                    v___y_553_ = v___x_572_;
                    state = 3;
                    continue;
                } else {
                    v___x_573_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_stdNext___closed__10),
                        core::ptr::addr_of_mut!(l_stdNext___closed__10_once),
                        _init_l_stdNext___closed__10,
                    );
                    v___x_574_ = lean_int_add(v_s1_x27_550_, v___x_573_);
                    leanh::lean_dec(v_s1_x27_550_);
                    v___x_575_ = l_Int_toNat(v___x_574_);
                    leanh::lean_dec(v___x_574_);
                    v___y_553_ = v___x_575_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_521_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_521_, 0, v___y_519_);
                leanh::lean_ctor_set(v___x_521_, 1, v___y_518_);
                v___x_522_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_522_, 0, v___y_520_);
                leanh::lean_ctor_set(v___x_522_, 1, v___x_521_);
                return v___x_522_;
            }
            2 => {
                leanh::lean_inc(v___y_524_);
                v___x_526_ = lean_nat_to_int(v___y_524_);
                leanh::lean_inc(v___y_525_);
                v___x_527_ = lean_nat_to_int(v___y_525_);
                v_z_528_ = lean_int_sub(v___x_526_, v___x_527_);
                leanh::lean_dec(v___x_527_);
                leanh::lean_dec(v___x_526_);
                v___x_529_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__0),
                    core::ptr::addr_of_mut!(l_stdNext___closed__0_once),
                    _init_l_stdNext___closed__0,
                );
                v___x_530_ = lean_int_dec_lt(v_z_528_, v___x_529_);
                if v___x_530_ == 0 {
                    v___x_531_ = l_Int_toNat(v_z_528_);
                    leanh::lean_dec(v_z_528_);
                    v___x_532_ = leanh::lean_unsigned_to_nat(2147483562);
                    v___x_533_ = lean_nat_mod(v___x_531_, v___x_532_);
                    leanh::lean_dec(v___x_531_);
                    v___y_518_ = v___y_525_;
                    v___y_519_ = v___y_524_;
                    v___y_520_ = v___x_533_;
                    state = 1;
                    continue;
                } else {
                    v___x_534_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_stdNext___closed__1),
                        core::ptr::addr_of_mut!(l_stdNext___closed__1_once),
                        _init_l_stdNext___closed__1,
                    );
                    v___x_535_ = lean_int_add(v_z_528_, v___x_534_);
                    leanh::lean_dec(v_z_528_);
                    v___x_536_ = l_Int_toNat(v___x_535_);
                    leanh::lean_dec(v___x_535_);
                    v___y_518_ = v___y_525_;
                    v___y_519_ = v___y_524_;
                    v___y_520_ = v___x_536_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_554_ = leanh::lean_unsigned_to_nat(52774);
                v___x_555_ = lean_nat_div(v_s2_538_, v___x_554_);
                v_k_x27_556_ = lean_nat_to_int(v___x_555_);
                v___x_557_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__6),
                    core::ptr::addr_of_mut!(l_stdNext___closed__6_once),
                    _init_l_stdNext___closed__6,
                );
                v___x_558_ = lean_nat_to_int(v_s2_538_);
                v___x_559_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__7),
                    core::ptr::addr_of_mut!(l_stdNext___closed__7_once),
                    _init_l_stdNext___closed__7,
                );
                v___x_560_ = lean_int_mul(v_k_x27_556_, v___x_559_);
                v___x_561_ = lean_int_sub(v___x_558_, v___x_560_);
                leanh::lean_dec(v___x_560_);
                leanh::lean_dec(v___x_558_);
                v___x_562_ = lean_int_mul(v___x_557_, v___x_561_);
                leanh::lean_dec(v___x_561_);
                v___x_563_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_stdNext___closed__8),
                    core::ptr::addr_of_mut!(l_stdNext___closed__8_once),
                    _init_l_stdNext___closed__8,
                );
                v___x_564_ = lean_int_mul(v_k_x27_556_, v___x_563_);
                leanh::lean_dec(v_k_x27_556_);
                v_s2_x27_565_ = lean_int_sub(v___x_562_, v___x_564_);
                leanh::lean_dec(v___x_564_);
                leanh::lean_dec(v___x_562_);
                v___x_566_ = lean_int_dec_lt(v_s2_x27_565_, v___x_551_);
                if v___x_566_ == 0 {
                    v___x_567_ = l_Int_toNat(v_s2_x27_565_);
                    leanh::lean_dec(v_s2_x27_565_);
                    v___y_524_ = v___y_553_;
                    v___y_525_ = v___x_567_;
                    state = 2;
                    continue;
                } else {
                    v___x_568_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_stdNext___closed__9),
                        core::ptr::addr_of_mut!(l_stdNext___closed__9_once),
                        _init_l_stdNext___closed__9,
                    );
                    v___x_569_ = lean_int_add(v_s2_x27_565_, v___x_568_);
                    leanh::lean_dec(v_s2_x27_565_);
                    v___x_570_ = l_Int_toNat(v___x_569_);
                    leanh::lean_dec(v___x_569_);
                    v___y_524_ = v___y_553_;
                    v___y_525_ = v___x_570_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_stdSplit(
    mut v_x_576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v_s1_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_leftG_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightG_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_unused_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s1_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s1_600_ = leanh::lean_ctor_get(v_x_576_, 0);
                v_s2_601_ = leanh::lean_ctor_get(v_x_576_, 1);
                v___x_608_ = leanh::lean_unsigned_to_nat(2147483562);
                v___x_609_ = lean_nat_dec_eq(v_s1_600_, v___x_608_);
                if v___x_609_ == 0 {
                    v___x_610_ = leanh::lean_unsigned_to_nat(1);
                    v___x_611_ = lean_nat_add(v_s1_600_, v___x_610_);
                    v___y_603_ = v___x_611_;
                    state = 6;
                    continue;
                } else {
                    v___x_612_ = leanh::lean_unsigned_to_nat(1);
                    v___y_603_ = v___x_612_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_580_ = l_stdNext(v_x_576_);
                v_snd_581_ = leanh::lean_ctor_get(v___x_580_, 1);
                v_isSharedCheck_598_ = (!leanh::lean_is_exclusive(v___x_580_)) as u8;
                if v_isSharedCheck_598_ == 0 {
                    v_unused_599_ = leanh::lean_ctor_get(v___x_580_, 0);
                    leanh::lean_dec(v_unused_599_);
                    v___x_583_ = v___x_580_;
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_581_);
                    leanh::lean_dec(v___x_580_);
                    v___x_583_ = leanh::lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_s1_585_ = leanh::lean_ctor_get(v_snd_581_, 0);
                v_s2_586_ = leanh::lean_ctor_get(v_snd_581_, 1);
                v_isSharedCheck_597_ = (!leanh::lean_is_exclusive(v_snd_581_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_588_ = v_snd_581_;
                    v_isShared_589_ = v_isSharedCheck_597_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_s2_586_);
                    leanh::lean_inc(v_s1_585_);
                    leanh::lean_dec(v_snd_581_);
                    v___x_588_ = leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_597_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 0, v___y_578_);
                    v_leftG_591_ = v___x_588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___y_578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 1, v_s2_586_);
                    v_leftG_591_ = v_reuseFailAlloc_596_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_rightG_592_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_rightG_592_, 0, v_s1_585_);
                leanh::lean_ctor_set(v_rightG_592_, 1, v___y_579_);
                if v_isShared_584_ == 0 {
                    leanh::lean_ctor_set(v___x_583_, 1, v_rightG_592_);
                    leanh::lean_ctor_set(v___x_583_, 0, v_leftG_591_);
                    v___x_594_ = v___x_583_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_leftG_591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v_rightG_592_);
                    v___x_594_ = v_reuseFailAlloc_595_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_594_;
            }
            6 => {
                v___x_604_ = leanh::lean_unsigned_to_nat(1);
                v___x_605_ = lean_nat_dec_eq(v_s2_601_, v___x_604_);
                if v___x_605_ == 0 {
                    v___x_606_ = lean_nat_sub(v_s2_601_, v___x_604_);
                    v___y_578_ = v___y_603_;
                    v___y_579_ = v___x_606_;
                    state = 1;
                    continue;
                } else {
                    v___x_607_ = leanh::lean_unsigned_to_nat(2147483398);
                    v___y_578_ = v___y_603_;
                    v___y_579_ = v___x_607_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instRandomGenStdGen___lam__0(
    mut v_x_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = l_stdRange;
    return v___x_614_;
}
pub unsafe fn l_instRandomGenStdGen___lam__0___boxed(
    mut v_x_615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_616_ = l_instRandomGenStdGen___lam__0(v_x_615_);
    leanh::lean_dec_ref(v_x_615_);
    return v_res_616_;
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___redArg(
    mut v_inst_625_: *mut leanh::LeanObject,
    mut v_genLo_626_: *mut leanh::LeanObject,
    mut v_genMag_627_: *mut leanh::LeanObject,
    mut v_x_628_: *mut leanh::LeanObject,
    mut v_x_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_631_: u8 = 0;
    let mut v_fst_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_x27_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_630_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_631_ = lean_nat_dec_eq(v_x_628_, v_zero_630_);
                if v_isZero_631_ == 1 {
                    leanh::lean_dec(v_x_628_);
                    leanh::lean_dec_ref(v_inst_625_);
                    return v_x_629_;
                } else {
                    v_fst_632_ = leanh::lean_ctor_get(v_x_629_, 0);
                    leanh::lean_inc(v_fst_632_);
                    v_snd_633_ = leanh::lean_ctor_get(v_x_629_, 1);
                    leanh::lean_inc(v_snd_633_);
                    leanh::lean_dec_ref(v_x_629_);
                    v_next_634_ = leanh::lean_ctor_get(v_inst_625_, 1);
                    leanh::lean_inc_ref(v_next_634_);
                    v___x_635_ = leanh::lean_apply_1(v_next_634_, v_snd_633_);
                    v_fst_636_ = leanh::lean_ctor_get(v___x_635_, 0);
                    v_snd_637_ = leanh::lean_ctor_get(v___x_635_, 1);
                    v_isSharedCheck_651_ = (!leanh::lean_is_exclusive(v___x_635_)) as u8;
                    if v_isSharedCheck_651_ == 0 {
                        v___x_639_ = v___x_635_;
                        v_isShared_640_ = v_isSharedCheck_651_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_637_);
                        leanh::lean_inc(v_fst_636_);
                        leanh::lean_dec(v___x_635_);
                        v___x_639_ = leanh::lean_box(0);
                        v_isShared_640_ = v_isSharedCheck_651_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_641_ = lean_nat_mul(v_fst_632_, v_genMag_627_);
                leanh::lean_dec(v_fst_632_);
                v___x_642_ = lean_nat_sub(v_fst_636_, v_genLo_626_);
                leanh::lean_dec(v_fst_636_);
                v_v_x27_643_ = lean_nat_add(v___x_641_, v___x_642_);
                leanh::lean_dec(v___x_642_);
                leanh::lean_dec(v___x_641_);
                v___x_644_ = lean_nat_div(v_x_628_, v_genMag_627_);
                leanh::lean_dec(v_x_628_);
                v___x_645_ = leanh::lean_unsigned_to_nat(1);
                v___x_646_ = lean_nat_sub(v___x_644_, v___x_645_);
                leanh::lean_dec(v___x_644_);
                if v_isShared_640_ == 0 {
                    leanh::lean_ctor_set(v___x_639_, 0, v_v_x27_643_);
                    v___x_648_ = v___x_639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_650_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_650_, 0, v_v_x27_643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_650_, 1, v_snd_637_);
                    v___x_648_ = v_reuseFailAlloc_650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_628_ = v___x_646_;
                v_x_629_ = v___x_648_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___redArg___boxed(
    mut v_inst_652_: *mut leanh::LeanObject,
    mut v_genLo_653_: *mut leanh::LeanObject,
    mut v_genMag_654_: *mut leanh::LeanObject,
    mut v_x_655_: *mut leanh::LeanObject,
    mut v_x_656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l___private_Init_Data_Random_0__randNatAux___redArg(
        v_inst_652_,
        v_genLo_653_,
        v_genMag_654_,
        v_x_655_,
        v_x_656_,
    );
    leanh::lean_dec(v_genMag_654_);
    leanh::lean_dec(v_genLo_653_);
    return v_res_657_;
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux(
    mut v_gen_658_: *mut leanh::LeanObject,
    mut v_inst_659_: *mut leanh::LeanObject,
    mut v_genLo_660_: *mut leanh::LeanObject,
    mut v_genMag_661_: *mut leanh::LeanObject,
    mut v_x_662_: *mut leanh::LeanObject,
    mut v_x_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = l___private_Init_Data_Random_0__randNatAux___redArg(
        v_inst_659_,
        v_genLo_660_,
        v_genMag_661_,
        v_x_662_,
        v_x_663_,
    );
    return v___x_664_;
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___boxed(
    mut v_gen_665_: *mut leanh::LeanObject,
    mut v_inst_666_: *mut leanh::LeanObject,
    mut v_genLo_667_: *mut leanh::LeanObject,
    mut v_genMag_668_: *mut leanh::LeanObject,
    mut v_x_669_: *mut leanh::LeanObject,
    mut v_x_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l___private_Init_Data_Random_0__randNatAux(
        v_gen_665_,
        v_inst_666_,
        v_genLo_667_,
        v_genMag_668_,
        v_x_669_,
        v_x_670_,
    );
    leanh::lean_dec(v_genMag_668_);
    leanh::lean_dec(v_genLo_667_);
    return v_res_671_;
}
pub unsafe fn l_randNat___redArg(
    mut v_inst_672_: *mut leanh::LeanObject,
    mut v_g_673_: *mut leanh::LeanObject,
    mut v_lo_674_: *mut leanh::LeanObject,
    mut v_hi_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_genMag_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgtMag_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_701_: u8 = 0;
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_x27_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_707_: u8 = 0;
    let mut v_reuseFailAlloc_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut v___x_710_: u8 = 0;
    let mut v___y_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_710_ = lean_nat_dec_lt(v_hi_675_, v_lo_674_);
                if v___x_710_ == 0 {
                    v___y_712_ = v_lo_674_;
                    state = 6;
                    continue;
                } else {
                    v___y_712_ = v_hi_675_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v_range_679_ = leanh::lean_ctor_get(v_inst_672_, 0);
                leanh::lean_inc_ref(v_range_679_);
                leanh::lean_inc(v_g_673_);
                v___x_680_ = leanh::lean_apply_1(v_range_679_, v_g_673_);
                v_fst_681_ = leanh::lean_ctor_get(v___x_680_, 0);
                v_snd_682_ = leanh::lean_ctor_get(v___x_680_, 1);
                v_isSharedCheck_709_ = (!leanh::lean_is_exclusive(v___x_680_)) as u8;
                if v_isSharedCheck_709_ == 0 {
                    v___x_684_ = v___x_680_;
                    v_isShared_685_ = v_isSharedCheck_709_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_682_);
                    leanh::lean_inc(v_fst_681_);
                    leanh::lean_dec(v___x_680_);
                    v___x_684_ = leanh::lean_box(0);
                    v_isShared_685_ = v_isSharedCheck_709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_686_ = lean_nat_sub(v_snd_682_, v_fst_681_);
                leanh::lean_dec(v_snd_682_);
                v___x_687_ = leanh::lean_unsigned_to_nat(1);
                v_genMag_688_ = lean_nat_add(v___x_686_, v___x_687_);
                leanh::lean_dec(v___x_686_);
                v_q_689_ = leanh::lean_unsigned_to_nat(1000);
                v___x_690_ = lean_nat_sub(v___y_678_, v___y_677_);
                v_k_691_ = lean_nat_add(v___x_690_, v___x_687_);
                leanh::lean_dec(v___x_690_);
                v_tgtMag_692_ = lean_nat_mul(v_k_691_, v_q_689_);
                v___x_693_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_685_ == 0 {
                    leanh::lean_ctor_set(v___x_684_, 1, v_g_673_);
                    leanh::lean_ctor_set(v___x_684_, 0, v___x_693_);
                    v___x_695_ = v___x_684_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_708_, 1, v_g_673_);
                    v___x_695_ = v_reuseFailAlloc_708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_696_ = l___private_Init_Data_Random_0__randNatAux___redArg(
                    v_inst_672_,
                    v_fst_681_,
                    v_genMag_688_,
                    v_tgtMag_692_,
                    v___x_695_,
                );
                leanh::lean_dec(v_genMag_688_);
                leanh::lean_dec(v_fst_681_);
                v_fst_697_ = leanh::lean_ctor_get(v___x_696_, 0);
                v_snd_698_ = leanh::lean_ctor_get(v___x_696_, 1);
                v_isSharedCheck_707_ = (!leanh::lean_is_exclusive(v___x_696_)) as u8;
                if v_isSharedCheck_707_ == 0 {
                    v___x_700_ = v___x_696_;
                    v_isShared_701_ = v_isSharedCheck_707_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_698_);
                    leanh::lean_inc(v_fst_697_);
                    leanh::lean_dec(v___x_696_);
                    v___x_700_ = leanh::lean_box(0);
                    v_isShared_701_ = v_isSharedCheck_707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_702_ = lean_nat_mod(v_fst_697_, v_k_691_);
                leanh::lean_dec(v_k_691_);
                leanh::lean_dec(v_fst_697_);
                v_v_x27_703_ = lean_nat_add(v___y_677_, v___x_702_);
                leanh::lean_dec(v___x_702_);
                if v_isShared_701_ == 0 {
                    leanh::lean_ctor_set(v___x_700_, 0, v_v_x27_703_);
                    v___x_705_ = v___x_700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v_v_x27_703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_698_);
                    v___x_705_ = v_reuseFailAlloc_706_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_705_;
            }
            6 => {
                if v___x_710_ == 0 {
                    v___y_677_ = v___y_712_;
                    v___y_678_ = v_hi_675_;
                    state = 1;
                    continue;
                } else {
                    v___y_677_ = v___y_712_;
                    v___y_678_ = v_lo_674_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_randNat___redArg___boxed(
    mut v_inst_713_: *mut leanh::LeanObject,
    mut v_g_714_: *mut leanh::LeanObject,
    mut v_lo_715_: *mut leanh::LeanObject,
    mut v_hi_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_randNat___redArg(v_inst_713_, v_g_714_, v_lo_715_, v_hi_716_);
    leanh::lean_dec(v_hi_716_);
    leanh::lean_dec(v_lo_715_);
    return v_res_717_;
}
pub unsafe fn l_randNat(
    mut v_gen_718_: *mut leanh::LeanObject,
    mut v_inst_719_: *mut leanh::LeanObject,
    mut v_g_720_: *mut leanh::LeanObject,
    mut v_lo_721_: *mut leanh::LeanObject,
    mut v_hi_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = l_randNat___redArg(v_inst_719_, v_g_720_, v_lo_721_, v_hi_722_);
    return v___x_723_;
}
pub unsafe fn l_randNat___boxed(
    mut v_gen_724_: *mut leanh::LeanObject,
    mut v_inst_725_: *mut leanh::LeanObject,
    mut v_g_726_: *mut leanh::LeanObject,
    mut v_lo_727_: *mut leanh::LeanObject,
    mut v_hi_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_randNat(v_gen_724_, v_inst_725_, v_g_726_, v_lo_727_, v_hi_728_);
    leanh::lean_dec(v_hi_728_);
    leanh::lean_dec(v_lo_727_);
    return v_res_729_;
}
pub unsafe fn l_randBool___redArg(
    mut v_inst_730_: *mut leanh::LeanObject,
    mut v_g_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v___x_740_: u8 = 0;
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_732_ = leanh::lean_unsigned_to_nat(0);
                v___x_733_ = leanh::lean_unsigned_to_nat(1);
                v___x_734_ = l_randNat___redArg(v_inst_730_, v_g_731_, v___x_732_, v___x_733_);
                v_fst_735_ = leanh::lean_ctor_get(v___x_734_, 0);
                v_snd_736_ = leanh::lean_ctor_get(v___x_734_, 1);
                v_isSharedCheck_745_ = (!leanh::lean_is_exclusive(v___x_734_)) as u8;
                if v_isSharedCheck_745_ == 0 {
                    v___x_738_ = v___x_734_;
                    v_isShared_739_ = v_isSharedCheck_745_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_736_);
                    leanh::lean_inc(v_fst_735_);
                    leanh::lean_dec(v___x_734_);
                    v___x_738_ = leanh::lean_box(0);
                    v_isShared_739_ = v_isSharedCheck_745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_740_ = lean_nat_dec_eq(v_fst_735_, v___x_733_);
                leanh::lean_dec(v_fst_735_);
                v___x_741_ = leanh::lean_box((v___x_740_) as usize);
                if v_isShared_739_ == 0 {
                    leanh::lean_ctor_set(v___x_738_, 0, v___x_741_);
                    v___x_743_ = v___x_738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_744_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_736_);
                    v___x_743_ = v_reuseFailAlloc_744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_randBool(
    mut v_gen_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_g_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = l_randBool___redArg(v_inst_747_, v_g_748_);
    return v___x_749_;
}
pub unsafe fn l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_751_: usize = 0;
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_756_: u8 = 0;
    let mut v___x_757_: u64 = 0;
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_764_: u8 = 0;
    let mut v_a_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_751_ = 8usize;
                v___x_752_ = lean_io_get_random_bytes(v___x_751_);
                if leanh::lean_obj_tag(v___x_752_) == 0 {
                    v_a_753_ = leanh::lean_ctor_get(v___x_752_, 0);
                    v_isSharedCheck_764_ = (!leanh::lean_is_exclusive(v___x_752_)) as u8;
                    if v_isSharedCheck_764_ == 0 {
                        v___x_755_ = v___x_752_;
                        v_isShared_756_ = v_isSharedCheck_764_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_753_);
                        leanh::lean_dec(v___x_752_);
                        v___x_755_ = leanh::lean_box(0);
                        v_isShared_756_ = v_isSharedCheck_764_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_765_ = leanh::lean_ctor_get(v___x_752_, 0);
                    v_isSharedCheck_772_ = (!leanh::lean_is_exclusive(v___x_752_)) as u8;
                    if v_isSharedCheck_772_ == 0 {
                        v___x_767_ = v___x_752_;
                        v_isShared_768_ = v_isSharedCheck_772_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_765_);
                        leanh::lean_dec(v___x_752_);
                        v___x_767_ = leanh::lean_box(0);
                        v_isShared_768_ = v_isSharedCheck_772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_757_ = l_ByteArray_toUInt64LE_x21(v_a_753_);
                leanh::lean_dec(v_a_753_);
                v___x_758_ = lean_uint64_to_nat(v___x_757_);
                v___x_759_ = l_mkStdGen(v___x_758_);
                leanh::lean_dec(v___x_758_);
                v___x_760_ = lean_st_mk_ref(v___x_759_);
                if v_isShared_756_ == 0 {
                    leanh::lean_ctor_set(v___x_755_, 0, v___x_760_);
                    v___x_762_ = v___x_755_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
                    v___x_762_ = v_reuseFailAlloc_763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_762_;
            }
            3 => {
                if v_isShared_768_ == 0 {
                    v___x_770_ = v___x_767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_771_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
                    v___x_770_ = v_reuseFailAlloc_771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2____boxed(
    mut v_a_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
    return v_res_774_;
}
pub unsafe fn l_IO_setRandSeed(
    mut v_n_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = l_IO_stdGenRef;
    v___x_778_ = l_mkStdGen(v_n_775_);
    v___x_779_ = lean_st_ref_set(v___x_777_, v___x_778_);
    return v___x_779_;
}
pub unsafe fn l_IO_setRandSeed___boxed(
    mut v_n_780_: *mut leanh::LeanObject,
    mut v_a_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_IO_setRandSeed(v_n_780_);
    leanh::lean_dec(v_n_780_);
    return v_res_782_;
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(
    mut v_genLo_783_: *mut leanh::LeanObject,
    mut v_genMag_784_: *mut leanh::LeanObject,
    mut v_x_785_: *mut leanh::LeanObject,
    mut v_x_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_788_: u8 = 0;
    let mut v_fst_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_796_: u8 = 0;
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_x27_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_787_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_788_ = lean_nat_dec_eq(v_x_785_, v_zero_787_);
                if v_isZero_788_ == 1 {
                    leanh::lean_dec(v_x_785_);
                    return v_x_786_;
                } else {
                    v_fst_789_ = leanh::lean_ctor_get(v_x_786_, 0);
                    leanh::lean_inc(v_fst_789_);
                    v_snd_790_ = leanh::lean_ctor_get(v_x_786_, 1);
                    leanh::lean_inc(v_snd_790_);
                    leanh::lean_dec_ref(v_x_786_);
                    v___x_791_ = l_stdNext(v_snd_790_);
                    v_fst_792_ = leanh::lean_ctor_get(v___x_791_, 0);
                    v_snd_793_ = leanh::lean_ctor_get(v___x_791_, 1);
                    v_isSharedCheck_807_ = (!leanh::lean_is_exclusive(v___x_791_)) as u8;
                    if v_isSharedCheck_807_ == 0 {
                        v___x_795_ = v___x_791_;
                        v_isShared_796_ = v_isSharedCheck_807_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_793_);
                        leanh::lean_inc(v_fst_792_);
                        leanh::lean_dec(v___x_791_);
                        v___x_795_ = leanh::lean_box(0);
                        v_isShared_796_ = v_isSharedCheck_807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_797_ = lean_nat_mul(v_fst_789_, v_genMag_784_);
                leanh::lean_dec(v_fst_789_);
                v___x_798_ = lean_nat_sub(v_fst_792_, v_genLo_783_);
                leanh::lean_dec(v_fst_792_);
                v_v_x27_799_ = lean_nat_add(v___x_797_, v___x_798_);
                leanh::lean_dec(v___x_798_);
                leanh::lean_dec(v___x_797_);
                v___x_800_ = lean_nat_div(v_x_785_, v_genMag_784_);
                leanh::lean_dec(v_x_785_);
                v___x_801_ = leanh::lean_unsigned_to_nat(1);
                v___x_802_ = lean_nat_sub(v___x_800_, v___x_801_);
                leanh::lean_dec(v___x_800_);
                if v_isShared_796_ == 0 {
                    leanh::lean_ctor_set(v___x_795_, 0, v_v_x27_799_);
                    v___x_804_ = v___x_795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_806_, 0, v_v_x27_799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_806_, 1, v_snd_793_);
                    v___x_804_ = v_reuseFailAlloc_806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_785_ = v___x_802_;
                v_x_786_ = v___x_804_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0___boxed(
    mut v_genLo_808_: *mut leanh::LeanObject,
    mut v_genMag_809_: *mut leanh::LeanObject,
    mut v_x_810_: *mut leanh::LeanObject,
    mut v_x_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(v_genLo_808_, v_genMag_809_, v_x_810_, v_x_811_);
    leanh::lean_dec(v_genMag_809_);
    leanh::lean_dec(v_genLo_808_);
    return v_res_812_;
}
pub unsafe fn l_randNat___at___00IO_rand_spec__0(
    mut v_g_813_: *mut leanh::LeanObject,
    mut v_lo_814_: *mut leanh::LeanObject,
    mut v_hi_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_genMag_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgtMag_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_x27_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_842_: u8 = 0;
    let mut v___x_843_: u8 = 0;
    let mut v___y_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_843_ = lean_nat_dec_lt(v_hi_815_, v_lo_814_);
                if v___x_843_ == 0 {
                    v___y_845_ = v_lo_814_;
                    state = 4;
                    continue;
                } else {
                    v___y_845_ = v_hi_815_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_819_ = l_stdRange;
                v_fst_820_ = leanh::lean_ctor_get(v___x_819_, 0);
                v_snd_821_ = leanh::lean_ctor_get(v___x_819_, 1);
                v___x_822_ = lean_nat_sub(v_snd_821_, v_fst_820_);
                v___x_823_ = leanh::lean_unsigned_to_nat(1);
                v_genMag_824_ = lean_nat_add(v___x_822_, v___x_823_);
                leanh::lean_dec(v___x_822_);
                v_q_825_ = leanh::lean_unsigned_to_nat(1000);
                v___x_826_ = lean_nat_sub(v___y_818_, v___y_817_);
                v_k_827_ = lean_nat_add(v___x_826_, v___x_823_);
                leanh::lean_dec(v___x_826_);
                v_tgtMag_828_ = lean_nat_mul(v_k_827_, v_q_825_);
                v___x_829_ = leanh::lean_unsigned_to_nat(0);
                v___x_830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_830_, 0, v___x_829_);
                leanh::lean_ctor_set(v___x_830_, 1, v_g_813_);
                v___x_831_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(v_fst_820_, v_genMag_824_, v_tgtMag_828_, v___x_830_);
                leanh::lean_dec(v_genMag_824_);
                v_fst_832_ = leanh::lean_ctor_get(v___x_831_, 0);
                v_snd_833_ = leanh::lean_ctor_get(v___x_831_, 1);
                v_isSharedCheck_842_ = (!leanh::lean_is_exclusive(v___x_831_)) as u8;
                if v_isSharedCheck_842_ == 0 {
                    v___x_835_ = v___x_831_;
                    v_isShared_836_ = v_isSharedCheck_842_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_833_);
                    leanh::lean_inc(v_fst_832_);
                    leanh::lean_dec(v___x_831_);
                    v___x_835_ = leanh::lean_box(0);
                    v_isShared_836_ = v_isSharedCheck_842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_837_ = lean_nat_mod(v_fst_832_, v_k_827_);
                leanh::lean_dec(v_k_827_);
                leanh::lean_dec(v_fst_832_);
                v_v_x27_838_ = lean_nat_add(v___y_817_, v___x_837_);
                leanh::lean_dec(v___x_837_);
                if v_isShared_836_ == 0 {
                    leanh::lean_ctor_set(v___x_835_, 0, v_v_x27_838_);
                    v___x_840_ = v___x_835_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_841_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_841_, 0, v_v_x27_838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_841_, 1, v_snd_833_);
                    v___x_840_ = v_reuseFailAlloc_841_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_840_;
            }
            4 => {
                if v___x_843_ == 0 {
                    v___y_817_ = v___y_845_;
                    v___y_818_ = v_hi_815_;
                    state = 1;
                    continue;
                } else {
                    v___y_817_ = v___y_845_;
                    v___y_818_ = v_lo_814_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_randNat___at___00IO_rand_spec__0___boxed(
    mut v_g_846_: *mut leanh::LeanObject,
    mut v_lo_847_: *mut leanh::LeanObject,
    mut v_hi_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_randNat___at___00IO_rand_spec__0(v_g_846_, v_lo_847_, v_hi_848_);
    leanh::lean_dec(v_hi_848_);
    leanh::lean_dec(v_lo_847_);
    return v_res_849_;
}
pub unsafe fn l_IO_rand(
    mut v_lo_850_: *mut leanh::LeanObject,
    mut v_hi_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l_IO_stdGenRef;
    v___x_854_ = lean_st_ref_get(v___x_853_);
    v___x_855_ = l_randNat___at___00IO_rand_spec__0(v___x_854_, v_lo_850_, v_hi_851_);
    v_fst_856_ = leanh::lean_ctor_get(v___x_855_, 0);
    leanh::lean_inc(v_fst_856_);
    v_snd_857_ = leanh::lean_ctor_get(v___x_855_, 1);
    leanh::lean_inc(v_snd_857_);
    leanh::lean_dec_ref(v___x_855_);
    v___x_858_ = lean_st_ref_set(v___x_853_, v_snd_857_);
    return v_fst_856_;
}
pub unsafe fn l_IO_rand___boxed(
    mut v_lo_859_: *mut leanh::LeanObject,
    mut v_hi_860_: *mut leanh::LeanObject,
    mut v_a_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l_IO_rand(v_lo_859_, v_hi_860_);
    leanh::lean_dec(v_hi_860_);
    leanh::lean_dec(v_lo_859_);
    return v_res_862_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Random(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_instInhabitedStdGen = _init_l_instInhabitedStdGen();
    leanh::lean_mark_persistent(l_instInhabitedStdGen);
    res = l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_IO_stdGenRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_IO_stdGenRef);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Random(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Random(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Random(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Random(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Random(builtin);
}