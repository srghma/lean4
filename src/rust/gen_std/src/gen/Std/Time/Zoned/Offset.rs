// Lean compiler output
// Module: Std.Time.Zoned.Offset
// Imports: Std.Time.Time
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_div, lean_int_ediv,
    lean_int_mod, lean_int_mul, lean_int_neg, lean_nat_to_int, lean_string_append,
    lean_string_length,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::l_compareOn___boxed;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Std::Time::Time::Unit::Second::{
    l_Std_Time_Second_instOrdOffset___aux__1___boxed, l_Std_Time_Second_instReprOffset___lam__0,
};
use crate::r#gen::Std::Time::Time::{initialize_Std_Time_Time, runtime_initialize_Std_Time_Time};
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 101, 99, 111, 110, 100, 0],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprOffset___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_TimeZone_instReprOffset_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_instInhabitedOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instOrdOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_instOrdOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instOrdOffset___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Second_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_instOrdOffset___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instOrdOffset___closed__2_value: leanh::LeanClosureObject<4> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_instOrdOffset___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instOrdOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instOrdOffset___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_toIsoString___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [48, 0],
};
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_toIsoString___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_Offset_toIsoString___closed__5_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_toIsoString___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [43, 0],
};
static mut l_Std_Time_TimeZone_Offset_toIsoString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_Offset_zero: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_instReprOffset_repr_spec__0(
    mut v_a_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = lean_nat_to_int(v_a_155_);
    return v___x_156_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_170_ = leanh::lean_unsigned_to_nat(10);
    v___x_171_ = lean_nat_to_int(v___x_170_);
    return v___x_171_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_173_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0;
    v___x_174_ = lean_string_length(v___x_173_);
    return v___x_174_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once),
        _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9,
    );
    v___x_176_ = lean_nat_to_int(v___x_175_);
    return v___x_176_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprOffset_repr___redArg(
    mut v_x_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: u8 = 0;
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6;
    v___x_183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once),
        _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7,
    );
    v___x_184_ = leanh::lean_unsigned_to_nat(0);
    v___x_185_ = l_Std_Time_Second_instReprOffset___lam__0(v_x_181_, v___x_184_);
    v___x_186_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_186_, 0, v___x_183_);
    leanh::lean_ctor_set(v___x_186_, 1, v___x_185_);
    v___x_187_ = 0;
    v___x_188_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_188_, 0, v___x_186_);
    leanh::lean_ctor_set_uint8(
        v___x_188_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_187_,
    );
    v___x_189_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_189_, 0, v___x_182_);
    leanh::lean_ctor_set(v___x_189_, 1, v___x_188_);
    v___x_190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once),
        _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10,
    );
    v___x_191_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11;
    v___x_192_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_192_, 0, v___x_191_);
    leanh::lean_ctor_set(v___x_192_, 1, v___x_189_);
    v___x_193_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12;
    v___x_194_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_194_, 0, v___x_192_);
    leanh::lean_ctor_set(v___x_194_, 1, v___x_193_);
    v___x_195_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_195_, 0, v___x_190_);
    leanh::lean_ctor_set(v___x_195_, 1, v___x_194_);
    v___x_196_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_196_, 0, v___x_195_);
    leanh::lean_ctor_set_uint8(
        v___x_196_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_187_,
    );
    return v___x_196_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprOffset_repr___redArg___boxed(
    mut v_x_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_198_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_197_);
    leanh::lean_dec(v_x_197_);
    return v_res_198_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprOffset_repr(
    mut v_x_199_: *mut leanh::LeanObject,
    mut v_prec_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_201_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_199_);
    return v___x_201_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprOffset_repr___boxed(
    mut v_x_202_: *mut leanh::LeanObject,
    mut v_prec_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = l_Std_Time_TimeZone_instReprOffset_repr(v_x_202_, v_prec_203_);
    leanh::lean_dec(v_prec_203_);
    leanh::lean_dec(v_x_202_);
    return v_res_204_;
}
pub unsafe fn l_Std_Time_TimeZone_instDecidableEqOffset_decEq(
    mut v_x_207_: *mut leanh::LeanObject,
    mut v_x_208_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_209_: u8 = 0;
    v___x_209_ = lean_int_dec_eq(v_x_207_, v_x_208_);
    return v___x_209_;
}
pub unsafe fn l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(
    mut v_x_210_: *mut leanh::LeanObject,
    mut v_x_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_212_: u8 = 0;
    let mut v_r_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ = l_Std_Time_TimeZone_instDecidableEqOffset_decEq(v_x_210_, v_x_211_);
    leanh::lean_dec(v_x_211_);
    leanh::lean_dec(v_x_210_);
    v_r_213_ = leanh::lean_box((v_res_212_) as usize);
    return v_r_213_;
}
pub unsafe fn l_Std_Time_TimeZone_instDecidableEqOffset(
    mut v_x_214_: *mut leanh::LeanObject,
    mut v_x_215_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_216_: u8 = 0;
    v___x_216_ = lean_int_dec_eq(v_x_214_, v_x_215_);
    return v___x_216_;
}
pub unsafe fn l_Std_Time_TimeZone_instDecidableEqOffset___boxed(
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_x_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_219_: u8 = 0;
    let mut v_r_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_219_ = l_Std_Time_TimeZone_instDecidableEqOffset(v_x_217_, v_x_218_);
    leanh::lean_dec(v_x_218_);
    leanh::lean_dec(v_x_217_);
    v_r_220_ = leanh::lean_box((v_res_219_) as usize);
    return v_r_220_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_221_ = leanh::lean_unsigned_to_nat(0);
    v___x_222_ = lean_nat_to_int(v___x_221_);
    return v___x_222_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedOffset() -> *mut leanh::LeanObject {
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_223_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0,
    );
    return v___x_223_;
}
pub unsafe fn l_Std_Time_TimeZone_instOrdOffset___lam__0(
    mut v_x_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_224_);
    return v_x_224_;
}
pub unsafe fn l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(
    mut v_x_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l_Std_Time_TimeZone_instOrdOffset___lam__0(v_x_225_);
    leanh::lean_dec(v_x_225_);
    return v_res_226_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(
    mut v_a_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = l_Rat_ofInt(v_a_233_);
    return v___x_234_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_237_ = leanh::lean_unsigned_to_nat(3600);
    v___x_238_ = lean_nat_to_int(v___x_237_);
    return v___x_238_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = leanh::lean_unsigned_to_nat(60);
    v___x_240_ = lean_nat_to_int(v___x_239_);
    return v___x_240_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = leanh::lean_unsigned_to_nat(0);
    v___x_242_ = lean_nat_to_int(v___x_241_);
    return v___x_242_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_toIsoString(
    mut v_offset_245_: *mut leanh::LeanObject,
    mut v_colon_246_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_258_: u8 = 0;
    let mut v___y_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: u8 = 0;
    let mut v___x_276_: u8 = 0;
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_281_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4,
                );
                v___x_282_ = lean_int_dec_le(v___x_281_, v_offset_245_);
                if v___x_282_ == 0 {
                    v___x_283_ = l_Std_Time_TimeZone_Offset_toIsoString___closed__5;
                    v___x_284_ = lean_int_neg(v_offset_245_);
                    leanh::lean_dec(v_offset_245_);
                    v_fst_267_ = v___x_283_;
                    v_snd_268_ = v___x_284_;
                    state = 3;
                    continue;
                } else {
                    v___x_285_ = l_Std_Time_TimeZone_Offset_toIsoString___closed__6;
                    v_fst_267_ = v___x_285_;
                    v_snd_268_ = v_offset_245_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v_colon_246_ == 0 {
                    leanh::lean_inc_ref(v___y_249_);
                    v___x_251_ = lean_string_append(v___y_249_, v___y_248_);
                    leanh::lean_dec_ref(v___y_248_);
                    v___x_252_ = lean_string_append(v___x_251_, v___y_250_);
                    leanh::lean_dec_ref(v___y_250_);
                    return v___x_252_;
                } else {
                    leanh::lean_inc_ref(v___y_249_);
                    v___x_253_ = lean_string_append(v___y_249_, v___y_248_);
                    leanh::lean_dec_ref(v___y_248_);
                    v___x_254_ = l_Std_Time_TimeZone_Offset_toIsoString___closed__0;
                    v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
                    v___x_256_ = lean_string_append(v___x_255_, v___y_250_);
                    leanh::lean_dec_ref(v___y_250_);
                    return v___x_256_;
                }
            }
            2 => {
                if v___y_258_ == 0 {
                    v___x_262_ = l_Int_repr(v___y_259_);
                    leanh::lean_dec(v___y_259_);
                    v___y_248_ = v___y_261_;
                    v___y_249_ = v___y_260_;
                    v___y_250_ = v___x_262_;
                    state = 1;
                    continue;
                } else {
                    v___x_263_ = l_Std_Time_TimeZone_Offset_toIsoString___closed__1;
                    v___x_264_ = l_Int_repr(v___y_259_);
                    leanh::lean_dec(v___y_259_);
                    v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
                    leanh::lean_dec_ref(v___x_264_);
                    v___y_248_ = v___y_261_;
                    v___y_249_ = v___y_260_;
                    v___y_250_ = v___x_265_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_269_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once
                    ),
                    _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2,
                );
                v_hour_270_ = lean_int_div(v_snd_268_, v___x_269_);
                v___x_271_ = lean_int_mod(v_snd_268_, v___x_269_);
                leanh::lean_dec(v_snd_268_);
                v___x_272_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once
                    ),
                    _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3,
                );
                v_minute_273_ = lean_int_ediv(v___x_271_, v___x_272_);
                leanh::lean_dec(v___x_271_);
                v___x_274_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7,
                );
                v___x_275_ = lean_int_dec_lt(v_hour_270_, v___x_274_);
                v___x_276_ = lean_int_dec_lt(v_minute_273_, v___x_274_);
                if v___x_275_ == 0 {
                    v___x_277_ = l_Int_repr(v_hour_270_);
                    leanh::lean_dec(v_hour_270_);
                    v___y_258_ = v___x_276_;
                    v___y_259_ = v_minute_273_;
                    v___y_260_ = v_fst_267_;
                    v___y_261_ = v___x_277_;
                    state = 2;
                    continue;
                } else {
                    v___x_278_ = l_Std_Time_TimeZone_Offset_toIsoString___closed__1;
                    v___x_279_ = l_Int_repr(v_hour_270_);
                    leanh::lean_dec(v_hour_270_);
                    v___x_280_ = lean_string_append(v___x_278_, v___x_279_);
                    leanh::lean_dec_ref(v___x_279_);
                    v___y_258_ = v___x_276_;
                    v___y_259_ = v_minute_273_;
                    v___y_260_ = v_fst_267_;
                    v___y_261_ = v___x_280_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_Offset_toIsoString___boxed(
    mut v_offset_286_: *mut leanh::LeanObject,
    mut v_colon_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_colon_boxed_288_: u8 = 0;
    let mut v_res_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_colon_boxed_288_ = (leanh::lean_unbox(v_colon_287_) as u8);
    v_res_289_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_286_, v_colon_boxed_288_);
    return v_res_289_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(
    mut v_a_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_nat_to_int(v_a_290_);
    v___x_292_ = l_Rat_ofInt(v___x_291_);
    return v___x_292_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_zero() -> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once),
        _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4,
    );
    return v___x_293_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_ofHours(
    mut v_n_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once),
        _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2,
    );
    v___x_296_ = lean_int_mul(v_n_294_, v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_ofHours___boxed(
    mut v_n_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_297_);
    leanh::lean_dec(v_n_297_);
    return v_res_298_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(
    mut v_n_299_: *mut leanh::LeanObject,
    mut v_m_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once),
        _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2,
    );
    v___x_302_ = lean_int_mul(v_n_299_, v___x_301_);
    v___x_303_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once),
        _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3,
    );
    v___x_304_ = lean_int_mul(v_m_300_, v___x_303_);
    v___x_305_ = lean_int_add(v___x_302_, v___x_304_);
    leanh::lean_dec(v___x_304_);
    leanh::lean_dec(v___x_302_);
    return v___x_305_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(
    mut v_n_306_: *mut leanh::LeanObject,
    mut v_m_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(v_n_306_, v_m_307_);
    leanh::lean_dec(v_m_307_);
    leanh::lean_dec(v_n_306_);
    return v_res_308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Offset(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_TimeZone_instInhabitedOffset = _init_l_Std_Time_TimeZone_instInhabitedOffset();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedOffset);
    l_Std_Time_TimeZone_Offset_zero = _init_l_Std_Time_TimeZone_Offset_zero();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_Offset_zero);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Offset(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_Offset(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Offset(builtin);
}