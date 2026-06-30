// Lean compiler output
// Module: Std.Time.Date.Basic
// Imports: Std.Time.Date.Unit.Basic Std.Time.Date.ValidDate
use crate::ffi::{lean_int_add, lean_int_div, lean_int_mul, lean_int_sub, lean_nat_to_int};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_add___boxed, l_Int_sub___boxed};
use crate::r#gen::Std::Time::Date::Unit::Basic::{
    initialize_Std_Time_Date_Unit_Basic, runtime_initialize_Std_Time_Date_Unit_Basic,
};
use crate::r#gen::Std::Time::Date::ValidDate::{
    initialize_Std_Time_Date_ValidDate, runtime_initialize_Std_Time_Date_ValidDate,
};
static mut l_Std_Time_Nanosecond_Offset_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_Offset_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_Offset_toWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_Offset_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_Offset_toWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_Offset_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_Offset_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_Offset_toWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_Offset_toWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Offset_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Offset_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Offset_toWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Offset_toWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__1___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__2___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__3___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__4___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__5___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__6___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__7___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__7___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__8___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__8___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__9___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__9___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__10___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__10___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__11___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__11___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__11___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__11___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__12___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__12___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__12___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__12___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__13___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__13___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__13___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__13___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__14___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__14___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__15___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__15___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__15___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__15___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__16___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__16___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__16___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__17___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__17___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__17___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__17___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__18___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__18___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__18___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__18___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__19___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__19___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__19___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__19___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__20___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__20___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__22___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__22___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__22___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__22___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__23___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__23___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__23___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__23___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__24___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__24___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__24___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__24___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__25___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__25___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__25___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__25___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__26___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__26___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__26___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__26___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__28___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__28___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__28___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__28___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__29___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__29___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__29___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__29___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__30___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__30___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__30___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__30___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__31___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__31___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__31___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__31___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__32___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__32___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__32___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__33___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__33___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__33___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__33___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__34___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__34___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__34___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__34___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__35___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__35___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__35___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__35___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__36___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__36___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__36___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__36___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__37___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__37___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__37___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__37___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__38___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__38___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__38___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__38___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__39___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__39___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__39___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__39___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__40___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__40___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__40___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__40___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__41___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffsetOffset__41___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__41___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__41___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHAddOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__1___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__2___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__3___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__4___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__5___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__6___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__7___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__8___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__9___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__9___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__10___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__10___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__11___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__11___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__11___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__11___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__12___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__12___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__12___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__12___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__13___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__13___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__13___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__13___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__14___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__14___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__15___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__15___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__15___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__15___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__16___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__16___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__16___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__17___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__17___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__17___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__17___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__18___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__18___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__18___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__18___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__19___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__19___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__19___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__19___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__20___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__20___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__22___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__22___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__22___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__22___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__23___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__23___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__23___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__23___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__24___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__24___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__24___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__24___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__25___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__25___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__25___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__25___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__26___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__26___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__26___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__26___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__28___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__28___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__28___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__28___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__29___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__29___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__29___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__29___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__30___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__30___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__30___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__30___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__31___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__31___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__31___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__31___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__32___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__32___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__32___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__33___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__33___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__33___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__33___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__34___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__34___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__34___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__34___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__35___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__35___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__35___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__35___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__36___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__36___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__36___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__36___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__37___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__37___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__37___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__37___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__38___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__38___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__38___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__38___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__39___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__39___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__39___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__39___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__40___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__40___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__40___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__40___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__41___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffsetOffset__41___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__41___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__41___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instHSubOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = leanh::lean_cstr_to_nat(b"86400000000000\0".as_ptr().cast());
    v___x_962_ = lean_nat_to_int(v___x_961_);
    return v___x_962_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toDays(
    mut v_nanoseconds_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_965_ = lean_int_div(v_nanoseconds_963_, v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toDays___boxed(
    mut v_nanoseconds_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Std_Time_Nanosecond_Offset_toDays(v_nanoseconds_966_);
    leanh::lean_dec(v_nanoseconds_966_);
    return v_res_967_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofDays(
    mut v_days_968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_970_ = lean_int_mul(v_days_968_, v___x_969_);
    return v___x_970_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofDays___boxed(
    mut v_days_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Std_Time_Nanosecond_Offset_ofDays(v_days_971_);
    leanh::lean_dec(v_days_971_);
    return v_res_972_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = leanh::lean_cstr_to_nat(b"604800000000000\0".as_ptr().cast());
    v___x_974_ = lean_nat_to_int(v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toWeeks(
    mut v_nanoseconds_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_977_ = lean_int_div(v_nanoseconds_975_, v___x_976_);
    return v___x_977_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toWeeks___boxed(
    mut v_nanoseconds_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_979_ = l_Std_Time_Nanosecond_Offset_toWeeks(v_nanoseconds_978_);
    leanh::lean_dec(v_nanoseconds_978_);
    return v_res_979_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofWeeks(
    mut v_weeks_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_981_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_982_ = lean_int_mul(v_weeks_980_, v___x_981_);
    return v___x_982_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofWeeks___boxed(
    mut v_weeks_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Std_Time_Nanosecond_Offset_ofWeeks(v_weeks_983_);
    leanh::lean_dec(v_weeks_983_);
    return v_res_984_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toDays___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = leanh::lean_unsigned_to_nat(86400000);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toDays(
    mut v_milliseconds_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_989_ = lean_int_div(v_milliseconds_987_, v___x_988_);
    return v___x_989_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toDays___boxed(
    mut v_milliseconds_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Std_Time_Millisecond_Offset_toDays(v_milliseconds_990_);
    leanh::lean_dec(v_milliseconds_990_);
    return v_res_991_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofDays(
    mut v_days_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_994_ = lean_int_mul(v_days_992_, v___x_993_);
    return v___x_994_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofDays___boxed(
    mut v_days_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Std_Time_Millisecond_Offset_ofDays(v_days_995_);
    leanh::lean_dec(v_days_995_);
    return v_res_996_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_997_ = leanh::lean_unsigned_to_nat(604800000);
    v___x_998_ = lean_nat_to_int(v___x_997_);
    return v___x_998_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toWeeks(
    mut v_milliseconds_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1001_ = lean_int_div(v_milliseconds_999_, v___x_1000_);
    return v___x_1001_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toWeeks___boxed(
    mut v_milliseconds_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_Std_Time_Millisecond_Offset_toWeeks(v_milliseconds_1002_);
    leanh::lean_dec(v_milliseconds_1002_);
    return v_res_1003_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofWeeks(
    mut v_weeks_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1006_ = lean_int_mul(v_weeks_1004_, v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofWeeks___boxed(
    mut v_weeks_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Std_Time_Millisecond_Offset_ofWeeks(v_weeks_1007_);
    leanh::lean_dec(v_weeks_1007_);
    return v_res_1008_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toDays___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = leanh::lean_unsigned_to_nat(86400);
    v___x_1010_ = lean_nat_to_int(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn l_Std_Time_Second_Offset_toDays(
    mut v_seconds_1011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1013_ = lean_int_div(v_seconds_1011_, v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Std_Time_Second_Offset_toDays___boxed(
    mut v_seconds_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Std_Time_Second_Offset_toDays(v_seconds_1014_);
    leanh::lean_dec(v_seconds_1014_);
    return v_res_1015_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofDays(
    mut v_days_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1018_ = lean_int_mul(v_days_1016_, v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofDays___boxed(
    mut v_days_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1020_ = l_Std_Time_Second_Offset_ofDays(v_days_1019_);
    leanh::lean_dec(v_days_1019_);
    return v_res_1020_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toWeeks___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = leanh::lean_unsigned_to_nat(604800);
    v___x_1022_ = lean_nat_to_int(v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Std_Time_Second_Offset_toWeeks(
    mut v_seconds_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1024_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1025_ = lean_int_div(v_seconds_1023_, v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Time_Second_Offset_toWeeks___boxed(
    mut v_seconds_1026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Std_Time_Second_Offset_toWeeks(v_seconds_1026_);
    leanh::lean_dec(v_seconds_1026_);
    return v_res_1027_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofWeeks(
    mut v_weeks_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1029_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1030_ = lean_int_mul(v_weeks_1028_, v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofWeeks___boxed(
    mut v_weeks_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Std_Time_Second_Offset_ofWeeks(v_weeks_1031_);
    leanh::lean_dec(v_weeks_1031_);
    return v_res_1032_;
}
pub unsafe fn _init_l_Std_Time_Minute_Offset_toDays___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = leanh::lean_unsigned_to_nat(1440);
    v___x_1034_ = lean_nat_to_int(v___x_1033_);
    return v___x_1034_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toDays(
    mut v_minutes_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1037_ = lean_int_div(v_minutes_1035_, v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toDays___boxed(
    mut v_minutes_1038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Std_Time_Minute_Offset_toDays(v_minutes_1038_);
    leanh::lean_dec(v_minutes_1038_);
    return v_res_1039_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofDays(
    mut v_days_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1041_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1042_ = lean_int_mul(v_days_1040_, v___x_1041_);
    return v___x_1042_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofDays___boxed(
    mut v_days_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1044_ = l_Std_Time_Minute_Offset_ofDays(v_days_1043_);
    leanh::lean_dec(v_days_1043_);
    return v_res_1044_;
}
pub unsafe fn _init_l_Std_Time_Minute_Offset_toWeeks___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = leanh::lean_unsigned_to_nat(10080);
    v___x_1046_ = lean_nat_to_int(v___x_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toWeeks(
    mut v_minutes_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1049_ = lean_int_div(v_minutes_1047_, v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toWeeks___boxed(
    mut v_minutes_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Std_Time_Minute_Offset_toWeeks(v_minutes_1050_);
    leanh::lean_dec(v_minutes_1050_);
    return v_res_1051_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofWeeks(
    mut v_weeks_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1054_ = lean_int_mul(v_weeks_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofWeeks___boxed(
    mut v_weeks_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_Time_Minute_Offset_ofWeeks(v_weeks_1055_);
    leanh::lean_dec(v_weeks_1055_);
    return v_res_1056_;
}
pub unsafe fn _init_l_Std_Time_Hour_Offset_toDays___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = leanh::lean_unsigned_to_nat(24);
    v___x_1058_ = lean_nat_to_int(v___x_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toDays(
    mut v_hours_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1061_ = lean_int_div(v_hours_1059_, v___x_1060_);
    return v___x_1061_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toDays___boxed(
    mut v_hours_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Std_Time_Hour_Offset_toDays(v_hours_1062_);
    leanh::lean_dec(v_hours_1062_);
    return v_res_1063_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofDays(
    mut v_days_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1065_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1066_ = lean_int_mul(v_days_1064_, v___x_1065_);
    return v___x_1066_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofDays___boxed(
    mut v_days_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_Time_Hour_Offset_ofDays(v_days_1067_);
    leanh::lean_dec(v_days_1067_);
    return v_res_1068_;
}
pub unsafe fn _init_l_Std_Time_Hour_Offset_toWeeks___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = leanh::lean_unsigned_to_nat(168);
    v___x_1070_ = lean_nat_to_int(v___x_1069_);
    return v___x_1070_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toWeeks(
    mut v_hours_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1073_ = lean_int_div(v_hours_1071_, v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toWeeks___boxed(
    mut v_hours_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_Std_Time_Hour_Offset_toWeeks(v_hours_1074_);
    leanh::lean_dec(v_hours_1074_);
    return v_res_1075_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofWeeks(
    mut v_weeks_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1078_ = lean_int_mul(v_weeks_1076_, v___x_1077_);
    return v___x_1078_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofWeeks___boxed(
    mut v_weeks_1079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Std_Time_Hour_Offset_ofWeeks(v_weeks_1079_);
    leanh::lean_dec(v_weeks_1079_);
    return v_res_1080_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = leanh::lean_unsigned_to_nat(1000000);
    v___x_1084_ = lean_nat_to_int(v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset___lam__0(
    mut v_x_1085_: *mut leanh::LeanObject,
    mut v_y_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1088_ = lean_int_mul(v_y_1086_, v___x_1087_);
    v___x_1089_ = lean_int_add(v_x_1085_, v___x_1088_);
    leanh::lean_dec(v___x_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset___lam__0___boxed(
    mut v_x_1090_: *mut leanh::LeanObject,
    mut v_y_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Std_Time_instHAddOffsetOffset___lam__0(v_x_1090_, v_y_1091_);
    leanh::lean_dec(v_y_1091_);
    leanh::lean_dec(v_x_1090_);
    return v_res_1092_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_1096_ = lean_nat_to_int(v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__1___lam__0(
    mut v_x_1097_: *mut leanh::LeanObject,
    mut v_y_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1099_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1100_ = lean_int_mul(v_y_1098_, v___x_1099_);
    v___x_1101_ = lean_int_add(v_x_1097_, v___x_1100_);
    leanh::lean_dec(v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(
    mut v_x_1102_: *mut leanh::LeanObject,
    mut v_y_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Std_Time_instHAddOffsetOffset__1___lam__0(v_x_1102_, v_y_1103_);
    leanh::lean_dec(v_y_1103_);
    leanh::lean_dec(v_x_1102_);
    return v_res_1104_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = leanh::lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_1108_ = lean_nat_to_int(v___x_1107_);
    return v___x_1108_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__2___lam__0(
    mut v_x_1109_: *mut leanh::LeanObject,
    mut v_y_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1112_ = lean_int_mul(v_y_1110_, v___x_1111_);
    v___x_1113_ = lean_int_add(v_x_1109_, v___x_1112_);
    leanh::lean_dec(v___x_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(
    mut v_x_1114_: *mut leanh::LeanObject,
    mut v_y_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_Time_instHAddOffsetOffset__2___lam__0(v_x_1114_, v_y_1115_);
    leanh::lean_dec(v_y_1115_);
    leanh::lean_dec(v_x_1114_);
    return v_res_1116_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = leanh::lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_1120_ = lean_nat_to_int(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__3___lam__0(
    mut v_x_1121_: *mut leanh::LeanObject,
    mut v_y_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1124_ = lean_int_mul(v_y_1122_, v___x_1123_);
    v___x_1125_ = lean_int_add(v_x_1121_, v___x_1124_);
    leanh::lean_dec(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(
    mut v_x_1126_: *mut leanh::LeanObject,
    mut v_y_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ = l_Std_Time_instHAddOffsetOffset__3___lam__0(v_x_1126_, v_y_1127_);
    leanh::lean_dec(v_y_1127_);
    leanh::lean_dec(v_x_1126_);
    return v_res_1128_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__4___lam__0(
    mut v_x_1131_: *mut leanh::LeanObject,
    mut v_y_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1134_ = lean_int_mul(v_y_1132_, v___x_1133_);
    v___x_1135_ = lean_int_add(v_x_1131_, v___x_1134_);
    leanh::lean_dec(v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(
    mut v_x_1136_: *mut leanh::LeanObject,
    mut v_y_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Std_Time_instHAddOffsetOffset__4___lam__0(v_x_1136_, v_y_1137_);
    leanh::lean_dec(v_y_1137_);
    leanh::lean_dec(v_x_1136_);
    return v_res_1138_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__5___lam__0(
    mut v_x_1141_: *mut leanh::LeanObject,
    mut v_y_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1144_ = lean_int_mul(v_y_1142_, v___x_1143_);
    v___x_1145_ = lean_int_add(v_x_1141_, v___x_1144_);
    leanh::lean_dec(v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(
    mut v_x_1146_: *mut leanh::LeanObject,
    mut v_y_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Std_Time_instHAddOffsetOffset__5___lam__0(v_x_1146_, v_y_1147_);
    leanh::lean_dec(v_y_1147_);
    leanh::lean_dec(v_x_1146_);
    return v_res_1148_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__6___lam__0(
    mut v_x_1151_: *mut leanh::LeanObject,
    mut v_y_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1154_ = lean_int_mul(v_x_1151_, v___x_1153_);
    v___x_1155_ = lean_int_add(v___x_1154_, v_y_1152_);
    leanh::lean_dec(v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(
    mut v_x_1156_: *mut leanh::LeanObject,
    mut v_y_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_Std_Time_instHAddOffsetOffset__6___lam__0(v_x_1156_, v_y_1157_);
    leanh::lean_dec(v_y_1157_);
    leanh::lean_dec(v_x_1156_);
    return v_res_1158_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = leanh::lean_unsigned_to_nat(1000);
    v___x_1163_ = lean_nat_to_int(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__7___lam__0(
    mut v_x_1164_: *mut leanh::LeanObject,
    mut v_y_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1167_ = lean_int_mul(v_y_1165_, v___x_1166_);
    v___x_1168_ = lean_int_add(v_x_1164_, v___x_1167_);
    leanh::lean_dec(v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(
    mut v_x_1169_: *mut leanh::LeanObject,
    mut v_y_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Std_Time_instHAddOffsetOffset__7___lam__0(v_x_1169_, v_y_1170_);
    leanh::lean_dec(v_y_1170_);
    leanh::lean_dec(v_x_1169_);
    return v_res_1171_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = leanh::lean_unsigned_to_nat(60000);
    v___x_1175_ = lean_nat_to_int(v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__8___lam__0(
    mut v_x_1176_: *mut leanh::LeanObject,
    mut v_y_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1179_ = lean_int_mul(v_y_1177_, v___x_1178_);
    v___x_1180_ = lean_int_add(v_x_1176_, v___x_1179_);
    leanh::lean_dec(v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(
    mut v_x_1181_: *mut leanh::LeanObject,
    mut v_y_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1183_ = l_Std_Time_instHAddOffsetOffset__8___lam__0(v_x_1181_, v_y_1182_);
    leanh::lean_dec(v_y_1182_);
    leanh::lean_dec(v_x_1181_);
    return v_res_1183_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1186_ = leanh::lean_unsigned_to_nat(3600000);
    v___x_1187_ = lean_nat_to_int(v___x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__9___lam__0(
    mut v_x_1188_: *mut leanh::LeanObject,
    mut v_y_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1191_ = lean_int_mul(v_y_1189_, v___x_1190_);
    v___x_1192_ = lean_int_add(v_x_1188_, v___x_1191_);
    leanh::lean_dec(v___x_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(
    mut v_x_1193_: *mut leanh::LeanObject,
    mut v_y_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Std_Time_instHAddOffsetOffset__9___lam__0(v_x_1193_, v_y_1194_);
    leanh::lean_dec(v_y_1194_);
    leanh::lean_dec(v_x_1193_);
    return v_res_1195_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__10___lam__0(
    mut v_x_1198_: *mut leanh::LeanObject,
    mut v_y_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1201_ = lean_int_mul(v_y_1199_, v___x_1200_);
    v___x_1202_ = lean_int_add(v_x_1198_, v___x_1201_);
    leanh::lean_dec(v___x_1201_);
    return v___x_1202_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(
    mut v_x_1203_: *mut leanh::LeanObject,
    mut v_y_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Std_Time_instHAddOffsetOffset__10___lam__0(v_x_1203_, v_y_1204_);
    leanh::lean_dec(v_y_1204_);
    leanh::lean_dec(v_x_1203_);
    return v_res_1205_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__11___lam__0(
    mut v_x_1208_: *mut leanh::LeanObject,
    mut v_y_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1211_ = lean_int_mul(v_y_1209_, v___x_1210_);
    v___x_1212_ = lean_int_add(v_x_1208_, v___x_1211_);
    leanh::lean_dec(v___x_1211_);
    return v___x_1212_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(
    mut v_x_1213_: *mut leanh::LeanObject,
    mut v_y_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Std_Time_instHAddOffsetOffset__11___lam__0(v_x_1213_, v_y_1214_);
    leanh::lean_dec(v_y_1214_);
    leanh::lean_dec(v_x_1213_);
    return v_res_1215_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__12___lam__0(
    mut v_x_1218_: *mut leanh::LeanObject,
    mut v_y_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1221_ = lean_int_mul(v_x_1218_, v___x_1220_);
    v___x_1222_ = lean_int_add(v___x_1221_, v_y_1219_);
    leanh::lean_dec(v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(
    mut v_x_1223_: *mut leanh::LeanObject,
    mut v_y_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_Time_instHAddOffsetOffset__12___lam__0(v_x_1223_, v_y_1224_);
    leanh::lean_dec(v_y_1224_);
    leanh::lean_dec(v_x_1223_);
    return v_res_1225_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__13___lam__0(
    mut v_x_1228_: *mut leanh::LeanObject,
    mut v_y_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1231_ = lean_int_mul(v_x_1228_, v___x_1230_);
    v___x_1232_ = lean_int_add(v___x_1231_, v_y_1229_);
    leanh::lean_dec(v___x_1231_);
    return v___x_1232_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(
    mut v_x_1233_: *mut leanh::LeanObject,
    mut v_y_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Std_Time_instHAddOffsetOffset__13___lam__0(v_x_1233_, v_y_1234_);
    leanh::lean_dec(v_y_1234_);
    leanh::lean_dec(v_x_1233_);
    return v_res_1235_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = leanh::lean_unsigned_to_nat(60);
    v___x_1240_ = lean_nat_to_int(v___x_1239_);
    return v___x_1240_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__14___lam__0(
    mut v_x_1241_: *mut leanh::LeanObject,
    mut v_y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1244_ = lean_int_mul(v_y_1242_, v___x_1243_);
    v___x_1245_ = lean_int_add(v_x_1241_, v___x_1244_);
    leanh::lean_dec(v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(
    mut v_x_1246_: *mut leanh::LeanObject,
    mut v_y_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_instHAddOffsetOffset__14___lam__0(v_x_1246_, v_y_1247_);
    leanh::lean_dec(v_y_1247_);
    leanh::lean_dec(v_x_1246_);
    return v_res_1248_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = leanh::lean_unsigned_to_nat(3600);
    v___x_1252_ = lean_nat_to_int(v___x_1251_);
    return v___x_1252_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__15___lam__0(
    mut v_x_1253_: *mut leanh::LeanObject,
    mut v_y_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1256_ = lean_int_mul(v_y_1254_, v___x_1255_);
    v___x_1257_ = lean_int_add(v_x_1253_, v___x_1256_);
    leanh::lean_dec(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(
    mut v_x_1258_: *mut leanh::LeanObject,
    mut v_y_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Std_Time_instHAddOffsetOffset__15___lam__0(v_x_1258_, v_y_1259_);
    leanh::lean_dec(v_y_1259_);
    leanh::lean_dec(v_x_1258_);
    return v_res_1260_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__16___lam__0(
    mut v_x_1263_: *mut leanh::LeanObject,
    mut v_y_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1266_ = lean_int_mul(v_y_1264_, v___x_1265_);
    v___x_1267_ = lean_int_add(v_x_1263_, v___x_1266_);
    leanh::lean_dec(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(
    mut v_x_1268_: *mut leanh::LeanObject,
    mut v_y_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Std_Time_instHAddOffsetOffset__16___lam__0(v_x_1268_, v_y_1269_);
    leanh::lean_dec(v_y_1269_);
    leanh::lean_dec(v_x_1268_);
    return v_res_1270_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__17___lam__0(
    mut v_x_1273_: *mut leanh::LeanObject,
    mut v_y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1276_ = lean_int_mul(v_y_1274_, v___x_1275_);
    v___x_1277_ = lean_int_add(v_x_1273_, v___x_1276_);
    leanh::lean_dec(v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(
    mut v_x_1278_: *mut leanh::LeanObject,
    mut v_y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Std_Time_instHAddOffsetOffset__17___lam__0(v_x_1278_, v_y_1279_);
    leanh::lean_dec(v_y_1279_);
    leanh::lean_dec(v_x_1278_);
    return v_res_1280_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__18___lam__0(
    mut v_x_1283_: *mut leanh::LeanObject,
    mut v_y_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1286_ = lean_int_mul(v_x_1283_, v___x_1285_);
    v___x_1287_ = lean_int_add(v___x_1286_, v_y_1284_);
    leanh::lean_dec(v___x_1286_);
    return v___x_1287_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(
    mut v_x_1288_: *mut leanh::LeanObject,
    mut v_y_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Std_Time_instHAddOffsetOffset__18___lam__0(v_x_1288_, v_y_1289_);
    leanh::lean_dec(v_y_1289_);
    leanh::lean_dec(v_x_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__19___lam__0(
    mut v_x_1293_: *mut leanh::LeanObject,
    mut v_y_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1296_ = lean_int_mul(v_x_1293_, v___x_1295_);
    v___x_1297_ = lean_int_add(v___x_1296_, v_y_1294_);
    leanh::lean_dec(v___x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(
    mut v_x_1298_: *mut leanh::LeanObject,
    mut v_y_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Std_Time_instHAddOffsetOffset__19___lam__0(v_x_1298_, v_y_1299_);
    leanh::lean_dec(v_y_1299_);
    leanh::lean_dec(v_x_1298_);
    return v_res_1300_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__20___lam__0(
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v_y_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1306_ = lean_int_mul(v_x_1303_, v___x_1305_);
    v___x_1307_ = lean_int_add(v___x_1306_, v_y_1304_);
    leanh::lean_dec(v___x_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(
    mut v_x_1308_: *mut leanh::LeanObject,
    mut v_y_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Std_Time_instHAddOffsetOffset__20___lam__0(v_x_1308_, v_y_1309_);
    leanh::lean_dec(v_y_1309_);
    leanh::lean_dec(v_x_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__22___lam__0(
    mut v_x_1315_: *mut leanh::LeanObject,
    mut v_y_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1318_ = lean_int_mul(v_y_1316_, v___x_1317_);
    v___x_1319_ = lean_int_add(v_x_1315_, v___x_1318_);
    leanh::lean_dec(v___x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(
    mut v_x_1320_: *mut leanh::LeanObject,
    mut v_y_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_Time_instHAddOffsetOffset__22___lam__0(v_x_1320_, v_y_1321_);
    leanh::lean_dec(v_y_1321_);
    leanh::lean_dec(v_x_1320_);
    return v_res_1322_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__23___lam__0(
    mut v_x_1325_: *mut leanh::LeanObject,
    mut v_y_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1328_ = lean_int_mul(v_y_1326_, v___x_1327_);
    v___x_1329_ = lean_int_add(v_x_1325_, v___x_1328_);
    leanh::lean_dec(v___x_1328_);
    return v___x_1329_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(
    mut v_x_1330_: *mut leanh::LeanObject,
    mut v_y_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Std_Time_instHAddOffsetOffset__23___lam__0(v_x_1330_, v_y_1331_);
    leanh::lean_dec(v_y_1331_);
    leanh::lean_dec(v_x_1330_);
    return v_res_1332_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__24___lam__0(
    mut v_x_1335_: *mut leanh::LeanObject,
    mut v_y_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1338_ = lean_int_mul(v_x_1335_, v___x_1337_);
    v___x_1339_ = lean_int_add(v___x_1338_, v_y_1336_);
    leanh::lean_dec(v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(
    mut v_x_1340_: *mut leanh::LeanObject,
    mut v_y_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Std_Time_instHAddOffsetOffset__24___lam__0(v_x_1340_, v_y_1341_);
    leanh::lean_dec(v_y_1341_);
    leanh::lean_dec(v_x_1340_);
    return v_res_1342_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__25___lam__0(
    mut v_x_1345_: *mut leanh::LeanObject,
    mut v_y_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1348_ = lean_int_mul(v_x_1345_, v___x_1347_);
    v___x_1349_ = lean_int_add(v___x_1348_, v_y_1346_);
    leanh::lean_dec(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(
    mut v_x_1350_: *mut leanh::LeanObject,
    mut v_y_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1352_ = l_Std_Time_instHAddOffsetOffset__25___lam__0(v_x_1350_, v_y_1351_);
    leanh::lean_dec(v_y_1351_);
    leanh::lean_dec(v_x_1350_);
    return v_res_1352_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__26___lam__0(
    mut v_x_1355_: *mut leanh::LeanObject,
    mut v_y_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1358_ = lean_int_mul(v_x_1355_, v___x_1357_);
    v___x_1359_ = lean_int_add(v___x_1358_, v_y_1356_);
    leanh::lean_dec(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(
    mut v_x_1360_: *mut leanh::LeanObject,
    mut v_y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_Time_instHAddOffsetOffset__26___lam__0(v_x_1360_, v_y_1361_);
    leanh::lean_dec(v_y_1361_);
    leanh::lean_dec(v_x_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__28___lam__0(
    mut v_x_1367_: *mut leanh::LeanObject,
    mut v_y_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1370_ = lean_int_mul(v_y_1368_, v___x_1369_);
    v___x_1371_ = lean_int_add(v_x_1367_, v___x_1370_);
    leanh::lean_dec(v___x_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(
    mut v_x_1372_: *mut leanh::LeanObject,
    mut v_y_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Std_Time_instHAddOffsetOffset__28___lam__0(v_x_1372_, v_y_1373_);
    leanh::lean_dec(v_y_1373_);
    leanh::lean_dec(v_x_1372_);
    return v_res_1374_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__29___lam__0(
    mut v_x_1377_: *mut leanh::LeanObject,
    mut v_y_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1380_ = lean_int_mul(v_y_1378_, v___x_1379_);
    v___x_1381_ = lean_int_add(v_x_1377_, v___x_1380_);
    leanh::lean_dec(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(
    mut v_x_1382_: *mut leanh::LeanObject,
    mut v_y_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_Time_instHAddOffsetOffset__29___lam__0(v_x_1382_, v_y_1383_);
    leanh::lean_dec(v_y_1383_);
    leanh::lean_dec(v_x_1382_);
    return v_res_1384_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__30___lam__0(
    mut v_x_1387_: *mut leanh::LeanObject,
    mut v_y_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1390_ = lean_int_mul(v_x_1387_, v___x_1389_);
    v___x_1391_ = lean_int_add(v___x_1390_, v_y_1388_);
    leanh::lean_dec(v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(
    mut v_x_1392_: *mut leanh::LeanObject,
    mut v_y_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Std_Time_instHAddOffsetOffset__30___lam__0(v_x_1392_, v_y_1393_);
    leanh::lean_dec(v_y_1393_);
    leanh::lean_dec(v_x_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__31___lam__0(
    mut v_x_1397_: *mut leanh::LeanObject,
    mut v_y_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1400_ = lean_int_mul(v_x_1397_, v___x_1399_);
    v___x_1401_ = lean_int_add(v___x_1400_, v_y_1398_);
    leanh::lean_dec(v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(
    mut v_x_1402_: *mut leanh::LeanObject,
    mut v_y_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1404_ = l_Std_Time_instHAddOffsetOffset__31___lam__0(v_x_1402_, v_y_1403_);
    leanh::lean_dec(v_y_1403_);
    leanh::lean_dec(v_x_1402_);
    return v_res_1404_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__32___lam__0(
    mut v_x_1407_: *mut leanh::LeanObject,
    mut v_y_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1410_ = lean_int_mul(v_x_1407_, v___x_1409_);
    v___x_1411_ = lean_int_add(v___x_1410_, v_y_1408_);
    leanh::lean_dec(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(
    mut v_x_1412_: *mut leanh::LeanObject,
    mut v_y_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Std_Time_instHAddOffsetOffset__32___lam__0(v_x_1412_, v_y_1413_);
    leanh::lean_dec(v_y_1413_);
    leanh::lean_dec(v_x_1412_);
    return v_res_1414_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__33___lam__0(
    mut v_x_1417_: *mut leanh::LeanObject,
    mut v_y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1420_ = lean_int_mul(v_x_1417_, v___x_1419_);
    v___x_1421_ = lean_int_add(v___x_1420_, v_y_1418_);
    leanh::lean_dec(v___x_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(
    mut v_x_1422_: *mut leanh::LeanObject,
    mut v_y_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Std_Time_instHAddOffsetOffset__33___lam__0(v_x_1422_, v_y_1423_);
    leanh::lean_dec(v_y_1423_);
    leanh::lean_dec(v_x_1422_);
    return v_res_1424_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__34___lam__0(
    mut v_x_1427_: *mut leanh::LeanObject,
    mut v_y_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1430_ = lean_int_mul(v_x_1427_, v___x_1429_);
    v___x_1431_ = lean_int_add(v___x_1430_, v_y_1428_);
    leanh::lean_dec(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v_y_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Std_Time_instHAddOffsetOffset__34___lam__0(v_x_1432_, v_y_1433_);
    leanh::lean_dec(v_y_1433_);
    leanh::lean_dec(v_x_1432_);
    return v_res_1434_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_unsigned_to_nat(7);
    v___x_1439_ = lean_nat_to_int(v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__35___lam__0(
    mut v_x_1440_: *mut leanh::LeanObject,
    mut v_y_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1443_ = lean_int_mul(v_y_1441_, v___x_1442_);
    v___x_1444_ = lean_int_add(v_x_1440_, v___x_1443_);
    leanh::lean_dec(v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(
    mut v_x_1445_: *mut leanh::LeanObject,
    mut v_y_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Std_Time_instHAddOffsetOffset__35___lam__0(v_x_1445_, v_y_1446_);
    leanh::lean_dec(v_y_1446_);
    leanh::lean_dec(v_x_1445_);
    return v_res_1447_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__36___lam__0(
    mut v_x_1450_: *mut leanh::LeanObject,
    mut v_y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1453_ = lean_int_mul(v_x_1450_, v___x_1452_);
    v___x_1454_ = lean_int_add(v___x_1453_, v_y_1451_);
    leanh::lean_dec(v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_y_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1457_ = l_Std_Time_instHAddOffsetOffset__36___lam__0(v_x_1455_, v_y_1456_);
    leanh::lean_dec(v_y_1456_);
    leanh::lean_dec(v_x_1455_);
    return v_res_1457_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__37___lam__0(
    mut v_x_1460_: *mut leanh::LeanObject,
    mut v_y_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1463_ = lean_int_mul(v_x_1460_, v___x_1462_);
    v___x_1464_ = lean_int_add(v___x_1463_, v_y_1461_);
    leanh::lean_dec(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(
    mut v_x_1465_: *mut leanh::LeanObject,
    mut v_y_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Std_Time_instHAddOffsetOffset__37___lam__0(v_x_1465_, v_y_1466_);
    leanh::lean_dec(v_y_1466_);
    leanh::lean_dec(v_x_1465_);
    return v_res_1467_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__38___lam__0(
    mut v_x_1470_: *mut leanh::LeanObject,
    mut v_y_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1473_ = lean_int_mul(v_x_1470_, v___x_1472_);
    v___x_1474_ = lean_int_add(v___x_1473_, v_y_1471_);
    leanh::lean_dec(v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(
    mut v_x_1475_: *mut leanh::LeanObject,
    mut v_y_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_Std_Time_instHAddOffsetOffset__38___lam__0(v_x_1475_, v_y_1476_);
    leanh::lean_dec(v_y_1476_);
    leanh::lean_dec(v_x_1475_);
    return v_res_1477_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__39___lam__0(
    mut v_x_1480_: *mut leanh::LeanObject,
    mut v_y_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1483_ = lean_int_mul(v_x_1480_, v___x_1482_);
    v___x_1484_ = lean_int_add(v___x_1483_, v_y_1481_);
    leanh::lean_dec(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(
    mut v_x_1485_: *mut leanh::LeanObject,
    mut v_y_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Std_Time_instHAddOffsetOffset__39___lam__0(v_x_1485_, v_y_1486_);
    leanh::lean_dec(v_y_1486_);
    leanh::lean_dec(v_x_1485_);
    return v_res_1487_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__40___lam__0(
    mut v_x_1490_: *mut leanh::LeanObject,
    mut v_y_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1493_ = lean_int_mul(v_x_1490_, v___x_1492_);
    v___x_1494_ = lean_int_add(v___x_1493_, v_y_1491_);
    leanh::lean_dec(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(
    mut v_x_1495_: *mut leanh::LeanObject,
    mut v_y_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1497_ = l_Std_Time_instHAddOffsetOffset__40___lam__0(v_x_1495_, v_y_1496_);
    leanh::lean_dec(v_y_1496_);
    leanh::lean_dec(v_x_1495_);
    return v_res_1497_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__41___lam__0(
    mut v_x_1500_: *mut leanh::LeanObject,
    mut v_y_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1503_ = lean_int_mul(v_x_1500_, v___x_1502_);
    v___x_1504_ = lean_int_add(v___x_1503_, v_y_1501_);
    leanh::lean_dec(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(
    mut v_x_1505_: *mut leanh::LeanObject,
    mut v_y_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1507_ = l_Std_Time_instHAddOffsetOffset__41___lam__0(v_x_1505_, v_y_1506_);
    leanh::lean_dec(v_y_1506_);
    leanh::lean_dec(v_x_1505_);
    return v_res_1507_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset___lam__0(
    mut v_x_1513_: *mut leanh::LeanObject,
    mut v_y_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1516_ = lean_int_mul(v_y_1514_, v___x_1515_);
    v___x_1517_ = lean_int_sub(v_x_1513_, v___x_1516_);
    leanh::lean_dec(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset___lam__0___boxed(
    mut v_x_1518_: *mut leanh::LeanObject,
    mut v_y_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_Std_Time_instHSubOffsetOffset___lam__0(v_x_1518_, v_y_1519_);
    leanh::lean_dec(v_y_1519_);
    leanh::lean_dec(v_x_1518_);
    return v_res_1520_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__1___lam__0(
    mut v_x_1523_: *mut leanh::LeanObject,
    mut v_y_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1526_ = lean_int_mul(v_y_1524_, v___x_1525_);
    v___x_1527_ = lean_int_sub(v_x_1523_, v___x_1526_);
    leanh::lean_dec(v___x_1526_);
    return v___x_1527_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(
    mut v_x_1528_: *mut leanh::LeanObject,
    mut v_y_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Std_Time_instHSubOffsetOffset__1___lam__0(v_x_1528_, v_y_1529_);
    leanh::lean_dec(v_y_1529_);
    leanh::lean_dec(v_x_1528_);
    return v_res_1530_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__2___lam__0(
    mut v_x_1533_: *mut leanh::LeanObject,
    mut v_y_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1536_ = lean_int_mul(v_y_1534_, v___x_1535_);
    v___x_1537_ = lean_int_sub(v_x_1533_, v___x_1536_);
    leanh::lean_dec(v___x_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(
    mut v_x_1538_: *mut leanh::LeanObject,
    mut v_y_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Std_Time_instHSubOffsetOffset__2___lam__0(v_x_1538_, v_y_1539_);
    leanh::lean_dec(v_y_1539_);
    leanh::lean_dec(v_x_1538_);
    return v_res_1540_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__3___lam__0(
    mut v_x_1543_: *mut leanh::LeanObject,
    mut v_y_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1546_ = lean_int_mul(v_y_1544_, v___x_1545_);
    v___x_1547_ = lean_int_sub(v_x_1543_, v___x_1546_);
    leanh::lean_dec(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(
    mut v_x_1548_: *mut leanh::LeanObject,
    mut v_y_1549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Std_Time_instHSubOffsetOffset__3___lam__0(v_x_1548_, v_y_1549_);
    leanh::lean_dec(v_y_1549_);
    leanh::lean_dec(v_x_1548_);
    return v_res_1550_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__4___lam__0(
    mut v_x_1553_: *mut leanh::LeanObject,
    mut v_y_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1556_ = lean_int_mul(v_y_1554_, v___x_1555_);
    v___x_1557_ = lean_int_sub(v_x_1553_, v___x_1556_);
    leanh::lean_dec(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(
    mut v_x_1558_: *mut leanh::LeanObject,
    mut v_y_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Std_Time_instHSubOffsetOffset__4___lam__0(v_x_1558_, v_y_1559_);
    leanh::lean_dec(v_y_1559_);
    leanh::lean_dec(v_x_1558_);
    return v_res_1560_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__5___lam__0(
    mut v_x_1563_: *mut leanh::LeanObject,
    mut v_y_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1565_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1566_ = lean_int_mul(v_y_1564_, v___x_1565_);
    v___x_1567_ = lean_int_sub(v_x_1563_, v___x_1566_);
    leanh::lean_dec(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(
    mut v_x_1568_: *mut leanh::LeanObject,
    mut v_y_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_Time_instHSubOffsetOffset__5___lam__0(v_x_1568_, v_y_1569_);
    leanh::lean_dec(v_y_1569_);
    leanh::lean_dec(v_x_1568_);
    return v_res_1570_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__6___lam__0(
    mut v_x_1573_: *mut leanh::LeanObject,
    mut v_y_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1576_ = lean_int_mul(v_x_1573_, v___x_1575_);
    v___x_1577_ = lean_int_sub(v___x_1576_, v_y_1574_);
    leanh::lean_dec(v___x_1576_);
    return v___x_1577_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(
    mut v_x_1578_: *mut leanh::LeanObject,
    mut v_y_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1580_ = l_Std_Time_instHSubOffsetOffset__6___lam__0(v_x_1578_, v_y_1579_);
    leanh::lean_dec(v_y_1579_);
    leanh::lean_dec(v_x_1578_);
    return v_res_1580_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__7___lam__0(
    mut v_x_1584_: *mut leanh::LeanObject,
    mut v_y_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1587_ = lean_int_mul(v_y_1585_, v___x_1586_);
    v___x_1588_ = lean_int_sub(v_x_1584_, v___x_1587_);
    leanh::lean_dec(v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_y_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Std_Time_instHSubOffsetOffset__7___lam__0(v_x_1589_, v_y_1590_);
    leanh::lean_dec(v_y_1590_);
    leanh::lean_dec(v_x_1589_);
    return v_res_1591_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__8___lam__0(
    mut v_x_1594_: *mut leanh::LeanObject,
    mut v_y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1596_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1597_ = lean_int_mul(v_y_1595_, v___x_1596_);
    v___x_1598_ = lean_int_sub(v_x_1594_, v___x_1597_);
    leanh::lean_dec(v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(
    mut v_x_1599_: *mut leanh::LeanObject,
    mut v_y_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Std_Time_instHSubOffsetOffset__8___lam__0(v_x_1599_, v_y_1600_);
    leanh::lean_dec(v_y_1600_);
    leanh::lean_dec(v_x_1599_);
    return v_res_1601_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__9___lam__0(
    mut v_x_1604_: *mut leanh::LeanObject,
    mut v_y_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1607_ = lean_int_mul(v_y_1605_, v___x_1606_);
    v___x_1608_ = lean_int_sub(v_x_1604_, v___x_1607_);
    leanh::lean_dec(v___x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(
    mut v_x_1609_: *mut leanh::LeanObject,
    mut v_y_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_Time_instHSubOffsetOffset__9___lam__0(v_x_1609_, v_y_1610_);
    leanh::lean_dec(v_y_1610_);
    leanh::lean_dec(v_x_1609_);
    return v_res_1611_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__10___lam__0(
    mut v_x_1614_: *mut leanh::LeanObject,
    mut v_y_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1616_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1617_ = lean_int_mul(v_y_1615_, v___x_1616_);
    v___x_1618_ = lean_int_sub(v_x_1614_, v___x_1617_);
    leanh::lean_dec(v___x_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(
    mut v_x_1619_: *mut leanh::LeanObject,
    mut v_y_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Std_Time_instHSubOffsetOffset__10___lam__0(v_x_1619_, v_y_1620_);
    leanh::lean_dec(v_y_1620_);
    leanh::lean_dec(v_x_1619_);
    return v_res_1621_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__11___lam__0(
    mut v_x_1624_: *mut leanh::LeanObject,
    mut v_y_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1627_ = lean_int_mul(v_y_1625_, v___x_1626_);
    v___x_1628_ = lean_int_sub(v_x_1624_, v___x_1627_);
    leanh::lean_dec(v___x_1627_);
    return v___x_1628_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_y_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Std_Time_instHSubOffsetOffset__11___lam__0(v_x_1629_, v_y_1630_);
    leanh::lean_dec(v_y_1630_);
    leanh::lean_dec(v_x_1629_);
    return v_res_1631_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__12___lam__0(
    mut v_x_1634_: *mut leanh::LeanObject,
    mut v_y_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1636_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1637_ = lean_int_mul(v_x_1634_, v___x_1636_);
    v___x_1638_ = lean_int_sub(v___x_1637_, v_y_1635_);
    leanh::lean_dec(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(
    mut v_x_1639_: *mut leanh::LeanObject,
    mut v_y_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1641_ = l_Std_Time_instHSubOffsetOffset__12___lam__0(v_x_1639_, v_y_1640_);
    leanh::lean_dec(v_y_1640_);
    leanh::lean_dec(v_x_1639_);
    return v_res_1641_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__13___lam__0(
    mut v_x_1644_: *mut leanh::LeanObject,
    mut v_y_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1647_ = lean_int_mul(v_x_1644_, v___x_1646_);
    v___x_1648_ = lean_int_sub(v___x_1647_, v_y_1645_);
    leanh::lean_dec(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v_y_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Std_Time_instHSubOffsetOffset__13___lam__0(v_x_1649_, v_y_1650_);
    leanh::lean_dec(v_y_1650_);
    leanh::lean_dec(v_x_1649_);
    return v_res_1651_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__14___lam__0(
    mut v_x_1655_: *mut leanh::LeanObject,
    mut v_y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1658_ = lean_int_mul(v_y_1656_, v___x_1657_);
    v___x_1659_ = lean_int_sub(v_x_1655_, v___x_1658_);
    leanh::lean_dec(v___x_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(
    mut v_x_1660_: *mut leanh::LeanObject,
    mut v_y_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_Time_instHSubOffsetOffset__14___lam__0(v_x_1660_, v_y_1661_);
    leanh::lean_dec(v_y_1661_);
    leanh::lean_dec(v_x_1660_);
    return v_res_1662_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__15___lam__0(
    mut v_x_1665_: *mut leanh::LeanObject,
    mut v_y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1668_ = lean_int_mul(v_y_1666_, v___x_1667_);
    v___x_1669_ = lean_int_sub(v_x_1665_, v___x_1668_);
    leanh::lean_dec(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(
    mut v_x_1670_: *mut leanh::LeanObject,
    mut v_y_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Std_Time_instHSubOffsetOffset__15___lam__0(v_x_1670_, v_y_1671_);
    leanh::lean_dec(v_y_1671_);
    leanh::lean_dec(v_x_1670_);
    return v_res_1672_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__16___lam__0(
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v_y_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1678_ = lean_int_mul(v_y_1676_, v___x_1677_);
    v___x_1679_ = lean_int_sub(v_x_1675_, v___x_1678_);
    leanh::lean_dec(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(
    mut v_x_1680_: *mut leanh::LeanObject,
    mut v_y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Std_Time_instHSubOffsetOffset__16___lam__0(v_x_1680_, v_y_1681_);
    leanh::lean_dec(v_y_1681_);
    leanh::lean_dec(v_x_1680_);
    return v_res_1682_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__17___lam__0(
    mut v_x_1685_: *mut leanh::LeanObject,
    mut v_y_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1688_ = lean_int_mul(v_y_1686_, v___x_1687_);
    v___x_1689_ = lean_int_sub(v_x_1685_, v___x_1688_);
    leanh::lean_dec(v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(
    mut v_x_1690_: *mut leanh::LeanObject,
    mut v_y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Std_Time_instHSubOffsetOffset__17___lam__0(v_x_1690_, v_y_1691_);
    leanh::lean_dec(v_y_1691_);
    leanh::lean_dec(v_x_1690_);
    return v_res_1692_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__18___lam__0(
    mut v_x_1695_: *mut leanh::LeanObject,
    mut v_y_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1698_ = lean_int_mul(v_x_1695_, v___x_1697_);
    v___x_1699_ = lean_int_sub(v___x_1698_, v_y_1696_);
    leanh::lean_dec(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(
    mut v_x_1700_: *mut leanh::LeanObject,
    mut v_y_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Std_Time_instHSubOffsetOffset__18___lam__0(v_x_1700_, v_y_1701_);
    leanh::lean_dec(v_y_1701_);
    leanh::lean_dec(v_x_1700_);
    return v_res_1702_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__19___lam__0(
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v_y_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1708_ = lean_int_mul(v_x_1705_, v___x_1707_);
    v___x_1709_ = lean_int_sub(v___x_1708_, v_y_1706_);
    leanh::lean_dec(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(
    mut v_x_1710_: *mut leanh::LeanObject,
    mut v_y_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Std_Time_instHSubOffsetOffset__19___lam__0(v_x_1710_, v_y_1711_);
    leanh::lean_dec(v_y_1711_);
    leanh::lean_dec(v_x_1710_);
    return v_res_1712_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__20___lam__0(
    mut v_x_1715_: *mut leanh::LeanObject,
    mut v_y_1716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1718_ = lean_int_mul(v_x_1715_, v___x_1717_);
    v___x_1719_ = lean_int_sub(v___x_1718_, v_y_1716_);
    leanh::lean_dec(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(
    mut v_x_1720_: *mut leanh::LeanObject,
    mut v_y_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Std_Time_instHSubOffsetOffset__20___lam__0(v_x_1720_, v_y_1721_);
    leanh::lean_dec(v_y_1721_);
    leanh::lean_dec(v_x_1720_);
    return v_res_1722_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__22___lam__0(
    mut v_x_1727_: *mut leanh::LeanObject,
    mut v_y_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1730_ = lean_int_mul(v_y_1728_, v___x_1729_);
    v___x_1731_ = lean_int_sub(v_x_1727_, v___x_1730_);
    leanh::lean_dec(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(
    mut v_x_1732_: *mut leanh::LeanObject,
    mut v_y_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Time_instHSubOffsetOffset__22___lam__0(v_x_1732_, v_y_1733_);
    leanh::lean_dec(v_y_1733_);
    leanh::lean_dec(v_x_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__23___lam__0(
    mut v_x_1737_: *mut leanh::LeanObject,
    mut v_y_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1740_ = lean_int_mul(v_y_1738_, v___x_1739_);
    v___x_1741_ = lean_int_sub(v_x_1737_, v___x_1740_);
    leanh::lean_dec(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(
    mut v_x_1742_: *mut leanh::LeanObject,
    mut v_y_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Std_Time_instHSubOffsetOffset__23___lam__0(v_x_1742_, v_y_1743_);
    leanh::lean_dec(v_y_1743_);
    leanh::lean_dec(v_x_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__24___lam__0(
    mut v_x_1747_: *mut leanh::LeanObject,
    mut v_y_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1750_ = lean_int_mul(v_x_1747_, v___x_1749_);
    v___x_1751_ = lean_int_sub(v___x_1750_, v_y_1748_);
    leanh::lean_dec(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(
    mut v_x_1752_: *mut leanh::LeanObject,
    mut v_y_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Std_Time_instHSubOffsetOffset__24___lam__0(v_x_1752_, v_y_1753_);
    leanh::lean_dec(v_y_1753_);
    leanh::lean_dec(v_x_1752_);
    return v_res_1754_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__25___lam__0(
    mut v_x_1757_: *mut leanh::LeanObject,
    mut v_y_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1760_ = lean_int_mul(v_x_1757_, v___x_1759_);
    v___x_1761_ = lean_int_sub(v___x_1760_, v_y_1758_);
    leanh::lean_dec(v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(
    mut v_x_1762_: *mut leanh::LeanObject,
    mut v_y_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Std_Time_instHSubOffsetOffset__25___lam__0(v_x_1762_, v_y_1763_);
    leanh::lean_dec(v_y_1763_);
    leanh::lean_dec(v_x_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__26___lam__0(
    mut v_x_1767_: *mut leanh::LeanObject,
    mut v_y_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1770_ = lean_int_mul(v_x_1767_, v___x_1769_);
    v___x_1771_ = lean_int_sub(v___x_1770_, v_y_1768_);
    leanh::lean_dec(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(
    mut v_x_1772_: *mut leanh::LeanObject,
    mut v_y_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Std_Time_instHSubOffsetOffset__26___lam__0(v_x_1772_, v_y_1773_);
    leanh::lean_dec(v_y_1773_);
    leanh::lean_dec(v_x_1772_);
    return v_res_1774_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__28___lam__0(
    mut v_x_1779_: *mut leanh::LeanObject,
    mut v_y_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1782_ = lean_int_mul(v_y_1780_, v___x_1781_);
    v___x_1783_ = lean_int_sub(v_x_1779_, v___x_1782_);
    leanh::lean_dec(v___x_1782_);
    return v___x_1783_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(
    mut v_x_1784_: *mut leanh::LeanObject,
    mut v_y_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_Time_instHSubOffsetOffset__28___lam__0(v_x_1784_, v_y_1785_);
    leanh::lean_dec(v_y_1785_);
    leanh::lean_dec(v_x_1784_);
    return v_res_1786_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__29___lam__0(
    mut v_x_1789_: *mut leanh::LeanObject,
    mut v_y_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1792_ = lean_int_mul(v_y_1790_, v___x_1791_);
    v___x_1793_ = lean_int_sub(v_x_1789_, v___x_1792_);
    leanh::lean_dec(v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_y_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Std_Time_instHSubOffsetOffset__29___lam__0(v_x_1794_, v_y_1795_);
    leanh::lean_dec(v_y_1795_);
    leanh::lean_dec(v_x_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__30___lam__0(
    mut v_x_1799_: *mut leanh::LeanObject,
    mut v_y_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1802_ = lean_int_mul(v_x_1799_, v___x_1801_);
    v___x_1803_ = lean_int_sub(v___x_1802_, v_y_1800_);
    leanh::lean_dec(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(
    mut v_x_1804_: *mut leanh::LeanObject,
    mut v_y_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Std_Time_instHSubOffsetOffset__30___lam__0(v_x_1804_, v_y_1805_);
    leanh::lean_dec(v_y_1805_);
    leanh::lean_dec(v_x_1804_);
    return v_res_1806_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__31___lam__0(
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v_y_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1812_ = lean_int_mul(v_x_1809_, v___x_1811_);
    v___x_1813_ = lean_int_sub(v___x_1812_, v_y_1810_);
    leanh::lean_dec(v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(
    mut v_x_1814_: *mut leanh::LeanObject,
    mut v_y_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_Time_instHSubOffsetOffset__31___lam__0(v_x_1814_, v_y_1815_);
    leanh::lean_dec(v_y_1815_);
    leanh::lean_dec(v_x_1814_);
    return v_res_1816_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__32___lam__0(
    mut v_x_1819_: *mut leanh::LeanObject,
    mut v_y_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1822_ = lean_int_mul(v_x_1819_, v___x_1821_);
    v___x_1823_ = lean_int_sub(v___x_1822_, v_y_1820_);
    leanh::lean_dec(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(
    mut v_x_1824_: *mut leanh::LeanObject,
    mut v_y_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_Time_instHSubOffsetOffset__32___lam__0(v_x_1824_, v_y_1825_);
    leanh::lean_dec(v_y_1825_);
    leanh::lean_dec(v_x_1824_);
    return v_res_1826_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__33___lam__0(
    mut v_x_1829_: *mut leanh::LeanObject,
    mut v_y_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1832_ = lean_int_mul(v_x_1829_, v___x_1831_);
    v___x_1833_ = lean_int_sub(v___x_1832_, v_y_1830_);
    leanh::lean_dec(v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(
    mut v_x_1834_: *mut leanh::LeanObject,
    mut v_y_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_Time_instHSubOffsetOffset__33___lam__0(v_x_1834_, v_y_1835_);
    leanh::lean_dec(v_y_1835_);
    leanh::lean_dec(v_x_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__34___lam__0(
    mut v_x_1839_: *mut leanh::LeanObject,
    mut v_y_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1842_ = lean_int_mul(v_x_1839_, v___x_1841_);
    v___x_1843_ = lean_int_sub(v___x_1842_, v_y_1840_);
    leanh::lean_dec(v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(
    mut v_x_1844_: *mut leanh::LeanObject,
    mut v_y_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Std_Time_instHSubOffsetOffset__34___lam__0(v_x_1844_, v_y_1845_);
    leanh::lean_dec(v_y_1845_);
    leanh::lean_dec(v_x_1844_);
    return v_res_1846_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__35___lam__0(
    mut v_x_1850_: *mut leanh::LeanObject,
    mut v_y_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1853_ = lean_int_mul(v_y_1851_, v___x_1852_);
    v___x_1854_ = lean_int_sub(v_x_1850_, v___x_1853_);
    leanh::lean_dec(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(
    mut v_x_1855_: *mut leanh::LeanObject,
    mut v_y_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_Time_instHSubOffsetOffset__35___lam__0(v_x_1855_, v_y_1856_);
    leanh::lean_dec(v_y_1856_);
    leanh::lean_dec(v_x_1855_);
    return v_res_1857_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__36___lam__0(
    mut v_x_1860_: *mut leanh::LeanObject,
    mut v_y_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1863_ = lean_int_mul(v_x_1860_, v___x_1862_);
    v___x_1864_ = lean_int_sub(v___x_1863_, v_y_1861_);
    leanh::lean_dec(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(
    mut v_x_1865_: *mut leanh::LeanObject,
    mut v_y_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Std_Time_instHSubOffsetOffset__36___lam__0(v_x_1865_, v_y_1866_);
    leanh::lean_dec(v_y_1866_);
    leanh::lean_dec(v_x_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__37___lam__0(
    mut v_x_1870_: *mut leanh::LeanObject,
    mut v_y_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1873_ = lean_int_mul(v_x_1870_, v___x_1872_);
    v___x_1874_ = lean_int_sub(v___x_1873_, v_y_1871_);
    leanh::lean_dec(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(
    mut v_x_1875_: *mut leanh::LeanObject,
    mut v_y_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Std_Time_instHSubOffsetOffset__37___lam__0(v_x_1875_, v_y_1876_);
    leanh::lean_dec(v_y_1876_);
    leanh::lean_dec(v_x_1875_);
    return v_res_1877_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__38___lam__0(
    mut v_x_1880_: *mut leanh::LeanObject,
    mut v_y_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1883_ = lean_int_mul(v_x_1880_, v___x_1882_);
    v___x_1884_ = lean_int_sub(v___x_1883_, v_y_1881_);
    leanh::lean_dec(v___x_1883_);
    return v___x_1884_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(
    mut v_x_1885_: *mut leanh::LeanObject,
    mut v_y_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Std_Time_instHSubOffsetOffset__38___lam__0(v_x_1885_, v_y_1886_);
    leanh::lean_dec(v_y_1886_);
    leanh::lean_dec(v_x_1885_);
    return v_res_1887_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__39___lam__0(
    mut v_x_1890_: *mut leanh::LeanObject,
    mut v_y_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1893_ = lean_int_mul(v_x_1890_, v___x_1892_);
    v___x_1894_ = lean_int_sub(v___x_1893_, v_y_1891_);
    leanh::lean_dec(v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(
    mut v_x_1895_: *mut leanh::LeanObject,
    mut v_y_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Std_Time_instHSubOffsetOffset__39___lam__0(v_x_1895_, v_y_1896_);
    leanh::lean_dec(v_y_1896_);
    leanh::lean_dec(v_x_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__40___lam__0(
    mut v_x_1900_: *mut leanh::LeanObject,
    mut v_y_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1903_ = lean_int_mul(v_x_1900_, v___x_1902_);
    v___x_1904_ = lean_int_sub(v___x_1903_, v_y_1901_);
    leanh::lean_dec(v___x_1903_);
    return v___x_1904_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(
    mut v_x_1905_: *mut leanh::LeanObject,
    mut v_y_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1907_ = l_Std_Time_instHSubOffsetOffset__40___lam__0(v_x_1905_, v_y_1906_);
    leanh::lean_dec(v_y_1906_);
    leanh::lean_dec(v_x_1905_);
    return v_res_1907_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__41___lam__0(
    mut v_x_1910_: *mut leanh::LeanObject,
    mut v_y_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1913_ = lean_int_mul(v_x_1910_, v___x_1912_);
    v___x_1914_ = lean_int_sub(v___x_1913_, v_y_1911_);
    leanh::lean_dec(v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(
    mut v_x_1915_: *mut leanh::LeanObject,
    mut v_y_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Std_Time_instHSubOffsetOffset__41___lam__0(v_x_1915_, v_y_1916_);
    leanh::lean_dec(v_y_1916_);
    leanh::lean_dec(v_x_1915_);
    return v_res_1917_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_ValidDate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_ValidDate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Basic(builtin);
}