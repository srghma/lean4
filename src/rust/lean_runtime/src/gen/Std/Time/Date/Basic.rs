// Lean compiler output
// Module: Std.Time.Date.Basic
// Imports: Std.Time.Date.Unit.Basic Std.Time.Date.ValidDate
use crate::r#gen::Init::Data::Int::Basic::{l_Int_add___boxed, l_Int_sub___boxed};
use crate::r#gen::Std::Time::Date::Unit::Basic::{
    initialize_Std_Time_Date_Unit_Basic, runtime_initialize_Std_Time_Date_Unit_Basic,
};
use crate::r#gen::Std::Time::Date::ValidDate::{
    initialize_Std_Time_Date_ValidDate, runtime_initialize_Std_Time_Date_ValidDate,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_mul, lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_div;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_cstr_to_nat, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Nanosecond_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toWeeks___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_Offset_toDays___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_Offset_toWeeks___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_Offset_toDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_Offset_toWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Minute_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_Offset_toDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Minute_Offset_toWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_Offset_toWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_Offset_toDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_Offset_toWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_Offset_toWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instHAddOffset___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instHAddOffsetOffset___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__1___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__1___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__2___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__2___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__3___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__3___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__4___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__4___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__5___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__5___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__6___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__6___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__7___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__7___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__7___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__8___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__8___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__8___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__9___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__9___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__9___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__9___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__10___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__10___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__10___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__10___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__11___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__11___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__11___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__11___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__12___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__12___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__12___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__12___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__13___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__13___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__13___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__13___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__14___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__14___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__15___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__15___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__15___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__15___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__16___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__16___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__16___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__17___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__17___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__17___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__17___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__18___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__18___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__18___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__18___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__19___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__19___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__19___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__19___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__20___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__20___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__14___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__22___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__22___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__22___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__22___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__23___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__23___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__23___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__23___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__24___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__24___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__24___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__24___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__25___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__25___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__25___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__25: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__25___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__26___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__26___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__26___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__26___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__27: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__28___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__28___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__28___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__28: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__28___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__29___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__29___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__29___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__29___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__30___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__30___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__30___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__30: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__30___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__31___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__31___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__31___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__31: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__31___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__32___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__32___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__32: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__32___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__33___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__33___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__33___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__33: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__33___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__34___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__34___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__34___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__34: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__34___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instHAddOffsetOffset__35___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__35___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__35___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__35: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__35___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__36___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__36___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__36___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__36: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__36___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__37___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__37___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__37___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__37: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__37___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__38___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__38___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__38___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__38: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__38___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__39___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__39___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__39___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__39: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__39___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__40___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__40___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__40___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__40: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__40___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHAddOffsetOffset__41___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHAddOffsetOffset__41___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__41___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffsetOffset__41: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffsetOffset__41___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHAddOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffset___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instHSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__1___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__2___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__2___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__3___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__3___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__4___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__4___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__5___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__5___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__6___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__6___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__7___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__7___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__7___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__8___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__8___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__8___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__9___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__9___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__9___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__9___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__10___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__10___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__10___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__10___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__11___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__11___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__11___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__11___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__12___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__12___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__12___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__12___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__13___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__13___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__13___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__13___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__14___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__14___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__15___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__15___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__15___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__15___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__16___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__16___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__16___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__17___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__17___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__17___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__17___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__18___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__18___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__18___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__18___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__19___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__19___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__19___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__19___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__20___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__20___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__14___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__22___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__22___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__22___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__22___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__23___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__23___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__23___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__23___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__24___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__24___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__24___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__24___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__25___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__25___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__25___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__25: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__25___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__26___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__26___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__26___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__26___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__27: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__20___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__28___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__28___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__28___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__28: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__28___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__29___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__29___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__29___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__29___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__30___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__30___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__30___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__30: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__30___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__31___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__31___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__31___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__31: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__31___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__32___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__32___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__32: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__32___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__33___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__33___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__33___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__33: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__33___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__34___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__34___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__34___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__34: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__34___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__35___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__35___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__35___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__35: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__35___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__36___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__36___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__36___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__36: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__36___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__37___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__37___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__37___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__37: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__37___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__38___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__38___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__38___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__38: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__38___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__39___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__39___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__39___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__39: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__39___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__40___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__40___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__40___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__40: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__40___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instHSubOffsetOffset__41___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instHSubOffsetOffset__41___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__41___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffsetOffset__41: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffsetOffset__41___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instHSubOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instHSubOffset___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = lean_cstr_to_nat(b"86400000000000\0".as_ptr().cast());
    v___x_962_ = lean_nat_to_int(v___x_961_);
    return v___x_962_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toDays(
    mut v_nanoseconds_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    v___x_964_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_965_ = lean_int_div(v_nanoseconds_963_, v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toDays___boxed(
    mut v_nanoseconds_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_967_: *mut LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Std_Time_Nanosecond_Offset_toDays(v_nanoseconds_966_);
    lean_dec(v_nanoseconds_966_);
    return v_res_967_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofDays(
    mut v_days_968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_969_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_970_ = lean_int_mul(v_days_968_, v___x_969_);
    return v___x_970_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofDays___boxed(
    mut v_days_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_972_: *mut LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Std_Time_Nanosecond_Offset_ofDays(v_days_971_);
    lean_dec(v_days_971_);
    return v_res_972_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_cstr_to_nat(b"604800000000000\0".as_ptr().cast());
    v___x_974_ = lean_nat_to_int(v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toWeeks(
    mut v_nanoseconds_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_977_ = lean_int_div(v_nanoseconds_975_, v___x_976_);
    return v___x_977_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toWeeks___boxed(
    mut v_nanoseconds_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_979_: *mut LeanObject = core::ptr::null_mut();
    v_res_979_ = l_Std_Time_Nanosecond_Offset_toWeeks(v_nanoseconds_978_);
    lean_dec(v_nanoseconds_978_);
    return v_res_979_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofWeeks(
    mut v_weeks_980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_982_ = lean_int_mul(v_weeks_980_, v___x_981_);
    return v___x_982_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofWeeks___boxed(
    mut v_weeks_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_984_: *mut LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Std_Time_Nanosecond_Offset_ofWeeks(v_weeks_983_);
    lean_dec(v_weeks_983_);
    return v_res_984_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = lean_unsigned_to_nat(86400000);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toDays(
    mut v_milliseconds_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v___x_988_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_989_ = lean_int_div(v_milliseconds_987_, v___x_988_);
    return v___x_989_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toDays___boxed(
    mut v_milliseconds_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_991_: *mut LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Std_Time_Millisecond_Offset_toDays(v_milliseconds_990_);
    lean_dec(v_milliseconds_990_);
    return v_res_991_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofDays(
    mut v_days_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_993_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_994_ = lean_int_mul(v_days_992_, v___x_993_);
    return v___x_994_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofDays___boxed(
    mut v_days_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_996_: *mut LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Std_Time_Millisecond_Offset_ofDays(v_days_995_);
    lean_dec(v_days_995_);
    return v_res_996_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v___x_997_ = lean_unsigned_to_nat(604800000);
    v___x_998_ = lean_nat_to_int(v___x_997_);
    return v___x_998_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toWeeks(
    mut v_milliseconds_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1001_ = lean_int_div(v_milliseconds_999_, v___x_1000_);
    return v___x_1001_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toWeeks___boxed(
    mut v_milliseconds_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_Std_Time_Millisecond_Offset_toWeeks(v_milliseconds_1002_);
    lean_dec(v_milliseconds_1002_);
    return v_res_1003_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofWeeks(
    mut v_weeks_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1005_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1006_ = lean_int_mul(v_weeks_1004_, v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofWeeks___boxed(
    mut v_weeks_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Std_Time_Millisecond_Offset_ofWeeks(v_weeks_1007_);
    lean_dec(v_weeks_1007_);
    return v_res_1008_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_unsigned_to_nat(86400);
    v___x_1010_ = lean_nat_to_int(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn l_Std_Time_Second_Offset_toDays(
    mut v_seconds_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1012_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1013_ = lean_int_div(v_seconds_1011_, v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Std_Time_Second_Offset_toDays___boxed(
    mut v_seconds_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Std_Time_Second_Offset_toDays(v_seconds_1014_);
    lean_dec(v_seconds_1014_);
    return v_res_1015_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofDays(
    mut v_days_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1018_ = lean_int_mul(v_days_1016_, v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofDays___boxed(
    mut v_days_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
    v_res_1020_ = l_Std_Time_Second_Offset_ofDays(v_days_1019_);
    lean_dec(v_days_1019_);
    return v_res_1020_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = lean_unsigned_to_nat(604800);
    v___x_1022_ = lean_nat_to_int(v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Std_Time_Second_Offset_toWeeks(
    mut v_seconds_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1024_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1025_ = lean_int_div(v_seconds_1023_, v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Time_Second_Offset_toWeeks___boxed(
    mut v_seconds_1026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1027_: *mut LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Std_Time_Second_Offset_toWeeks(v_seconds_1026_);
    lean_dec(v_seconds_1026_);
    return v_res_1027_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofWeeks(
    mut v_weeks_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1029_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1030_ = lean_int_mul(v_weeks_1028_, v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofWeeks___boxed(
    mut v_weeks_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Std_Time_Second_Offset_ofWeeks(v_weeks_1031_);
    lean_dec(v_weeks_1031_);
    return v_res_1032_;
}
pub unsafe fn _init_l_Std_Time_Minute_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    v___x_1033_ = lean_unsigned_to_nat(1440);
    v___x_1034_ = lean_nat_to_int(v___x_1033_);
    return v___x_1034_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toDays(
    mut v_minutes_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1036_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1037_ = lean_int_div(v_minutes_1035_, v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toDays___boxed(
    mut v_minutes_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1039_: *mut LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Std_Time_Minute_Offset_toDays(v_minutes_1038_);
    lean_dec(v_minutes_1038_);
    return v_res_1039_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofDays(
    mut v_days_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    v___x_1041_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1042_ = lean_int_mul(v_days_1040_, v___x_1041_);
    return v___x_1042_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofDays___boxed(
    mut v_days_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1044_: *mut LeanObject = core::ptr::null_mut();
    v_res_1044_ = l_Std_Time_Minute_Offset_ofDays(v_days_1043_);
    lean_dec(v_days_1043_);
    return v_res_1044_;
}
pub unsafe fn _init_l_Std_Time_Minute_Offset_toWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045_ = lean_unsigned_to_nat(10080);
    v___x_1046_ = lean_nat_to_int(v___x_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toWeeks(
    mut v_minutes_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    v___x_1048_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1049_ = lean_int_div(v_minutes_1047_, v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toWeeks___boxed(
    mut v_minutes_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1051_: *mut LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Std_Time_Minute_Offset_toWeeks(v_minutes_1050_);
    lean_dec(v_minutes_1050_);
    return v_res_1051_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofWeeks(
    mut v_weeks_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1053_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1054_ = lean_int_mul(v_weeks_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofWeeks___boxed(
    mut v_weeks_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_Time_Minute_Offset_ofWeeks(v_weeks_1055_);
    lean_dec(v_weeks_1055_);
    return v_res_1056_;
}
pub unsafe fn _init_l_Std_Time_Hour_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ = lean_unsigned_to_nat(24);
    v___x_1058_ = lean_nat_to_int(v___x_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toDays(mut v_hours_1059_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    v___x_1060_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1061_ = lean_int_div(v_hours_1059_, v___x_1060_);
    return v___x_1061_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toDays___boxed(
    mut v_hours_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1063_: *mut LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Std_Time_Hour_Offset_toDays(v_hours_1062_);
    lean_dec(v_hours_1062_);
    return v_res_1063_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofDays(mut v_days_1064_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    v___x_1065_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1066_ = lean_int_mul(v_days_1064_, v___x_1065_);
    return v___x_1066_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofDays___boxed(
    mut v_days_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_Time_Hour_Offset_ofDays(v_days_1067_);
    lean_dec(v_days_1067_);
    return v_res_1068_;
}
pub unsafe fn _init_l_Std_Time_Hour_Offset_toWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    v___x_1069_ = lean_unsigned_to_nat(168);
    v___x_1070_ = lean_nat_to_int(v___x_1069_);
    return v___x_1070_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toWeeks(
    mut v_hours_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1073_ = lean_int_div(v_hours_1071_, v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toWeeks___boxed(
    mut v_hours_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1075_: *mut LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_Std_Time_Hour_Offset_toWeeks(v_hours_1074_);
    lean_dec(v_hours_1074_);
    return v_res_1075_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofWeeks(
    mut v_weeks_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    v___x_1077_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1078_ = lean_int_mul(v_weeks_1076_, v___x_1077_);
    return v___x_1078_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofWeeks___boxed(
    mut v_weeks_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1080_: *mut LeanObject = core::ptr::null_mut();
    v_res_1080_ = l_Std_Time_Hour_Offset_ofWeeks(v_weeks_1079_);
    lean_dec(v_weeks_1079_);
    return v_res_1080_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    v___x_1083_ = lean_unsigned_to_nat(1000000);
    v___x_1084_ = lean_nat_to_int(v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset___lam__0(
    mut v_x_1085_: *mut LeanObject,
    mut v_y_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1088_ = lean_int_mul(v_y_1086_, v___x_1087_);
    v___x_1089_ = lean_int_add(v_x_1085_, v___x_1088_);
    lean_dec(v___x_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset___lam__0___boxed(
    mut v_x_1090_: *mut LeanObject,
    mut v_y_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Std_Time_instHAddOffsetOffset___lam__0(v_x_1090_, v_y_1091_);
    lean_dec(v_y_1091_);
    lean_dec(v_x_1090_);
    return v_res_1092_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v___x_1095_ = lean_unsigned_to_nat(1000000000);
    v___x_1096_ = lean_nat_to_int(v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__1___lam__0(
    mut v_x_1097_: *mut LeanObject,
    mut v_y_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1099_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1100_ = lean_int_mul(v_y_1098_, v___x_1099_);
    v___x_1101_ = lean_int_add(v_x_1097_, v___x_1100_);
    lean_dec(v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(
    mut v_x_1102_: *mut LeanObject,
    mut v_y_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1104_: *mut LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Std_Time_instHAddOffsetOffset__1___lam__0(v_x_1102_, v_y_1103_);
    lean_dec(v_y_1103_);
    lean_dec(v_x_1102_);
    return v_res_1104_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_1108_ = lean_nat_to_int(v___x_1107_);
    return v___x_1108_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__2___lam__0(
    mut v_x_1109_: *mut LeanObject,
    mut v_y_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v___x_1111_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1112_ = lean_int_mul(v_y_1110_, v___x_1111_);
    v___x_1113_ = lean_int_add(v_x_1109_, v___x_1112_);
    lean_dec(v___x_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(
    mut v_x_1114_: *mut LeanObject,
    mut v_y_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1116_: *mut LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_Time_instHAddOffsetOffset__2___lam__0(v_x_1114_, v_y_1115_);
    lean_dec(v_y_1115_);
    lean_dec(v_x_1114_);
    return v_res_1116_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1119_ = lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_1120_ = lean_nat_to_int(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__3___lam__0(
    mut v_x_1121_: *mut LeanObject,
    mut v_y_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1124_ = lean_int_mul(v_y_1122_, v___x_1123_);
    v___x_1125_ = lean_int_add(v_x_1121_, v___x_1124_);
    lean_dec(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(
    mut v_x_1126_: *mut LeanObject,
    mut v_y_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1128_: *mut LeanObject = core::ptr::null_mut();
    v_res_1128_ = l_Std_Time_instHAddOffsetOffset__3___lam__0(v_x_1126_, v_y_1127_);
    lean_dec(v_y_1127_);
    lean_dec(v_x_1126_);
    return v_res_1128_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__4___lam__0(
    mut v_x_1131_: *mut LeanObject,
    mut v_y_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1133_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1134_ = lean_int_mul(v_y_1132_, v___x_1133_);
    v___x_1135_ = lean_int_add(v_x_1131_, v___x_1134_);
    lean_dec(v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(
    mut v_x_1136_: *mut LeanObject,
    mut v_y_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Std_Time_instHAddOffsetOffset__4___lam__0(v_x_1136_, v_y_1137_);
    lean_dec(v_y_1137_);
    lean_dec(v_x_1136_);
    return v_res_1138_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__5___lam__0(
    mut v_x_1141_: *mut LeanObject,
    mut v_y_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1144_ = lean_int_mul(v_y_1142_, v___x_1143_);
    v___x_1145_ = lean_int_add(v_x_1141_, v___x_1144_);
    lean_dec(v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(
    mut v_x_1146_: *mut LeanObject,
    mut v_y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Std_Time_instHAddOffsetOffset__5___lam__0(v_x_1146_, v_y_1147_);
    lean_dec(v_y_1147_);
    lean_dec(v_x_1146_);
    return v_res_1148_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__6___lam__0(
    mut v_x_1151_: *mut LeanObject,
    mut v_y_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    v___x_1153_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1154_ = lean_int_mul(v_x_1151_, v___x_1153_);
    v___x_1155_ = lean_int_add(v___x_1154_, v_y_1152_);
    lean_dec(v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(
    mut v_x_1156_: *mut LeanObject,
    mut v_y_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1158_: *mut LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_Std_Time_instHAddOffsetOffset__6___lam__0(v_x_1156_, v_y_1157_);
    lean_dec(v_y_1157_);
    lean_dec(v_x_1156_);
    return v_res_1158_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = lean_unsigned_to_nat(1000);
    v___x_1163_ = lean_nat_to_int(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__7___lam__0(
    mut v_x_1164_: *mut LeanObject,
    mut v_y_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    v___x_1166_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1167_ = lean_int_mul(v_y_1165_, v___x_1166_);
    v___x_1168_ = lean_int_add(v_x_1164_, v___x_1167_);
    lean_dec(v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(
    mut v_x_1169_: *mut LeanObject,
    mut v_y_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Std_Time_instHAddOffsetOffset__7___lam__0(v_x_1169_, v_y_1170_);
    lean_dec(v_y_1170_);
    lean_dec(v_x_1169_);
    return v_res_1171_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1174_ = lean_unsigned_to_nat(60000);
    v___x_1175_ = lean_nat_to_int(v___x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__8___lam__0(
    mut v_x_1176_: *mut LeanObject,
    mut v_y_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    v___x_1178_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1179_ = lean_int_mul(v_y_1177_, v___x_1178_);
    v___x_1180_ = lean_int_add(v_x_1176_, v___x_1179_);
    lean_dec(v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(
    mut v_x_1181_: *mut LeanObject,
    mut v_y_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1183_: *mut LeanObject = core::ptr::null_mut();
    v_res_1183_ = l_Std_Time_instHAddOffsetOffset__8___lam__0(v_x_1181_, v_y_1182_);
    lean_dec(v_y_1182_);
    lean_dec(v_x_1181_);
    return v_res_1183_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1186_ = lean_unsigned_to_nat(3600000);
    v___x_1187_ = lean_nat_to_int(v___x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__9___lam__0(
    mut v_x_1188_: *mut LeanObject,
    mut v_y_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1190_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1191_ = lean_int_mul(v_y_1189_, v___x_1190_);
    v___x_1192_ = lean_int_add(v_x_1188_, v___x_1191_);
    lean_dec(v___x_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(
    mut v_x_1193_: *mut LeanObject,
    mut v_y_1194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1195_: *mut LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Std_Time_instHAddOffsetOffset__9___lam__0(v_x_1193_, v_y_1194_);
    lean_dec(v_y_1194_);
    lean_dec(v_x_1193_);
    return v_res_1195_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__10___lam__0(
    mut v_x_1198_: *mut LeanObject,
    mut v_y_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    v___x_1200_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1201_ = lean_int_mul(v_y_1199_, v___x_1200_);
    v___x_1202_ = lean_int_add(v_x_1198_, v___x_1201_);
    lean_dec(v___x_1201_);
    return v___x_1202_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(
    mut v_x_1203_: *mut LeanObject,
    mut v_y_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1205_: *mut LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Std_Time_instHAddOffsetOffset__10___lam__0(v_x_1203_, v_y_1204_);
    lean_dec(v_y_1204_);
    lean_dec(v_x_1203_);
    return v_res_1205_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__11___lam__0(
    mut v_x_1208_: *mut LeanObject,
    mut v_y_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    v___x_1210_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1211_ = lean_int_mul(v_y_1209_, v___x_1210_);
    v___x_1212_ = lean_int_add(v_x_1208_, v___x_1211_);
    lean_dec(v___x_1211_);
    return v___x_1212_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(
    mut v_x_1213_: *mut LeanObject,
    mut v_y_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1215_: *mut LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Std_Time_instHAddOffsetOffset__11___lam__0(v_x_1213_, v_y_1214_);
    lean_dec(v_y_1214_);
    lean_dec(v_x_1213_);
    return v_res_1215_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__12___lam__0(
    mut v_x_1218_: *mut LeanObject,
    mut v_y_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1221_ = lean_int_mul(v_x_1218_, v___x_1220_);
    v___x_1222_ = lean_int_add(v___x_1221_, v_y_1219_);
    lean_dec(v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(
    mut v_x_1223_: *mut LeanObject,
    mut v_y_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_Time_instHAddOffsetOffset__12___lam__0(v_x_1223_, v_y_1224_);
    lean_dec(v_y_1224_);
    lean_dec(v_x_1223_);
    return v_res_1225_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__13___lam__0(
    mut v_x_1228_: *mut LeanObject,
    mut v_y_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    v___x_1230_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1231_ = lean_int_mul(v_x_1228_, v___x_1230_);
    v___x_1232_ = lean_int_add(v___x_1231_, v_y_1229_);
    lean_dec(v___x_1231_);
    return v___x_1232_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(
    mut v_x_1233_: *mut LeanObject,
    mut v_y_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1235_: *mut LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Std_Time_instHAddOffsetOffset__13___lam__0(v_x_1233_, v_y_1234_);
    lean_dec(v_y_1234_);
    lean_dec(v_x_1233_);
    return v_res_1235_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    v___x_1239_ = lean_unsigned_to_nat(60);
    v___x_1240_ = lean_nat_to_int(v___x_1239_);
    return v___x_1240_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__14___lam__0(
    mut v_x_1241_: *mut LeanObject,
    mut v_y_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    v___x_1243_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1244_ = lean_int_mul(v_y_1242_, v___x_1243_);
    v___x_1245_ = lean_int_add(v_x_1241_, v___x_1244_);
    lean_dec(v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(
    mut v_x_1246_: *mut LeanObject,
    mut v_y_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_instHAddOffsetOffset__14___lam__0(v_x_1246_, v_y_1247_);
    lean_dec(v_y_1247_);
    lean_dec(v_x_1246_);
    return v_res_1248_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1251_ = lean_unsigned_to_nat(3600);
    v___x_1252_ = lean_nat_to_int(v___x_1251_);
    return v___x_1252_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__15___lam__0(
    mut v_x_1253_: *mut LeanObject,
    mut v_y_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1256_ = lean_int_mul(v_y_1254_, v___x_1255_);
    v___x_1257_ = lean_int_add(v_x_1253_, v___x_1256_);
    lean_dec(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(
    mut v_x_1258_: *mut LeanObject,
    mut v_y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Std_Time_instHAddOffsetOffset__15___lam__0(v_x_1258_, v_y_1259_);
    lean_dec(v_y_1259_);
    lean_dec(v_x_1258_);
    return v_res_1260_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__16___lam__0(
    mut v_x_1263_: *mut LeanObject,
    mut v_y_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1266_ = lean_int_mul(v_y_1264_, v___x_1265_);
    v___x_1267_ = lean_int_add(v_x_1263_, v___x_1266_);
    lean_dec(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(
    mut v_x_1268_: *mut LeanObject,
    mut v_y_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Std_Time_instHAddOffsetOffset__16___lam__0(v_x_1268_, v_y_1269_);
    lean_dec(v_y_1269_);
    lean_dec(v_x_1268_);
    return v_res_1270_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__17___lam__0(
    mut v_x_1273_: *mut LeanObject,
    mut v_y_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1276_ = lean_int_mul(v_y_1274_, v___x_1275_);
    v___x_1277_ = lean_int_add(v_x_1273_, v___x_1276_);
    lean_dec(v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(
    mut v_x_1278_: *mut LeanObject,
    mut v_y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1280_: *mut LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Std_Time_instHAddOffsetOffset__17___lam__0(v_x_1278_, v_y_1279_);
    lean_dec(v_y_1279_);
    lean_dec(v_x_1278_);
    return v_res_1280_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__18___lam__0(
    mut v_x_1283_: *mut LeanObject,
    mut v_y_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1286_ = lean_int_mul(v_x_1283_, v___x_1285_);
    v___x_1287_ = lean_int_add(v___x_1286_, v_y_1284_);
    lean_dec(v___x_1286_);
    return v___x_1287_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(
    mut v_x_1288_: *mut LeanObject,
    mut v_y_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Std_Time_instHAddOffsetOffset__18___lam__0(v_x_1288_, v_y_1289_);
    lean_dec(v_y_1289_);
    lean_dec(v_x_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__19___lam__0(
    mut v_x_1293_: *mut LeanObject,
    mut v_y_1294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1296_ = lean_int_mul(v_x_1293_, v___x_1295_);
    v___x_1297_ = lean_int_add(v___x_1296_, v_y_1294_);
    lean_dec(v___x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(
    mut v_x_1298_: *mut LeanObject,
    mut v_y_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Std_Time_instHAddOffsetOffset__19___lam__0(v_x_1298_, v_y_1299_);
    lean_dec(v_y_1299_);
    lean_dec(v_x_1298_);
    return v_res_1300_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__20___lam__0(
    mut v_x_1303_: *mut LeanObject,
    mut v_y_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1306_ = lean_int_mul(v_x_1303_, v___x_1305_);
    v___x_1307_ = lean_int_add(v___x_1306_, v_y_1304_);
    lean_dec(v___x_1306_);
    return v___x_1307_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(
    mut v_x_1308_: *mut LeanObject,
    mut v_y_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1310_: *mut LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Std_Time_instHAddOffsetOffset__20___lam__0(v_x_1308_, v_y_1309_);
    lean_dec(v_y_1309_);
    lean_dec(v_x_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__22___lam__0(
    mut v_x_1315_: *mut LeanObject,
    mut v_y_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1318_ = lean_int_mul(v_y_1316_, v___x_1317_);
    v___x_1319_ = lean_int_add(v_x_1315_, v___x_1318_);
    lean_dec(v___x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(
    mut v_x_1320_: *mut LeanObject,
    mut v_y_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_Time_instHAddOffsetOffset__22___lam__0(v_x_1320_, v_y_1321_);
    lean_dec(v_y_1321_);
    lean_dec(v_x_1320_);
    return v_res_1322_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__23___lam__0(
    mut v_x_1325_: *mut LeanObject,
    mut v_y_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1328_ = lean_int_mul(v_y_1326_, v___x_1327_);
    v___x_1329_ = lean_int_add(v_x_1325_, v___x_1328_);
    lean_dec(v___x_1328_);
    return v___x_1329_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(
    mut v_x_1330_: *mut LeanObject,
    mut v_y_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1332_: *mut LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Std_Time_instHAddOffsetOffset__23___lam__0(v_x_1330_, v_y_1331_);
    lean_dec(v_y_1331_);
    lean_dec(v_x_1330_);
    return v_res_1332_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__24___lam__0(
    mut v_x_1335_: *mut LeanObject,
    mut v_y_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1338_ = lean_int_mul(v_x_1335_, v___x_1337_);
    v___x_1339_ = lean_int_add(v___x_1338_, v_y_1336_);
    lean_dec(v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(
    mut v_x_1340_: *mut LeanObject,
    mut v_y_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1342_: *mut LeanObject = core::ptr::null_mut();
    v_res_1342_ = l_Std_Time_instHAddOffsetOffset__24___lam__0(v_x_1340_, v_y_1341_);
    lean_dec(v_y_1341_);
    lean_dec(v_x_1340_);
    return v_res_1342_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__25___lam__0(
    mut v_x_1345_: *mut LeanObject,
    mut v_y_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1348_ = lean_int_mul(v_x_1345_, v___x_1347_);
    v___x_1349_ = lean_int_add(v___x_1348_, v_y_1346_);
    lean_dec(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(
    mut v_x_1350_: *mut LeanObject,
    mut v_y_1351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1352_: *mut LeanObject = core::ptr::null_mut();
    v_res_1352_ = l_Std_Time_instHAddOffsetOffset__25___lam__0(v_x_1350_, v_y_1351_);
    lean_dec(v_y_1351_);
    lean_dec(v_x_1350_);
    return v_res_1352_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__26___lam__0(
    mut v_x_1355_: *mut LeanObject,
    mut v_y_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1358_ = lean_int_mul(v_x_1355_, v___x_1357_);
    v___x_1359_ = lean_int_add(v___x_1358_, v_y_1356_);
    lean_dec(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(
    mut v_x_1360_: *mut LeanObject,
    mut v_y_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1362_: *mut LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_Time_instHAddOffsetOffset__26___lam__0(v_x_1360_, v_y_1361_);
    lean_dec(v_y_1361_);
    lean_dec(v_x_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__28___lam__0(
    mut v_x_1367_: *mut LeanObject,
    mut v_y_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1370_ = lean_int_mul(v_y_1368_, v___x_1369_);
    v___x_1371_ = lean_int_add(v_x_1367_, v___x_1370_);
    lean_dec(v___x_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(
    mut v_x_1372_: *mut LeanObject,
    mut v_y_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1374_: *mut LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Std_Time_instHAddOffsetOffset__28___lam__0(v_x_1372_, v_y_1373_);
    lean_dec(v_y_1373_);
    lean_dec(v_x_1372_);
    return v_res_1374_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__29___lam__0(
    mut v_x_1377_: *mut LeanObject,
    mut v_y_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v___x_1379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1380_ = lean_int_mul(v_y_1378_, v___x_1379_);
    v___x_1381_ = lean_int_add(v_x_1377_, v___x_1380_);
    lean_dec(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(
    mut v_x_1382_: *mut LeanObject,
    mut v_y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_Time_instHAddOffsetOffset__29___lam__0(v_x_1382_, v_y_1383_);
    lean_dec(v_y_1383_);
    lean_dec(v_x_1382_);
    return v_res_1384_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__30___lam__0(
    mut v_x_1387_: *mut LeanObject,
    mut v_y_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1389_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1390_ = lean_int_mul(v_x_1387_, v___x_1389_);
    v___x_1391_ = lean_int_add(v___x_1390_, v_y_1388_);
    lean_dec(v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(
    mut v_x_1392_: *mut LeanObject,
    mut v_y_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Std_Time_instHAddOffsetOffset__30___lam__0(v_x_1392_, v_y_1393_);
    lean_dec(v_y_1393_);
    lean_dec(v_x_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__31___lam__0(
    mut v_x_1397_: *mut LeanObject,
    mut v_y_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1400_ = lean_int_mul(v_x_1397_, v___x_1399_);
    v___x_1401_ = lean_int_add(v___x_1400_, v_y_1398_);
    lean_dec(v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(
    mut v_x_1402_: *mut LeanObject,
    mut v_y_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1404_: *mut LeanObject = core::ptr::null_mut();
    v_res_1404_ = l_Std_Time_instHAddOffsetOffset__31___lam__0(v_x_1402_, v_y_1403_);
    lean_dec(v_y_1403_);
    lean_dec(v_x_1402_);
    return v_res_1404_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__32___lam__0(
    mut v_x_1407_: *mut LeanObject,
    mut v_y_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1409_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1410_ = lean_int_mul(v_x_1407_, v___x_1409_);
    v___x_1411_ = lean_int_add(v___x_1410_, v_y_1408_);
    lean_dec(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(
    mut v_x_1412_: *mut LeanObject,
    mut v_y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Std_Time_instHAddOffsetOffset__32___lam__0(v_x_1412_, v_y_1413_);
    lean_dec(v_y_1413_);
    lean_dec(v_x_1412_);
    return v_res_1414_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__33___lam__0(
    mut v_x_1417_: *mut LeanObject,
    mut v_y_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1420_ = lean_int_mul(v_x_1417_, v___x_1419_);
    v___x_1421_ = lean_int_add(v___x_1420_, v_y_1418_);
    lean_dec(v___x_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(
    mut v_x_1422_: *mut LeanObject,
    mut v_y_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Std_Time_instHAddOffsetOffset__33___lam__0(v_x_1422_, v_y_1423_);
    lean_dec(v_y_1423_);
    lean_dec(v_x_1422_);
    return v_res_1424_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__34___lam__0(
    mut v_x_1427_: *mut LeanObject,
    mut v_y_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1430_ = lean_int_mul(v_x_1427_, v___x_1429_);
    v___x_1431_ = lean_int_add(v___x_1430_, v_y_1428_);
    lean_dec(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(
    mut v_x_1432_: *mut LeanObject,
    mut v_y_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1434_: *mut LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Std_Time_instHAddOffsetOffset__34___lam__0(v_x_1432_, v_y_1433_);
    lean_dec(v_y_1433_);
    lean_dec(v_x_1432_);
    return v_res_1434_;
}
pub unsafe fn _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_unsigned_to_nat(7);
    v___x_1439_ = lean_nat_to_int(v___x_1438_);
    return v___x_1439_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__35___lam__0(
    mut v_x_1440_: *mut LeanObject,
    mut v_y_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1443_ = lean_int_mul(v_y_1441_, v___x_1442_);
    v___x_1444_ = lean_int_add(v_x_1440_, v___x_1443_);
    lean_dec(v___x_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(
    mut v_x_1445_: *mut LeanObject,
    mut v_y_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1447_: *mut LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Std_Time_instHAddOffsetOffset__35___lam__0(v_x_1445_, v_y_1446_);
    lean_dec(v_y_1446_);
    lean_dec(v_x_1445_);
    return v_res_1447_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__36___lam__0(
    mut v_x_1450_: *mut LeanObject,
    mut v_y_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1453_ = lean_int_mul(v_x_1450_, v___x_1452_);
    v___x_1454_ = lean_int_add(v___x_1453_, v_y_1451_);
    lean_dec(v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(
    mut v_x_1455_: *mut LeanObject,
    mut v_y_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1457_: *mut LeanObject = core::ptr::null_mut();
    v_res_1457_ = l_Std_Time_instHAddOffsetOffset__36___lam__0(v_x_1455_, v_y_1456_);
    lean_dec(v_y_1456_);
    lean_dec(v_x_1455_);
    return v_res_1457_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__37___lam__0(
    mut v_x_1460_: *mut LeanObject,
    mut v_y_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1463_ = lean_int_mul(v_x_1460_, v___x_1462_);
    v___x_1464_ = lean_int_add(v___x_1463_, v_y_1461_);
    lean_dec(v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(
    mut v_x_1465_: *mut LeanObject,
    mut v_y_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1467_: *mut LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Std_Time_instHAddOffsetOffset__37___lam__0(v_x_1465_, v_y_1466_);
    lean_dec(v_y_1466_);
    lean_dec(v_x_1465_);
    return v_res_1467_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__38___lam__0(
    mut v_x_1470_: *mut LeanObject,
    mut v_y_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v___x_1472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1473_ = lean_int_mul(v_x_1470_, v___x_1472_);
    v___x_1474_ = lean_int_add(v___x_1473_, v_y_1471_);
    lean_dec(v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(
    mut v_x_1475_: *mut LeanObject,
    mut v_y_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_Std_Time_instHAddOffsetOffset__38___lam__0(v_x_1475_, v_y_1476_);
    lean_dec(v_y_1476_);
    lean_dec(v_x_1475_);
    return v_res_1477_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__39___lam__0(
    mut v_x_1480_: *mut LeanObject,
    mut v_y_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1483_ = lean_int_mul(v_x_1480_, v___x_1482_);
    v___x_1484_ = lean_int_add(v___x_1483_, v_y_1481_);
    lean_dec(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(
    mut v_x_1485_: *mut LeanObject,
    mut v_y_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1487_: *mut LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Std_Time_instHAddOffsetOffset__39___lam__0(v_x_1485_, v_y_1486_);
    lean_dec(v_y_1486_);
    lean_dec(v_x_1485_);
    return v_res_1487_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__40___lam__0(
    mut v_x_1490_: *mut LeanObject,
    mut v_y_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1493_ = lean_int_mul(v_x_1490_, v___x_1492_);
    v___x_1494_ = lean_int_add(v___x_1493_, v_y_1491_);
    lean_dec(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(
    mut v_x_1495_: *mut LeanObject,
    mut v_y_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1497_: *mut LeanObject = core::ptr::null_mut();
    v_res_1497_ = l_Std_Time_instHAddOffsetOffset__40___lam__0(v_x_1495_, v_y_1496_);
    lean_dec(v_y_1496_);
    lean_dec(v_x_1495_);
    return v_res_1497_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__41___lam__0(
    mut v_x_1500_: *mut LeanObject,
    mut v_y_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1503_ = lean_int_mul(v_x_1500_, v___x_1502_);
    v___x_1504_ = lean_int_add(v___x_1503_, v_y_1501_);
    lean_dec(v___x_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(
    mut v_x_1505_: *mut LeanObject,
    mut v_y_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1507_: *mut LeanObject = core::ptr::null_mut();
    v_res_1507_ = l_Std_Time_instHAddOffsetOffset__41___lam__0(v_x_1505_, v_y_1506_);
    lean_dec(v_y_1506_);
    lean_dec(v_x_1505_);
    return v_res_1507_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset___lam__0(
    mut v_x_1513_: *mut LeanObject,
    mut v_y_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    v___x_1515_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1516_ = lean_int_mul(v_y_1514_, v___x_1515_);
    v___x_1517_ = lean_int_sub(v_x_1513_, v___x_1516_);
    lean_dec(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset___lam__0___boxed(
    mut v_x_1518_: *mut LeanObject,
    mut v_y_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1520_: *mut LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_Std_Time_instHSubOffsetOffset___lam__0(v_x_1518_, v_y_1519_);
    lean_dec(v_y_1519_);
    lean_dec(v_x_1518_);
    return v_res_1520_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__1___lam__0(
    mut v_x_1523_: *mut LeanObject,
    mut v_y_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1525_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1526_ = lean_int_mul(v_y_1524_, v___x_1525_);
    v___x_1527_ = lean_int_sub(v_x_1523_, v___x_1526_);
    lean_dec(v___x_1526_);
    return v___x_1527_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(
    mut v_x_1528_: *mut LeanObject,
    mut v_y_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Std_Time_instHSubOffsetOffset__1___lam__0(v_x_1528_, v_y_1529_);
    lean_dec(v_y_1529_);
    lean_dec(v_x_1528_);
    return v_res_1530_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__2___lam__0(
    mut v_x_1533_: *mut LeanObject,
    mut v_y_1534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    v___x_1535_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1536_ = lean_int_mul(v_y_1534_, v___x_1535_);
    v___x_1537_ = lean_int_sub(v_x_1533_, v___x_1536_);
    lean_dec(v___x_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(
    mut v_x_1538_: *mut LeanObject,
    mut v_y_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1540_: *mut LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Std_Time_instHSubOffsetOffset__2___lam__0(v_x_1538_, v_y_1539_);
    lean_dec(v_y_1539_);
    lean_dec(v_x_1538_);
    return v_res_1540_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__3___lam__0(
    mut v_x_1543_: *mut LeanObject,
    mut v_y_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1545_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1546_ = lean_int_mul(v_y_1544_, v___x_1545_);
    v___x_1547_ = lean_int_sub(v_x_1543_, v___x_1546_);
    lean_dec(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(
    mut v_x_1548_: *mut LeanObject,
    mut v_y_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Std_Time_instHSubOffsetOffset__3___lam__0(v_x_1548_, v_y_1549_);
    lean_dec(v_y_1549_);
    lean_dec(v_x_1548_);
    return v_res_1550_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__4___lam__0(
    mut v_x_1553_: *mut LeanObject,
    mut v_y_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1556_ = lean_int_mul(v_y_1554_, v___x_1555_);
    v___x_1557_ = lean_int_sub(v_x_1553_, v___x_1556_);
    lean_dec(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(
    mut v_x_1558_: *mut LeanObject,
    mut v_y_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Std_Time_instHSubOffsetOffset__4___lam__0(v_x_1558_, v_y_1559_);
    lean_dec(v_y_1559_);
    lean_dec(v_x_1558_);
    return v_res_1560_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__5___lam__0(
    mut v_x_1563_: *mut LeanObject,
    mut v_y_1564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1565_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1566_ = lean_int_mul(v_y_1564_, v___x_1565_);
    v___x_1567_ = lean_int_sub(v_x_1563_, v___x_1566_);
    lean_dec(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(
    mut v_x_1568_: *mut LeanObject,
    mut v_y_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1570_: *mut LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_Time_instHSubOffsetOffset__5___lam__0(v_x_1568_, v_y_1569_);
    lean_dec(v_y_1569_);
    lean_dec(v_x_1568_);
    return v_res_1570_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__6___lam__0(
    mut v_x_1573_: *mut LeanObject,
    mut v_y_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    v___x_1575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0,
    );
    v___x_1576_ = lean_int_mul(v_x_1573_, v___x_1575_);
    v___x_1577_ = lean_int_sub(v___x_1576_, v_y_1574_);
    lean_dec(v___x_1576_);
    return v___x_1577_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(
    mut v_x_1578_: *mut LeanObject,
    mut v_y_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1580_: *mut LeanObject = core::ptr::null_mut();
    v_res_1580_ = l_Std_Time_instHSubOffsetOffset__6___lam__0(v_x_1578_, v_y_1579_);
    lean_dec(v_y_1579_);
    lean_dec(v_x_1578_);
    return v_res_1580_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__7___lam__0(
    mut v_x_1584_: *mut LeanObject,
    mut v_y_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1587_ = lean_int_mul(v_y_1585_, v___x_1586_);
    v___x_1588_ = lean_int_sub(v_x_1584_, v___x_1587_);
    lean_dec(v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(
    mut v_x_1589_: *mut LeanObject,
    mut v_y_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1591_: *mut LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Std_Time_instHSubOffsetOffset__7___lam__0(v_x_1589_, v_y_1590_);
    lean_dec(v_y_1590_);
    lean_dec(v_x_1589_);
    return v_res_1591_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__8___lam__0(
    mut v_x_1594_: *mut LeanObject,
    mut v_y_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    v___x_1596_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1597_ = lean_int_mul(v_y_1595_, v___x_1596_);
    v___x_1598_ = lean_int_sub(v_x_1594_, v___x_1597_);
    lean_dec(v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(
    mut v_x_1599_: *mut LeanObject,
    mut v_y_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1601_: *mut LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Std_Time_instHSubOffsetOffset__8___lam__0(v_x_1599_, v_y_1600_);
    lean_dec(v_y_1600_);
    lean_dec(v_x_1599_);
    return v_res_1601_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__9___lam__0(
    mut v_x_1604_: *mut LeanObject,
    mut v_y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1607_ = lean_int_mul(v_y_1605_, v___x_1606_);
    v___x_1608_ = lean_int_sub(v_x_1604_, v___x_1607_);
    lean_dec(v___x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(
    mut v_x_1609_: *mut LeanObject,
    mut v_y_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1611_: *mut LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_Time_instHSubOffsetOffset__9___lam__0(v_x_1609_, v_y_1610_);
    lean_dec(v_y_1610_);
    lean_dec(v_x_1609_);
    return v_res_1611_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__10___lam__0(
    mut v_x_1614_: *mut LeanObject,
    mut v_y_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1616_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1617_ = lean_int_mul(v_y_1615_, v___x_1616_);
    v___x_1618_ = lean_int_sub(v_x_1614_, v___x_1617_);
    lean_dec(v___x_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(
    mut v_x_1619_: *mut LeanObject,
    mut v_y_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1621_: *mut LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Std_Time_instHSubOffsetOffset__10___lam__0(v_x_1619_, v_y_1620_);
    lean_dec(v_y_1620_);
    lean_dec(v_x_1619_);
    return v_res_1621_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__11___lam__0(
    mut v_x_1624_: *mut LeanObject,
    mut v_y_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1627_ = lean_int_mul(v_y_1625_, v___x_1626_);
    v___x_1628_ = lean_int_sub(v_x_1624_, v___x_1627_);
    lean_dec(v___x_1627_);
    return v___x_1628_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(
    mut v_x_1629_: *mut LeanObject,
    mut v_y_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1631_: *mut LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Std_Time_instHSubOffsetOffset__11___lam__0(v_x_1629_, v_y_1630_);
    lean_dec(v_y_1630_);
    lean_dec(v_x_1629_);
    return v_res_1631_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__12___lam__0(
    mut v_x_1634_: *mut LeanObject,
    mut v_y_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1636_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0,
    );
    v___x_1637_ = lean_int_mul(v_x_1634_, v___x_1636_);
    v___x_1638_ = lean_int_sub(v___x_1637_, v_y_1635_);
    lean_dec(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(
    mut v_x_1639_: *mut LeanObject,
    mut v_y_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1641_: *mut LeanObject = core::ptr::null_mut();
    v_res_1641_ = l_Std_Time_instHSubOffsetOffset__12___lam__0(v_x_1639_, v_y_1640_);
    lean_dec(v_y_1640_);
    lean_dec(v_x_1639_);
    return v_res_1641_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__13___lam__0(
    mut v_x_1644_: *mut LeanObject,
    mut v_y_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1646_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0,
    );
    v___x_1647_ = lean_int_mul(v_x_1644_, v___x_1646_);
    v___x_1648_ = lean_int_sub(v___x_1647_, v_y_1645_);
    lean_dec(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(
    mut v_x_1649_: *mut LeanObject,
    mut v_y_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1651_: *mut LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Std_Time_instHSubOffsetOffset__13___lam__0(v_x_1649_, v_y_1650_);
    lean_dec(v_y_1650_);
    lean_dec(v_x_1649_);
    return v_res_1651_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__14___lam__0(
    mut v_x_1655_: *mut LeanObject,
    mut v_y_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1658_ = lean_int_mul(v_y_1656_, v___x_1657_);
    v___x_1659_ = lean_int_sub(v_x_1655_, v___x_1658_);
    lean_dec(v___x_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(
    mut v_x_1660_: *mut LeanObject,
    mut v_y_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1662_: *mut LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_Time_instHSubOffsetOffset__14___lam__0(v_x_1660_, v_y_1661_);
    lean_dec(v_y_1661_);
    lean_dec(v_x_1660_);
    return v_res_1662_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__15___lam__0(
    mut v_x_1665_: *mut LeanObject,
    mut v_y_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v___x_1667_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1668_ = lean_int_mul(v_y_1666_, v___x_1667_);
    v___x_1669_ = lean_int_sub(v_x_1665_, v___x_1668_);
    lean_dec(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(
    mut v_x_1670_: *mut LeanObject,
    mut v_y_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1672_: *mut LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Std_Time_instHSubOffsetOffset__15___lam__0(v_x_1670_, v_y_1671_);
    lean_dec(v_y_1671_);
    lean_dec(v_x_1670_);
    return v_res_1672_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__16___lam__0(
    mut v_x_1675_: *mut LeanObject,
    mut v_y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    v___x_1677_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1678_ = lean_int_mul(v_y_1676_, v___x_1677_);
    v___x_1679_ = lean_int_sub(v_x_1675_, v___x_1678_);
    lean_dec(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(
    mut v_x_1680_: *mut LeanObject,
    mut v_y_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1682_: *mut LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Std_Time_instHSubOffsetOffset__16___lam__0(v_x_1680_, v_y_1681_);
    lean_dec(v_y_1681_);
    lean_dec(v_x_1680_);
    return v_res_1682_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__17___lam__0(
    mut v_x_1685_: *mut LeanObject,
    mut v_y_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1687_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1688_ = lean_int_mul(v_y_1686_, v___x_1687_);
    v___x_1689_ = lean_int_sub(v_x_1685_, v___x_1688_);
    lean_dec(v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(
    mut v_x_1690_: *mut LeanObject,
    mut v_y_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Std_Time_instHSubOffsetOffset__17___lam__0(v_x_1690_, v_y_1691_);
    lean_dec(v_y_1691_);
    lean_dec(v_x_1690_);
    return v_res_1692_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__18___lam__0(
    mut v_x_1695_: *mut LeanObject,
    mut v_y_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1697_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0,
    );
    v___x_1698_ = lean_int_mul(v_x_1695_, v___x_1697_);
    v___x_1699_ = lean_int_sub(v___x_1698_, v_y_1696_);
    lean_dec(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(
    mut v_x_1700_: *mut LeanObject,
    mut v_y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Std_Time_instHSubOffsetOffset__18___lam__0(v_x_1700_, v_y_1701_);
    lean_dec(v_y_1701_);
    lean_dec(v_x_1700_);
    return v_res_1702_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__19___lam__0(
    mut v_x_1705_: *mut LeanObject,
    mut v_y_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0,
    );
    v___x_1708_ = lean_int_mul(v_x_1705_, v___x_1707_);
    v___x_1709_ = lean_int_sub(v___x_1708_, v_y_1706_);
    lean_dec(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(
    mut v_x_1710_: *mut LeanObject,
    mut v_y_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Std_Time_instHSubOffsetOffset__19___lam__0(v_x_1710_, v_y_1711_);
    lean_dec(v_y_1711_);
    lean_dec(v_x_1710_);
    return v_res_1712_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__20___lam__0(
    mut v_x_1715_: *mut LeanObject,
    mut v_y_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1717_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0,
    );
    v___x_1718_ = lean_int_mul(v_x_1715_, v___x_1717_);
    v___x_1719_ = lean_int_sub(v___x_1718_, v_y_1716_);
    lean_dec(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(
    mut v_x_1720_: *mut LeanObject,
    mut v_y_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1722_: *mut LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Std_Time_instHSubOffsetOffset__20___lam__0(v_x_1720_, v_y_1721_);
    lean_dec(v_y_1721_);
    lean_dec(v_x_1720_);
    return v_res_1722_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__22___lam__0(
    mut v_x_1727_: *mut LeanObject,
    mut v_y_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1730_ = lean_int_mul(v_y_1728_, v___x_1729_);
    v___x_1731_ = lean_int_sub(v_x_1727_, v___x_1730_);
    lean_dec(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(
    mut v_x_1732_: *mut LeanObject,
    mut v_y_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Time_instHSubOffsetOffset__22___lam__0(v_x_1732_, v_y_1733_);
    lean_dec(v_y_1733_);
    lean_dec(v_x_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__23___lam__0(
    mut v_x_1737_: *mut LeanObject,
    mut v_y_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1740_ = lean_int_mul(v_y_1738_, v___x_1739_);
    v___x_1741_ = lean_int_sub(v_x_1737_, v___x_1740_);
    lean_dec(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(
    mut v_x_1742_: *mut LeanObject,
    mut v_y_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1744_: *mut LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Std_Time_instHSubOffsetOffset__23___lam__0(v_x_1742_, v_y_1743_);
    lean_dec(v_y_1743_);
    lean_dec(v_x_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__24___lam__0(
    mut v_x_1747_: *mut LeanObject,
    mut v_y_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1749_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0,
    );
    v___x_1750_ = lean_int_mul(v_x_1747_, v___x_1749_);
    v___x_1751_ = lean_int_sub(v___x_1750_, v_y_1748_);
    lean_dec(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(
    mut v_x_1752_: *mut LeanObject,
    mut v_y_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1754_: *mut LeanObject = core::ptr::null_mut();
    v_res_1754_ = l_Std_Time_instHSubOffsetOffset__24___lam__0(v_x_1752_, v_y_1753_);
    lean_dec(v_y_1753_);
    lean_dec(v_x_1752_);
    return v_res_1754_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__25___lam__0(
    mut v_x_1757_: *mut LeanObject,
    mut v_y_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0,
    );
    v___x_1760_ = lean_int_mul(v_x_1757_, v___x_1759_);
    v___x_1761_ = lean_int_sub(v___x_1760_, v_y_1758_);
    lean_dec(v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(
    mut v_x_1762_: *mut LeanObject,
    mut v_y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1764_: *mut LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Std_Time_instHSubOffsetOffset__25___lam__0(v_x_1762_, v_y_1763_);
    lean_dec(v_y_1763_);
    lean_dec(v_x_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__26___lam__0(
    mut v_x_1767_: *mut LeanObject,
    mut v_y_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v___x_1769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0,
    );
    v___x_1770_ = lean_int_mul(v_x_1767_, v___x_1769_);
    v___x_1771_ = lean_int_sub(v___x_1770_, v_y_1768_);
    lean_dec(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(
    mut v_x_1772_: *mut LeanObject,
    mut v_y_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Std_Time_instHSubOffsetOffset__26___lam__0(v_x_1772_, v_y_1773_);
    lean_dec(v_y_1773_);
    lean_dec(v_x_1772_);
    return v_res_1774_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__28___lam__0(
    mut v_x_1779_: *mut LeanObject,
    mut v_y_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1782_ = lean_int_mul(v_y_1780_, v___x_1781_);
    v___x_1783_ = lean_int_sub(v_x_1779_, v___x_1782_);
    lean_dec(v___x_1782_);
    return v___x_1783_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(
    mut v_x_1784_: *mut LeanObject,
    mut v_y_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1786_: *mut LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_Time_instHSubOffsetOffset__28___lam__0(v_x_1784_, v_y_1785_);
    lean_dec(v_y_1785_);
    lean_dec(v_x_1784_);
    return v_res_1786_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__29___lam__0(
    mut v_x_1789_: *mut LeanObject,
    mut v_y_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    v___x_1791_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1792_ = lean_int_mul(v_y_1790_, v___x_1791_);
    v___x_1793_ = lean_int_sub(v_x_1789_, v___x_1792_);
    lean_dec(v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(
    mut v_x_1794_: *mut LeanObject,
    mut v_y_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Std_Time_instHSubOffsetOffset__29___lam__0(v_x_1794_, v_y_1795_);
    lean_dec(v_y_1795_);
    lean_dec(v_x_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__30___lam__0(
    mut v_x_1799_: *mut LeanObject,
    mut v_y_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1801_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0,
    );
    v___x_1802_ = lean_int_mul(v_x_1799_, v___x_1801_);
    v___x_1803_ = lean_int_sub(v___x_1802_, v_y_1800_);
    lean_dec(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(
    mut v_x_1804_: *mut LeanObject,
    mut v_y_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1806_: *mut LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Std_Time_instHSubOffsetOffset__30___lam__0(v_x_1804_, v_y_1805_);
    lean_dec(v_y_1805_);
    lean_dec(v_x_1804_);
    return v_res_1806_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__31___lam__0(
    mut v_x_1809_: *mut LeanObject,
    mut v_y_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    v___x_1811_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toDays___closed__0,
    );
    v___x_1812_ = lean_int_mul(v_x_1809_, v___x_1811_);
    v___x_1813_ = lean_int_sub(v___x_1812_, v_y_1810_);
    lean_dec(v___x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(
    mut v_x_1814_: *mut LeanObject,
    mut v_y_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1816_: *mut LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Std_Time_instHSubOffsetOffset__31___lam__0(v_x_1814_, v_y_1815_);
    lean_dec(v_y_1815_);
    lean_dec(v_x_1814_);
    return v_res_1816_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__32___lam__0(
    mut v_x_1819_: *mut LeanObject,
    mut v_y_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Second_Offset_toDays___closed__0,
    );
    v___x_1822_ = lean_int_mul(v_x_1819_, v___x_1821_);
    v___x_1823_ = lean_int_sub(v___x_1822_, v_y_1820_);
    lean_dec(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(
    mut v_x_1824_: *mut LeanObject,
    mut v_y_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1826_: *mut LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_Time_instHSubOffsetOffset__32___lam__0(v_x_1824_, v_y_1825_);
    lean_dec(v_y_1825_);
    lean_dec(v_x_1824_);
    return v_res_1826_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__33___lam__0(
    mut v_x_1829_: *mut LeanObject,
    mut v_y_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toDays___closed__0,
    );
    v___x_1832_ = lean_int_mul(v_x_1829_, v___x_1831_);
    v___x_1833_ = lean_int_sub(v___x_1832_, v_y_1830_);
    lean_dec(v___x_1832_);
    return v___x_1833_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(
    mut v_x_1834_: *mut LeanObject,
    mut v_y_1835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1836_: *mut LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_Time_instHSubOffsetOffset__33___lam__0(v_x_1834_, v_y_1835_);
    lean_dec(v_y_1835_);
    lean_dec(v_x_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__34___lam__0(
    mut v_x_1839_: *mut LeanObject,
    mut v_y_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1841_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toDays___closed__0,
    );
    v___x_1842_ = lean_int_mul(v_x_1839_, v___x_1841_);
    v___x_1843_ = lean_int_sub(v___x_1842_, v_y_1840_);
    lean_dec(v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(
    mut v_x_1844_: *mut LeanObject,
    mut v_y_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Std_Time_instHSubOffsetOffset__34___lam__0(v_x_1844_, v_y_1845_);
    lean_dec(v_y_1845_);
    lean_dec(v_x_1844_);
    return v_res_1846_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__35___lam__0(
    mut v_x_1850_: *mut LeanObject,
    mut v_y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1853_ = lean_int_mul(v_y_1851_, v___x_1852_);
    v___x_1854_ = lean_int_sub(v_x_1850_, v___x_1853_);
    lean_dec(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(
    mut v_x_1855_: *mut LeanObject,
    mut v_y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_Time_instHSubOffsetOffset__35___lam__0(v_x_1855_, v_y_1856_);
    lean_dec(v_y_1856_);
    lean_dec(v_x_1855_);
    return v_res_1857_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__36___lam__0(
    mut v_x_1860_: *mut LeanObject,
    mut v_y_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0,
    );
    v___x_1863_ = lean_int_mul(v_x_1860_, v___x_1862_);
    v___x_1864_ = lean_int_sub(v___x_1863_, v_y_1861_);
    lean_dec(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(
    mut v_x_1865_: *mut LeanObject,
    mut v_y_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Std_Time_instHSubOffsetOffset__36___lam__0(v_x_1865_, v_y_1866_);
    lean_dec(v_y_1866_);
    lean_dec(v_x_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__37___lam__0(
    mut v_x_1870_: *mut LeanObject,
    mut v_y_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1872_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0,
    );
    v___x_1873_ = lean_int_mul(v_x_1870_, v___x_1872_);
    v___x_1874_ = lean_int_sub(v___x_1873_, v_y_1871_);
    lean_dec(v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(
    mut v_x_1875_: *mut LeanObject,
    mut v_y_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Std_Time_instHSubOffsetOffset__37___lam__0(v_x_1875_, v_y_1876_);
    lean_dec(v_y_1876_);
    lean_dec(v_x_1875_);
    return v_res_1877_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__38___lam__0(
    mut v_x_1880_: *mut LeanObject,
    mut v_y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Second_Offset_toWeeks___closed__0,
    );
    v___x_1883_ = lean_int_mul(v_x_1880_, v___x_1882_);
    v___x_1884_ = lean_int_sub(v___x_1883_, v_y_1881_);
    lean_dec(v___x_1883_);
    return v___x_1884_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(
    mut v_x_1885_: *mut LeanObject,
    mut v_y_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1887_: *mut LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Std_Time_instHSubOffsetOffset__38___lam__0(v_x_1885_, v_y_1886_);
    lean_dec(v_y_1886_);
    lean_dec(v_x_1885_);
    return v_res_1887_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__39___lam__0(
    mut v_x_1890_: *mut LeanObject,
    mut v_y_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Minute_Offset_toWeeks___closed__0,
    );
    v___x_1893_ = lean_int_mul(v_x_1890_, v___x_1892_);
    v___x_1894_ = lean_int_sub(v___x_1893_, v_y_1891_);
    lean_dec(v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(
    mut v_x_1895_: *mut LeanObject,
    mut v_y_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = l_Std_Time_instHSubOffsetOffset__39___lam__0(v_x_1895_, v_y_1896_);
    lean_dec(v_y_1896_);
    lean_dec(v_x_1895_);
    return v_res_1897_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__40___lam__0(
    mut v_x_1900_: *mut LeanObject,
    mut v_y_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    v___x_1902_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Offset_toWeeks___closed__0_once),
        _init_l_Std_Time_Hour_Offset_toWeeks___closed__0,
    );
    v___x_1903_ = lean_int_mul(v_x_1900_, v___x_1902_);
    v___x_1904_ = lean_int_sub(v___x_1903_, v_y_1901_);
    lean_dec(v___x_1903_);
    return v___x_1904_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(
    mut v_x_1905_: *mut LeanObject,
    mut v_y_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1907_: *mut LeanObject = core::ptr::null_mut();
    v_res_1907_ = l_Std_Time_instHSubOffsetOffset__40___lam__0(v_x_1905_, v_y_1906_);
    lean_dec(v_y_1906_);
    lean_dec(v_x_1905_);
    return v_res_1907_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__41___lam__0(
    mut v_x_1910_: *mut LeanObject,
    mut v_y_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once),
        _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0,
    );
    v___x_1913_ = lean_int_mul(v_x_1910_, v___x_1912_);
    v___x_1914_ = lean_int_sub(v___x_1913_, v_y_1911_);
    lean_dec(v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(
    mut v_x_1915_: *mut LeanObject,
    mut v_y_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ = l_Std_Time_instHSubOffsetOffset__41___lam__0(v_x_1915_, v_y_1916_);
    lean_dec(v_y_1916_);
    lean_dec(v_x_1915_);
    return v_res_1917_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_ValidDate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Date_ValidDate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Date_Basic(builtin);
}
