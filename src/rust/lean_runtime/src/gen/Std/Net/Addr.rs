// Lean compiler output
// Module: Std.Net.Addr
// Imports: Init.System.IO Init.Data.Vector.Basic
use crate::r#gen::Init::Data::Array::DecidableEq::l_Array_instDecidableEqImpl___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_instDecidableEqUInt8___boxed, l_instDecidableEqUInt16___boxed,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint16_to_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_string_dec_eq, lean_uint8_of_nat, lean_uint16_dec_eq, lean_uint16_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint16, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_uint16, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint8_once, lean_uint16_once, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Std_Net_instInhabitedMACAddr_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Net_instInhabitedMACAddr_default___closed__0: u8 = 0;
static mut l_Std_Net_instInhabitedMACAddr_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Net_instInhabitedMACAddr_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedMACAddr_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedMACAddr: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Net_instInhabitedIPv4Addr_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPv4Addr_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPv4Addr: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Net_instInhabitedSocketAddressV4_default___closed__0: u16 = 0;
static mut l_Std_Net_instInhabitedSocketAddressV4_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Net_instInhabitedSocketAddressV4_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddressV4_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddressV4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Net_instInhabitedIPv6Addr_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPv6Addr_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPv6Addr: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Net_instInhabitedSocketAddressV6_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddressV6_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddressV6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedIPAddr_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Net_instInhabitedIPAddr_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPAddr_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedIPAddr: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Net_instInhabitedSocketAddress_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Net_instInhabitedSocketAddress_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddress_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedSocketAddress: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedAddressFamily_default: u8 = 0;
pub static mut l_Std_Net_instInhabitedAddressFamily: u8 = 0;
pub static l_Std_Net_IPv4Addr_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_IPv4Addr_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_IPv4Addr_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv4Addr_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_IPv4Addr_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv4Addr_instToString___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_IPv4Addr_instCoeIPAddr: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_SocketAddressV4_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_SocketAddressV4_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_SocketAddressV4_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV4_instToString___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Net_SocketAddressV4_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV4_instToString___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Net_SocketAddressV4_instCoeSocketAddress: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_IPv6Addr_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_IPv6Addr_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_IPv6Addr_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv6Addr_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_IPv6Addr_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv6Addr_instToString___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_IPv6Addr_instCoeIPAddr: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [93, 58, 0],
    };
static mut l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Net_SocketAddressV6_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_SocketAddressV6_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_SocketAddressV6_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instToString___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Net_SocketAddressV6_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instToString___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Net_SocketAddressV6_instCoeSocketAddress: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Net_IPAddr_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_IPAddr_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_IPAddr_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPAddr_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_IPAddr_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_IPAddr_instToString___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_SocketAddress_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Net_SocketAddress_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Net_SocketAddress_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddress_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Net_SocketAddress_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_SocketAddress_instToString___closed__0_value) as *mut LeanObject;
pub static l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Net_instInhabitedInterfaceAddress_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Net_instInhabitedInterfaceAddress_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedInterfaceAddress_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Net_instInhabitedInterfaceAddress: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Net_instInhabitedMACAddr_default___closed__0() -> u8 {
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    v___x_552_ = lean_unsigned_to_nat(0);
    v___x_553_ = lean_uint8_of_nat(v___x_552_);
    return v___x_553_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedMACAddr_default___closed__1() -> *mut LeanObject {
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__0_once),
        _init_l_Std_Net_instInhabitedMACAddr_default___closed__0,
    );
    v___x_555_ = lean_unsigned_to_nat(6);
    v___x_556_ = lean_box((v___x_554_) as usize);
    v___x_557_ = lean_mk_array(v___x_555_, v___x_556_);
    return v___x_557_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedMACAddr_default() -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__1_once),
        _init_l_Std_Net_instInhabitedMACAddr_default___closed__1,
    );
    return v___x_558_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedMACAddr() -> *mut LeanObject {
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v___x_559_ = l_Std_Net_instInhabitedMACAddr_default;
    return v___x_559_;
}
pub unsafe fn l_Std_Net_instDecidableEqMACAddr_decEq(
    mut v_x_560_: *mut LeanObject,
    mut v_x_561_: *mut LeanObject,
) -> u8 {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: u8 = 0;
    v___x_562_ = lean_alloc_closure(
        l_instDecidableEqUInt8___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_563_ = l_Array_instDecidableEqImpl___redArg(v___x_562_, v_x_560_, v_x_561_);
    return v___x_563_;
}
pub unsafe fn l_Std_Net_instDecidableEqMACAddr_decEq___boxed(
    mut v_x_564_: *mut LeanObject,
    mut v_x_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: u8 = 0;
    let mut v_r_567_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_564_, v_x_565_);
    lean_dec_ref(v_x_565_);
    lean_dec_ref(v_x_564_);
    v_r_567_ = lean_box((v_res_566_) as usize);
    return v_r_567_;
}
pub unsafe fn l_Std_Net_instDecidableEqMACAddr(
    mut v_x_568_: *mut LeanObject,
    mut v_x_569_: *mut LeanObject,
) -> u8 {
    let mut v___x_570_: u8 = 0;
    v___x_570_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_568_, v_x_569_);
    return v___x_570_;
}
pub unsafe fn l_Std_Net_instDecidableEqMACAddr___boxed(
    mut v_x_571_: *mut LeanObject,
    mut v_x_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_573_: u8 = 0;
    let mut v_r_574_: *mut LeanObject = core::ptr::null_mut();
    v_res_573_ = l_Std_Net_instDecidableEqMACAddr(v_x_571_, v_x_572_);
    lean_dec_ref(v_x_572_);
    lean_dec_ref(v_x_571_);
    v_r_574_ = lean_box((v_res_573_) as usize);
    return v_r_574_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0() -> *mut LeanObject {
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    v___x_575_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedMACAddr_default___closed__0_once),
        _init_l_Std_Net_instInhabitedMACAddr_default___closed__0,
    );
    v___x_576_ = lean_unsigned_to_nat(4);
    v___x_577_ = lean_box((v___x_575_) as usize);
    v___x_578_ = lean_mk_array(v___x_576_, v___x_577_);
    return v___x_578_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv4Addr_default() -> *mut LeanObject {
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_579_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPv4Addr_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once),
        _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0,
    );
    return v___x_579_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv4Addr() -> *mut LeanObject {
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = l_Std_Net_instInhabitedIPv4Addr_default;
    return v___x_580_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv4Addr_decEq(
    mut v_x_581_: *mut LeanObject,
    mut v_x_582_: *mut LeanObject,
) -> u8 {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    v___x_583_ = lean_alloc_closure(
        l_instDecidableEqUInt8___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_584_ = l_Array_instDecidableEqImpl___redArg(v___x_583_, v_x_581_, v_x_582_);
    return v___x_584_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(
    mut v_x_585_: *mut LeanObject,
    mut v_x_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_587_: u8 = 0;
    let mut v_r_588_: *mut LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_585_, v_x_586_);
    lean_dec_ref(v_x_586_);
    lean_dec_ref(v_x_585_);
    v_r_588_ = lean_box((v_res_587_) as usize);
    return v_r_588_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv4Addr(
    mut v_x_589_: *mut LeanObject,
    mut v_x_590_: *mut LeanObject,
) -> u8 {
    let mut v___x_591_: u8 = 0;
    v___x_591_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_589_, v_x_590_);
    return v___x_591_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv4Addr___boxed(
    mut v_x_592_: *mut LeanObject,
    mut v_x_593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_594_: u8 = 0;
    let mut v_r_595_: *mut LeanObject = core::ptr::null_mut();
    v_res_594_ = l_Std_Net_instDecidableEqIPv4Addr(v_x_592_, v_x_593_);
    lean_dec_ref(v_x_593_);
    lean_dec_ref(v_x_592_);
    v_r_595_ = lean_box((v_res_594_) as usize);
    return v_r_595_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0() -> u16 {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u16 = 0;
    v___x_596_ = lean_unsigned_to_nat(0);
    v___x_597_ = lean_uint16_of_nat(v___x_596_);
    return v___x_597_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__1() -> *mut LeanObject
{
    let mut v___x_598_: u16 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_598_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once),
        _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0,
    );
    v___x_599_ = l_Std_Net_instInhabitedIPv4Addr_default;
    v___x_600_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v___x_600_, 0, v___x_599_);
    lean_ctor_set_uint16(
        v___x_600_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_598_,
    );
    return v___x_600_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV4_default() -> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__1_once),
        _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__1,
    );
    return v___x_601_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV4() -> *mut LeanObject {
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_602_ = l_Std_Net_instInhabitedSocketAddressV4_default;
    return v___x_602_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV4_decEq(
    mut v_x_603_: *mut LeanObject,
    mut v_x_604_: *mut LeanObject,
) -> u8 {
    let mut v_addr_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_606_: u16 = 0;
    let mut v_addr_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_608_: u16 = 0;
    let mut v___x_609_: u8 = 0;
    v_addr_605_ = lean_ctor_get(v_x_603_, 0);
    v_port_606_ = lean_ctor_get_uint16(
        v_x_603_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_addr_607_ = lean_ctor_get(v_x_604_, 0);
    v_port_608_ = lean_ctor_get_uint16(
        v_x_604_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_609_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_605_, v_addr_607_);
    if v___x_609_ == 0 {
        return v___x_609_;
    } else {
        let mut v___x_610_: u8 = 0;
        v___x_610_ = lean_uint16_dec_eq(v_port_606_, v_port_608_);
        return v___x_610_;
    }
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(
    mut v_x_611_: *mut LeanObject,
    mut v_x_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_613_: u8 = 0;
    let mut v_r_614_: *mut LeanObject = core::ptr::null_mut();
    v_res_613_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_611_, v_x_612_);
    lean_dec_ref(v_x_612_);
    lean_dec_ref(v_x_611_);
    v_r_614_ = lean_box((v_res_613_) as usize);
    return v_r_614_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV4(
    mut v_x_615_: *mut LeanObject,
    mut v_x_616_: *mut LeanObject,
) -> u8 {
    let mut v___x_617_: u8 = 0;
    v___x_617_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_615_, v_x_616_);
    return v___x_617_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV4___boxed(
    mut v_x_618_: *mut LeanObject,
    mut v_x_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_620_: u8 = 0;
    let mut v_r_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_620_ = l_Std_Net_instDecidableEqSocketAddressV4(v_x_618_, v_x_619_);
    lean_dec_ref(v_x_619_);
    lean_dec_ref(v_x_618_);
    v_r_621_ = lean_box((v_res_620_) as usize);
    return v_r_621_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0() -> *mut LeanObject {
    let mut v___x_622_: u16 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once),
        _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0,
    );
    v___x_623_ = lean_unsigned_to_nat(8);
    v___x_624_ = lean_box((v___x_622_) as usize);
    v___x_625_ = lean_mk_array(v___x_623_, v___x_624_);
    return v___x_625_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv6Addr_default() -> *mut LeanObject {
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPv6Addr_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once),
        _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0,
    );
    return v___x_626_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPv6Addr() -> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = l_Std_Net_instInhabitedIPv6Addr_default;
    return v___x_627_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv6Addr_decEq(
    mut v_x_628_: *mut LeanObject,
    mut v_x_629_: *mut LeanObject,
) -> u8 {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    v___x_630_ = lean_alloc_closure(
        l_instDecidableEqUInt16___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_631_ = l_Array_instDecidableEqImpl___redArg(v___x_630_, v_x_628_, v_x_629_);
    return v___x_631_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(
    mut v_x_632_: *mut LeanObject,
    mut v_x_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_634_: u8 = 0;
    let mut v_r_635_: *mut LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_632_, v_x_633_);
    lean_dec_ref(v_x_633_);
    lean_dec_ref(v_x_632_);
    v_r_635_ = lean_box((v_res_634_) as usize);
    return v_r_635_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv6Addr(
    mut v_x_636_: *mut LeanObject,
    mut v_x_637_: *mut LeanObject,
) -> u8 {
    let mut v___x_638_: u8 = 0;
    v___x_638_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_636_, v_x_637_);
    return v___x_638_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPv6Addr___boxed(
    mut v_x_639_: *mut LeanObject,
    mut v_x_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_641_: u8 = 0;
    let mut v_r_642_: *mut LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Std_Net_instDecidableEqIPv6Addr(v_x_639_, v_x_640_);
    lean_dec_ref(v_x_640_);
    lean_dec_ref(v_x_639_);
    v_r_642_ = lean_box((v_res_641_) as usize);
    return v_r_642_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0() -> *mut LeanObject
{
    let mut v___x_643_: u16 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once),
        _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0,
    );
    v___x_644_ = l_Std_Net_instInhabitedIPv6Addr_default;
    v___x_645_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v___x_645_, 0, v___x_644_);
    lean_ctor_set_uint16(
        v___x_645_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_643_,
    );
    return v___x_645_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV6_default() -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV6_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once),
        _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0,
    );
    return v___x_646_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddressV6() -> *mut LeanObject {
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Std_Net_instInhabitedSocketAddressV6_default;
    return v___x_647_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV6_decEq(
    mut v_x_648_: *mut LeanObject,
    mut v_x_649_: *mut LeanObject,
) -> u8 {
    let mut v_addr_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_651_: u16 = 0;
    let mut v_addr_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_653_: u16 = 0;
    let mut v___x_654_: u8 = 0;
    v_addr_650_ = lean_ctor_get(v_x_648_, 0);
    v_port_651_ = lean_ctor_get_uint16(
        v_x_648_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_addr_652_ = lean_ctor_get(v_x_649_, 0);
    v_port_653_ = lean_ctor_get_uint16(
        v_x_649_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_654_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_650_, v_addr_652_);
    if v___x_654_ == 0 {
        return v___x_654_;
    } else {
        let mut v___x_655_: u8 = 0;
        v___x_655_ = lean_uint16_dec_eq(v_port_651_, v_port_653_);
        return v___x_655_;
    }
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(
    mut v_x_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_658_: u8 = 0;
    let mut v_r_659_: *mut LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_656_, v_x_657_);
    lean_dec_ref(v_x_657_);
    lean_dec_ref(v_x_656_);
    v_r_659_ = lean_box((v_res_658_) as usize);
    return v_r_659_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV6(
    mut v_x_660_: *mut LeanObject,
    mut v_x_661_: *mut LeanObject,
) -> u8 {
    let mut v___x_662_: u8 = 0;
    v___x_662_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_660_, v_x_661_);
    return v___x_662_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddressV6___boxed(
    mut v_x_663_: *mut LeanObject,
    mut v_x_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_665_: u8 = 0;
    let mut v_r_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Std_Net_instDecidableEqSocketAddressV6(v_x_663_, v_x_664_);
    lean_dec_ref(v_x_664_);
    lean_dec_ref(v_x_663_);
    v_r_666_ = lean_box((v_res_665_) as usize);
    return v_r_666_;
}
pub unsafe fn l_Std_Net_IPAddr_ctorIdx(mut v_x_667_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_667_) == 0 {
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        v___x_668_ = lean_unsigned_to_nat(0);
        return v___x_668_;
    } else {
        let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
        v___x_669_ = lean_unsigned_to_nat(1);
        return v___x_669_;
    }
}
pub unsafe fn l_Std_Net_IPAddr_ctorIdx___boxed(mut v_x_670_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_671_: *mut LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Std_Net_IPAddr_ctorIdx(v_x_670_);
    lean_dec_ref(v_x_670_);
    return v_res_671_;
}
pub unsafe fn l_Std_Net_IPAddr_ctorElim___redArg(
    mut v_t_672_: *mut LeanObject,
    mut v_k_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addr_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    v_addr_674_ = lean_ctor_get(v_t_672_, 0);
    lean_inc_ref(v_addr_674_);
    lean_dec_ref(v_t_672_);
    v___x_675_ = lean_apply_1(v_k_673_, v_addr_674_);
    return v___x_675_;
}
pub unsafe fn l_Std_Net_IPAddr_ctorElim(
    mut v_motive_676_: *mut LeanObject,
    mut v_ctorIdx_677_: *mut LeanObject,
    mut v_t_678_: *mut LeanObject,
    mut v_h_679_: *mut LeanObject,
    mut v_k_680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v___x_681_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_678_, v_k_680_);
    return v___x_681_;
}
pub unsafe fn l_Std_Net_IPAddr_ctorElim___boxed(
    mut v_motive_682_: *mut LeanObject,
    mut v_ctorIdx_683_: *mut LeanObject,
    mut v_t_684_: *mut LeanObject,
    mut v_h_685_: *mut LeanObject,
    mut v_k_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_687_: *mut LeanObject = core::ptr::null_mut();
    v_res_687_ =
        l_Std_Net_IPAddr_ctorElim(v_motive_682_, v_ctorIdx_683_, v_t_684_, v_h_685_, v_k_686_);
    lean_dec(v_ctorIdx_683_);
    return v_res_687_;
}
pub unsafe fn l_Std_Net_IPAddr_v4_elim___redArg(
    mut v_t_688_: *mut LeanObject,
    mut v_v4_689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_688_, v_v4_689_);
    return v___x_690_;
}
pub unsafe fn l_Std_Net_IPAddr_v4_elim(
    mut v_motive_691_: *mut LeanObject,
    mut v_t_692_: *mut LeanObject,
    mut v_h_693_: *mut LeanObject,
    mut v_v4_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    v___x_695_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_692_, v_v4_694_);
    return v___x_695_;
}
pub unsafe fn l_Std_Net_IPAddr_v6_elim___redArg(
    mut v_t_696_: *mut LeanObject,
    mut v_v6_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_696_, v_v6_697_);
    return v___x_698_;
}
pub unsafe fn l_Std_Net_IPAddr_v6_elim(
    mut v_motive_699_: *mut LeanObject,
    mut v_t_700_: *mut LeanObject,
    mut v_h_701_: *mut LeanObject,
    mut v_v6_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_700_, v_v6_702_);
    return v___x_703_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPAddr_default___closed__0() -> *mut LeanObject {
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Std_Net_instInhabitedIPv4Addr_default;
    v___x_705_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_705_, 0, v___x_704_);
    return v___x_705_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPAddr_default() -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPAddr_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedIPAddr_default___closed__0_once),
        _init_l_Std_Net_instInhabitedIPAddr_default___closed__0,
    );
    return v___x_706_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedIPAddr() -> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Std_Net_instInhabitedIPAddr_default;
    return v___x_707_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPAddr_decEq(
    mut v_x_708_: *mut LeanObject,
    mut v_x_709_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_708_) == 0 {
        if lean_obj_tag(v_x_709_) == 0 {
            let mut v_addr_710_: *mut LeanObject = core::ptr::null_mut();
            let mut v_addr_711_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_712_: u8 = 0;
            v_addr_710_ = lean_ctor_get(v_x_708_, 0);
            v_addr_711_ = lean_ctor_get(v_x_709_, 0);
            v___x_712_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_710_, v_addr_711_);
            return v___x_712_;
        } else {
            let mut v___x_713_: u8 = 0;
            v___x_713_ = 0;
            return v___x_713_;
        }
    } else {
        if lean_obj_tag(v_x_709_) == 0 {
            let mut v___x_714_: u8 = 0;
            v___x_714_ = 0;
            return v___x_714_;
        } else {
            let mut v_addr_715_: *mut LeanObject = core::ptr::null_mut();
            let mut v_addr_716_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_717_: u8 = 0;
            v_addr_715_ = lean_ctor_get(v_x_708_, 0);
            v_addr_716_ = lean_ctor_get(v_x_709_, 0);
            v___x_717_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_715_, v_addr_716_);
            return v___x_717_;
        }
    }
}
pub unsafe fn l_Std_Net_instDecidableEqIPAddr_decEq___boxed(
    mut v_x_718_: *mut LeanObject,
    mut v_x_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: u8 = 0;
    let mut v_r_721_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_718_, v_x_719_);
    lean_dec_ref(v_x_719_);
    lean_dec_ref(v_x_718_);
    v_r_721_ = lean_box((v_res_720_) as usize);
    return v_r_721_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPAddr(
    mut v_x_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
) -> u8 {
    let mut v___x_724_: u8 = 0;
    v___x_724_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_722_, v_x_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Net_instDecidableEqIPAddr___boxed(
    mut v_x_725_: *mut LeanObject,
    mut v_x_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_727_: u8 = 0;
    let mut v_r_728_: *mut LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Std_Net_instDecidableEqIPAddr(v_x_725_, v_x_726_);
    lean_dec_ref(v_x_726_);
    lean_dec_ref(v_x_725_);
    v_r_728_ = lean_box((v_res_727_) as usize);
    return v_r_728_;
}
pub unsafe fn l_Std_Net_SocketAddress_ctorIdx(mut v_x_729_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_729_) == 0 {
        let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
        v___x_730_ = lean_unsigned_to_nat(0);
        return v___x_730_;
    } else {
        let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
        v___x_731_ = lean_unsigned_to_nat(1);
        return v___x_731_;
    }
}
pub unsafe fn l_Std_Net_SocketAddress_ctorIdx___boxed(
    mut v_x_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_733_: *mut LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Std_Net_SocketAddress_ctorIdx(v_x_732_);
    lean_dec_ref(v_x_732_);
    return v_res_733_;
}
pub unsafe fn l_Std_Net_SocketAddress_ctorElim___redArg(
    mut v_t_734_: *mut LeanObject,
    mut v_k_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addr_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v_addr_736_ = lean_ctor_get(v_t_734_, 0);
    lean_inc_ref(v_addr_736_);
    lean_dec_ref(v_t_734_);
    v___x_737_ = lean_apply_1(v_k_735_, v_addr_736_);
    return v___x_737_;
}
pub unsafe fn l_Std_Net_SocketAddress_ctorElim(
    mut v_motive_738_: *mut LeanObject,
    mut v_ctorIdx_739_: *mut LeanObject,
    mut v_t_740_: *mut LeanObject,
    mut v_h_741_: *mut LeanObject,
    mut v_k_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_740_, v_k_742_);
    return v___x_743_;
}
pub unsafe fn l_Std_Net_SocketAddress_ctorElim___boxed(
    mut v_motive_744_: *mut LeanObject,
    mut v_ctorIdx_745_: *mut LeanObject,
    mut v_t_746_: *mut LeanObject,
    mut v_h_747_: *mut LeanObject,
    mut v_k_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_749_: *mut LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Std_Net_SocketAddress_ctorElim(
        v_motive_744_,
        v_ctorIdx_745_,
        v_t_746_,
        v_h_747_,
        v_k_748_,
    );
    lean_dec(v_ctorIdx_745_);
    return v_res_749_;
}
pub unsafe fn l_Std_Net_SocketAddress_v4_elim___redArg(
    mut v_t_750_: *mut LeanObject,
    mut v_v4_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_750_, v_v4_751_);
    return v___x_752_;
}
pub unsafe fn l_Std_Net_SocketAddress_v4_elim(
    mut v_motive_753_: *mut LeanObject,
    mut v_t_754_: *mut LeanObject,
    mut v_h_755_: *mut LeanObject,
    mut v_v4_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_754_, v_v4_756_);
    return v___x_757_;
}
pub unsafe fn l_Std_Net_SocketAddress_v6_elim___redArg(
    mut v_t_758_: *mut LeanObject,
    mut v_v6_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_758_, v_v6_759_);
    return v___x_760_;
}
pub unsafe fn l_Std_Net_SocketAddress_v6_elim(
    mut v_motive_761_: *mut LeanObject,
    mut v_t_762_: *mut LeanObject,
    mut v_h_763_: *mut LeanObject,
    mut v_v6_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_762_, v_v6_764_);
    return v___x_765_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0() -> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Std_Net_instInhabitedSocketAddressV4_default;
    v___x_767_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_767_, 0, v___x_766_);
    return v___x_767_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddress_default() -> *mut LeanObject {
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    v___x_768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddress_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedSocketAddress_default___closed__0_once),
        _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0,
    );
    return v___x_768_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedSocketAddress() -> *mut LeanObject {
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Std_Net_instInhabitedSocketAddress_default;
    return v___x_769_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddress_decEq(
    mut v_x_770_: *mut LeanObject,
    mut v_x_771_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_770_) == 0 {
        if lean_obj_tag(v_x_771_) == 0 {
            let mut v_addr_772_: *mut LeanObject = core::ptr::null_mut();
            let mut v_addr_773_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_774_: u8 = 0;
            v_addr_772_ = lean_ctor_get(v_x_770_, 0);
            v_addr_773_ = lean_ctor_get(v_x_771_, 0);
            v___x_774_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_addr_772_, v_addr_773_);
            return v___x_774_;
        } else {
            let mut v___x_775_: u8 = 0;
            v___x_775_ = 0;
            return v___x_775_;
        }
    } else {
        if lean_obj_tag(v_x_771_) == 0 {
            let mut v___x_776_: u8 = 0;
            v___x_776_ = 0;
            return v___x_776_;
        } else {
            let mut v_addr_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v_addr_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_779_: u8 = 0;
            v_addr_777_ = lean_ctor_get(v_x_770_, 0);
            v_addr_778_ = lean_ctor_get(v_x_771_, 0);
            v___x_779_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_addr_777_, v_addr_778_);
            return v___x_779_;
        }
    }
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(
    mut v_x_780_: *mut LeanObject,
    mut v_x_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_782_: u8 = 0;
    let mut v_r_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_780_, v_x_781_);
    lean_dec_ref(v_x_781_);
    lean_dec_ref(v_x_780_);
    v_r_783_ = lean_box((v_res_782_) as usize);
    return v_r_783_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddress(
    mut v_x_784_: *mut LeanObject,
    mut v_x_785_: *mut LeanObject,
) -> u8 {
    let mut v___x_786_: u8 = 0;
    v___x_786_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_784_, v_x_785_);
    return v___x_786_;
}
pub unsafe fn l_Std_Net_instDecidableEqSocketAddress___boxed(
    mut v_x_787_: *mut LeanObject,
    mut v_x_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_789_: u8 = 0;
    let mut v_r_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_789_ = l_Std_Net_instDecidableEqSocketAddress(v_x_787_, v_x_788_);
    lean_dec_ref(v_x_788_);
    lean_dec_ref(v_x_787_);
    v_r_790_ = lean_box((v_res_789_) as usize);
    return v_r_790_;
}
pub unsafe fn l_Std_Net_AddressFamily_ctorIdx(mut v_x_791_: u8) -> *mut LeanObject {
    if v_x_791_ == 0 {
        let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
        v___x_792_ = lean_unsigned_to_nat(0);
        return v___x_792_;
    } else {
        let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
        v___x_793_ = lean_unsigned_to_nat(1);
        return v___x_793_;
    }
}
pub unsafe fn l_Std_Net_AddressFamily_ctorIdx___boxed(
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_795_: u8 = 0;
    let mut v_res_796_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_795_ = (lean_unbox(v_x_794_) as u8);
    v_res_796_ = l_Std_Net_AddressFamily_ctorIdx(v_x_boxed_795_);
    return v_res_796_;
}
pub unsafe fn l_Std_Net_AddressFamily_toCtorIdx(mut v_x_797_: u8) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Std_Net_AddressFamily_ctorIdx(v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Std_Net_AddressFamily_toCtorIdx___boxed(
    mut v_x_799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_800_: u8 = 0;
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_800_ = (lean_unbox(v_x_799_) as u8);
    v_res_801_ = l_Std_Net_AddressFamily_toCtorIdx(v_x_4__boxed_800_);
    return v_res_801_;
}
pub unsafe fn l_Std_Net_AddressFamily_ctorElim___redArg(
    mut v_k_802_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_802_);
    return v_k_802_;
}
pub unsafe fn l_Std_Net_AddressFamily_ctorElim___redArg___boxed(
    mut v_k_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Std_Net_AddressFamily_ctorElim___redArg(v_k_803_);
    lean_dec(v_k_803_);
    return v_res_804_;
}
pub unsafe fn l_Std_Net_AddressFamily_ctorElim(
    mut v_motive_805_: *mut LeanObject,
    mut v_ctorIdx_806_: *mut LeanObject,
    mut v_t_807_: u8,
    mut v_h_808_: *mut LeanObject,
    mut v_k_809_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_809_);
    return v_k_809_;
}
pub unsafe fn l_Std_Net_AddressFamily_ctorElim___boxed(
    mut v_motive_810_: *mut LeanObject,
    mut v_ctorIdx_811_: *mut LeanObject,
    mut v_t_812_: *mut LeanObject,
    mut v_h_813_: *mut LeanObject,
    mut v_k_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_815_: u8 = 0;
    let mut v_res_816_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_815_ = (lean_unbox(v_t_812_) as u8);
    v_res_816_ = l_Std_Net_AddressFamily_ctorElim(
        v_motive_810_,
        v_ctorIdx_811_,
        v_t_boxed_815_,
        v_h_813_,
        v_k_814_,
    );
    lean_dec(v_k_814_);
    lean_dec(v_ctorIdx_811_);
    return v_res_816_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv4_elim___redArg(
    mut v_ipv4_817_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ipv4_817_);
    return v_ipv4_817_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(
    mut v_ipv4_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Std_Net_AddressFamily_ipv4_elim___redArg(v_ipv4_818_);
    lean_dec(v_ipv4_818_);
    return v_res_819_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv4_elim(
    mut v_motive_820_: *mut LeanObject,
    mut v_t_821_: u8,
    mut v_h_822_: *mut LeanObject,
    mut v_ipv4_823_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ipv4_823_);
    return v_ipv4_823_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv4_elim___boxed(
    mut v_motive_824_: *mut LeanObject,
    mut v_t_825_: *mut LeanObject,
    mut v_h_826_: *mut LeanObject,
    mut v_ipv4_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_828_: u8 = 0;
    let mut v_res_829_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_828_ = (lean_unbox(v_t_825_) as u8);
    v_res_829_ =
        l_Std_Net_AddressFamily_ipv4_elim(v_motive_824_, v_t_boxed_828_, v_h_826_, v_ipv4_827_);
    lean_dec(v_ipv4_827_);
    return v_res_829_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv6_elim___redArg(
    mut v_ipv6_830_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ipv6_830_);
    return v_ipv6_830_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(
    mut v_ipv6_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_832_: *mut LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Std_Net_AddressFamily_ipv6_elim___redArg(v_ipv6_831_);
    lean_dec(v_ipv6_831_);
    return v_res_832_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv6_elim(
    mut v_motive_833_: *mut LeanObject,
    mut v_t_834_: u8,
    mut v_h_835_: *mut LeanObject,
    mut v_ipv6_836_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ipv6_836_);
    return v_ipv6_836_;
}
pub unsafe fn l_Std_Net_AddressFamily_ipv6_elim___boxed(
    mut v_motive_837_: *mut LeanObject,
    mut v_t_838_: *mut LeanObject,
    mut v_h_839_: *mut LeanObject,
    mut v_ipv6_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_841_: u8 = 0;
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_841_ = (lean_unbox(v_t_838_) as u8);
    v_res_842_ =
        l_Std_Net_AddressFamily_ipv6_elim(v_motive_837_, v_t_boxed_841_, v_h_839_, v_ipv6_840_);
    lean_dec(v_ipv6_840_);
    return v_res_842_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedAddressFamily_default() -> u8 {
    let mut v___x_843_: u8 = 0;
    v___x_843_ = 0;
    return v___x_843_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedAddressFamily() -> u8 {
    let mut v___x_844_: u8 = 0;
    v___x_844_ = 0;
    return v___x_844_;
}
pub unsafe fn l_Std_Net_AddressFamily_ofNat(mut v_n_845_: *mut LeanObject) -> u8 {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    v___x_846_ = lean_unsigned_to_nat(0);
    v___x_847_ = lean_nat_dec_le(v_n_845_, v___x_846_);
    if v___x_847_ == 0 {
        let mut v___x_848_: u8 = 0;
        v___x_848_ = 1;
        return v___x_848_;
    } else {
        let mut v___x_849_: u8 = 0;
        v___x_849_ = 0;
        return v___x_849_;
    }
}
pub unsafe fn l_Std_Net_AddressFamily_ofNat___boxed(
    mut v_n_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_851_: u8 = 0;
    let mut v_r_852_: *mut LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Std_Net_AddressFamily_ofNat(v_n_850_);
    lean_dec(v_n_850_);
    v_r_852_ = lean_box((v_res_851_) as usize);
    return v_r_852_;
}
pub unsafe fn l_Std_Net_instDecidableEqAddressFamily(mut v_x_853_: u8, mut v_y_854_: u8) -> u8 {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: u8 = 0;
    v___x_855_ = l_Std_Net_AddressFamily_ctorIdx(v_x_853_);
    v___x_856_ = l_Std_Net_AddressFamily_ctorIdx(v_y_854_);
    v___x_857_ = lean_nat_dec_eq(v___x_855_, v___x_856_);
    lean_dec(v___x_856_);
    lean_dec(v___x_855_);
    return v___x_857_;
}
pub unsafe fn l_Std_Net_instDecidableEqAddressFamily___boxed(
    mut v_x_858_: *mut LeanObject,
    mut v_y_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_860_: u8 = 0;
    let mut v_y_14__boxed_861_: u8 = 0;
    let mut v_res_862_: u8 = 0;
    let mut v_r_863_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_860_ = (lean_unbox(v_x_858_) as u8);
    v_y_14__boxed_861_ = (lean_unbox(v_y_859_) as u8);
    v_res_862_ = l_Std_Net_instDecidableEqAddressFamily(v_x_13__boxed_860_, v_y_14__boxed_861_);
    v_r_863_ = lean_box((v_res_862_) as usize);
    return v_r_863_;
}
pub unsafe fn l_Std_Net_IPv4Addr_ofParts(
    mut v_a_864_: u8,
    mut v_b_865_: u8,
    mut v_c_866_: u8,
    mut v_d_867_: u8,
) -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ = lean_unsigned_to_nat(4);
    v___x_869_ = lean_mk_empty_array_with_capacity(v___x_868_);
    v___x_870_ = lean_box((v_a_864_) as usize);
    v___x_871_ = lean_array_push(v___x_869_, v___x_870_);
    v___x_872_ = lean_box((v_b_865_) as usize);
    v___x_873_ = lean_array_push(v___x_871_, v___x_872_);
    v___x_874_ = lean_box((v_c_866_) as usize);
    v___x_875_ = lean_array_push(v___x_873_, v___x_874_);
    v___x_876_ = lean_box((v_d_867_) as usize);
    v___x_877_ = lean_array_push(v___x_875_, v___x_876_);
    return v___x_877_;
}
pub unsafe fn l_Std_Net_IPv4Addr_ofParts___boxed(
    mut v_a_878_: *mut LeanObject,
    mut v_b_879_: *mut LeanObject,
    mut v_c_880_: *mut LeanObject,
    mut v_d_881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_882_: u8 = 0;
    let mut v_b_boxed_883_: u8 = 0;
    let mut v_c_boxed_884_: u8 = 0;
    let mut v_d_boxed_885_: u8 = 0;
    let mut v_res_886_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_882_ = (lean_unbox(v_a_878_) as u8);
    v_b_boxed_883_ = (lean_unbox(v_b_879_) as u8);
    v_c_boxed_884_ = (lean_unbox(v_c_880_) as u8);
    v_d_boxed_885_ = (lean_unbox(v_d_881_) as u8);
    v_res_886_ = l_Std_Net_IPv4Addr_ofParts(
        v_a_boxed_882_,
        v_b_boxed_883_,
        v_c_boxed_884_,
        v_d_boxed_885_,
    );
    return v_res_886_;
}
pub unsafe fn l_Std_Net_IPv4Addr_ofString___boxed(
    mut v_s_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ = lean_uv_pton_v4(v_s_888_);
    lean_dec_ref(v_s_888_);
    return v_res_889_;
}
pub unsafe fn l_Std_Net_IPv4Addr_toString___boxed(
    mut v_addr_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_892_: *mut LeanObject = core::ptr::null_mut();
    v_res_892_ = lean_uv_ntop_v4(v_addr_891_);
    lean_dec_ref(v_addr_891_);
    return v_res_892_;
}
pub unsafe fn l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(
    mut v_addr_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_896_, 0, v_addr_895_);
    return v___x_896_;
}
pub unsafe fn l_Std_Net_SocketAddressV4_instToString___lam__0(
    mut v_sa_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addr_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_902_: u16 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v_addr_901_ = lean_ctor_get(v_sa_900_, 0);
    v_port_902_ = lean_ctor_get_uint16(
        v_sa_900_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_903_ = lean_uv_ntop_v4(v_addr_901_);
    v___x_904_ = l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0;
    v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
    v___x_906_ = lean_uint16_to_nat(v_port_902_);
    v___x_907_ = l_Nat_reprFast(v___x_906_);
    v___x_908_ = lean_string_append(v___x_905_, v___x_907_);
    lean_dec_ref(v___x_907_);
    return v___x_908_;
}
pub unsafe fn l_Std_Net_SocketAddressV4_instToString___lam__0___boxed(
    mut v_sa_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Std_Net_SocketAddressV4_instToString___lam__0(v_sa_909_);
    lean_dec_ref(v_sa_909_);
    return v_res_910_;
}
pub unsafe fn l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(
    mut v_addr_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v_addr_913_);
    return v___x_914_;
}
pub unsafe fn l_Std_Net_IPv6Addr_ofParts(
    mut v_a_917_: u16,
    mut v_b_918_: u16,
    mut v_c_919_: u16,
    mut v_d_920_: u16,
    mut v_e_921_: u16,
    mut v_f_922_: u16,
    mut v_g_923_: u16,
    mut v_h_924_: u16,
) -> *mut LeanObject {
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___x_925_ = lean_unsigned_to_nat(8);
    v___x_926_ = lean_mk_empty_array_with_capacity(v___x_925_);
    v___x_927_ = lean_box((v_a_917_) as usize);
    v___x_928_ = lean_array_push(v___x_926_, v___x_927_);
    v___x_929_ = lean_box((v_b_918_) as usize);
    v___x_930_ = lean_array_push(v___x_928_, v___x_929_);
    v___x_931_ = lean_box((v_c_919_) as usize);
    v___x_932_ = lean_array_push(v___x_930_, v___x_931_);
    v___x_933_ = lean_box((v_d_920_) as usize);
    v___x_934_ = lean_array_push(v___x_932_, v___x_933_);
    v___x_935_ = lean_box((v_e_921_) as usize);
    v___x_936_ = lean_array_push(v___x_934_, v___x_935_);
    v___x_937_ = lean_box((v_f_922_) as usize);
    v___x_938_ = lean_array_push(v___x_936_, v___x_937_);
    v___x_939_ = lean_box((v_g_923_) as usize);
    v___x_940_ = lean_array_push(v___x_938_, v___x_939_);
    v___x_941_ = lean_box((v_h_924_) as usize);
    v___x_942_ = lean_array_push(v___x_940_, v___x_941_);
    return v___x_942_;
}
pub unsafe fn l_Std_Net_IPv6Addr_ofParts___boxed(
    mut v_a_943_: *mut LeanObject,
    mut v_b_944_: *mut LeanObject,
    mut v_c_945_: *mut LeanObject,
    mut v_d_946_: *mut LeanObject,
    mut v_e_947_: *mut LeanObject,
    mut v_f_948_: *mut LeanObject,
    mut v_g_949_: *mut LeanObject,
    mut v_h_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_951_: u16 = 0;
    let mut v_b_boxed_952_: u16 = 0;
    let mut v_c_boxed_953_: u16 = 0;
    let mut v_d_boxed_954_: u16 = 0;
    let mut v_e_boxed_955_: u16 = 0;
    let mut v_f_boxed_956_: u16 = 0;
    let mut v_g_boxed_957_: u16 = 0;
    let mut v_h_boxed_958_: u16 = 0;
    let mut v_res_959_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_951_ = (lean_unbox(v_a_943_) as u16);
    v_b_boxed_952_ = (lean_unbox(v_b_944_) as u16);
    v_c_boxed_953_ = (lean_unbox(v_c_945_) as u16);
    v_d_boxed_954_ = (lean_unbox(v_d_946_) as u16);
    v_e_boxed_955_ = (lean_unbox(v_e_947_) as u16);
    v_f_boxed_956_ = (lean_unbox(v_f_948_) as u16);
    v_g_boxed_957_ = (lean_unbox(v_g_949_) as u16);
    v_h_boxed_958_ = (lean_unbox(v_h_950_) as u16);
    v_res_959_ = l_Std_Net_IPv6Addr_ofParts(
        v_a_boxed_951_,
        v_b_boxed_952_,
        v_c_boxed_953_,
        v_d_boxed_954_,
        v_e_boxed_955_,
        v_f_boxed_956_,
        v_g_boxed_957_,
        v_h_boxed_958_,
    );
    return v_res_959_;
}
pub unsafe fn l_Std_Net_IPv6Addr_ofString___boxed(
    mut v_s_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_962_: *mut LeanObject = core::ptr::null_mut();
    v_res_962_ = lean_uv_pton_v6(v_s_961_);
    lean_dec_ref(v_s_961_);
    return v_res_962_;
}
pub unsafe fn l_Std_Net_IPv6Addr_toString___boxed(
    mut v_addr_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_965_: *mut LeanObject = core::ptr::null_mut();
    v_res_965_ = lean_uv_ntop_v6(v_addr_964_);
    lean_dec_ref(v_addr_964_);
    return v_res_965_;
}
pub unsafe fn l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(
    mut v_addr_968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    v___x_969_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_969_, 0, v_addr_968_);
    return v___x_969_;
}
pub unsafe fn l_Std_Net_SocketAddressV6_instToString___lam__0(
    mut v_sa_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addr_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_976_: u16 = 0;
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v_addr_975_ = lean_ctor_get(v_sa_974_, 0);
    v_port_976_ = lean_ctor_get_uint16(
        v_sa_974_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_977_ = l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0;
    v___x_978_ = lean_uv_ntop_v6(v_addr_975_);
    v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
    lean_dec_ref(v___x_978_);
    v___x_980_ = l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1;
    v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
    v___x_982_ = lean_uint16_to_nat(v_port_976_);
    v___x_983_ = l_Nat_reprFast(v___x_982_);
    v___x_984_ = lean_string_append(v___x_981_, v___x_983_);
    lean_dec_ref(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Std_Net_SocketAddressV6_instToString___lam__0___boxed(
    mut v_sa_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_986_: *mut LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Std_Net_SocketAddressV6_instToString___lam__0(v_sa_985_);
    lean_dec_ref(v_sa_985_);
    return v_res_986_;
}
pub unsafe fn l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(
    mut v_addr_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    v___x_990_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_990_, 0, v_addr_989_);
    return v___x_990_;
}
pub unsafe fn l_Std_Net_IPAddr_family(mut v_x_993_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_993_) == 0 {
        let mut v___x_994_: u8 = 0;
        v___x_994_ = 0;
        return v___x_994_;
    } else {
        let mut v___x_995_: u8 = 0;
        v___x_995_ = 1;
        return v___x_995_;
    }
}
pub unsafe fn l_Std_Net_IPAddr_family___boxed(mut v_x_996_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_997_: u8 = 0;
    let mut v_r_998_: *mut LeanObject = core::ptr::null_mut();
    v_res_997_ = l_Std_Net_IPAddr_family(v_x_996_);
    lean_dec_ref(v_x_996_);
    v_r_998_ = lean_box((v_res_997_) as usize);
    return v_r_998_;
}
pub unsafe fn l_Std_Net_IPAddr_toString(mut v_x_999_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_999_) == 0 {
        let mut v_addr_1000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
        v_addr_1000_ = lean_ctor_get(v_x_999_, 0);
        v___x_1001_ = lean_uv_ntop_v4(v_addr_1000_);
        return v___x_1001_;
    } else {
        let mut v_addr_1002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
        v_addr_1002_ = lean_ctor_get(v_x_999_, 0);
        v___x_1003_ = lean_uv_ntop_v6(v_addr_1002_);
        return v___x_1003_;
    }
}
pub unsafe fn l_Std_Net_IPAddr_toString___boxed(mut v_x_1004_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1005_: *mut LeanObject = core::ptr::null_mut();
    v_res_1005_ = l_Std_Net_IPAddr_toString(v_x_1004_);
    lean_dec_ref(v_x_1004_);
    return v_res_1005_;
}
pub unsafe fn l_Std_Net_SocketAddress_instToString___lam__0(
    mut v_x_1008_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1008_) == 0 {
        let mut v_addr_1009_: *mut LeanObject = core::ptr::null_mut();
        let mut v_addr_1010_: *mut LeanObject = core::ptr::null_mut();
        let mut v_port_1011_: u16 = 0;
        let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
        v_addr_1009_ = lean_ctor_get(v_x_1008_, 0);
        v_addr_1010_ = lean_ctor_get(v_addr_1009_, 0);
        v_port_1011_ = lean_ctor_get_uint16(
            v_addr_1009_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_1012_ = lean_uv_ntop_v4(v_addr_1010_);
        v___x_1013_ = l_Std_Net_SocketAddressV4_instToString___lam__0___closed__0;
        v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
        v___x_1015_ = lean_uint16_to_nat(v_port_1011_);
        v___x_1016_ = l_Nat_reprFast(v___x_1015_);
        v___x_1017_ = lean_string_append(v___x_1014_, v___x_1016_);
        lean_dec_ref(v___x_1016_);
        return v___x_1017_;
    } else {
        let mut v_addr_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v_addr_1019_: *mut LeanObject = core::ptr::null_mut();
        let mut v_port_1020_: u16 = 0;
        let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
        v_addr_1018_ = lean_ctor_get(v_x_1008_, 0);
        v_addr_1019_ = lean_ctor_get(v_addr_1018_, 0);
        v_port_1020_ = lean_ctor_get_uint16(
            v_addr_1018_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_1021_ = l_Std_Net_SocketAddressV6_instToString___lam__0___closed__0;
        v___x_1022_ = lean_uv_ntop_v6(v_addr_1019_);
        v___x_1023_ = lean_string_append(v___x_1021_, v___x_1022_);
        lean_dec_ref(v___x_1022_);
        v___x_1024_ = l_Std_Net_SocketAddressV6_instToString___lam__0___closed__1;
        v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
        v___x_1026_ = lean_uint16_to_nat(v_port_1020_);
        v___x_1027_ = l_Nat_reprFast(v___x_1026_);
        v___x_1028_ = lean_string_append(v___x_1025_, v___x_1027_);
        lean_dec_ref(v___x_1027_);
        return v___x_1028_;
    }
}
pub unsafe fn l_Std_Net_SocketAddress_instToString___lam__0___boxed(
    mut v_x_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Std_Net_SocketAddress_instToString___lam__0(v_x_1029_);
    lean_dec_ref(v_x_1029_);
    return v_res_1030_;
}
pub unsafe fn l_Std_Net_SocketAddress_family(mut v_x_1033_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1033_) == 0 {
        let mut v___x_1034_: u8 = 0;
        v___x_1034_ = 0;
        return v___x_1034_;
    } else {
        let mut v___x_1035_: u8 = 0;
        v___x_1035_ = 1;
        return v___x_1035_;
    }
}
pub unsafe fn l_Std_Net_SocketAddress_family___boxed(
    mut v_x_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1037_: u8 = 0;
    let mut v_r_1038_: *mut LeanObject = core::ptr::null_mut();
    v_res_1037_ = l_Std_Net_SocketAddress_family(v_x_1036_);
    lean_dec_ref(v_x_1036_);
    v_r_1038_ = lean_box((v_res_1037_) as usize);
    return v_r_1038_;
}
pub unsafe fn l_Std_Net_SocketAddress_ipAddr(mut v_x_1039_: *mut LeanObject) -> *mut LeanObject {
    let mut v_addr_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v_addr_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut v_addr_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v_addr_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1039_) == 0 {
                    v_addr_1040_ = lean_ctor_get(v_x_1039_, 0);
                    v_isSharedCheck_1048_ = (!lean_is_exclusive(v_x_1039_)) as u8;
                    if v_isSharedCheck_1048_ == 0 {
                        v___x_1042_ = v_x_1039_;
                        v_isShared_1043_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_addr_1040_);
                        lean_dec(v_x_1039_);
                        v___x_1042_ = lean_box(0);
                        v_isShared_1043_ = v_isSharedCheck_1048_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_addr_1049_ = lean_ctor_get(v_x_1039_, 0);
                    v_isSharedCheck_1057_ = (!lean_is_exclusive(v_x_1039_)) as u8;
                    if v_isSharedCheck_1057_ == 0 {
                        v___x_1051_ = v_x_1039_;
                        v_isShared_1052_ = v_isSharedCheck_1057_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_addr_1049_);
                        lean_dec(v_x_1039_);
                        v___x_1051_ = lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1057_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_addr_1044_ = lean_ctor_get(v_addr_1040_, 0);
                lean_inc_ref(v_addr_1044_);
                lean_dec_ref(v_addr_1040_);
                if v_isShared_1043_ == 0 {
                    lean_ctor_set(v___x_1042_, 0, v_addr_1044_);
                    v___x_1046_ = v___x_1042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_addr_1044_);
                    v___x_1046_ = v_reuseFailAlloc_1047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1046_;
            }
            3 => {
                v_addr_1053_ = lean_ctor_get(v_addr_1049_, 0);
                lean_inc_ref(v_addr_1053_);
                lean_dec_ref(v_addr_1049_);
                if v_isShared_1052_ == 0 {
                    lean_ctor_set(v___x_1051_, 0, v_addr_1053_);
                    v___x_1055_ = v___x_1051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_addr_1053_);
                    v___x_1055_ = v_reuseFailAlloc_1056_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Net_SocketAddress_port(mut v_x_1058_: *mut LeanObject) -> u16 {
    let mut v_addr_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_port_1060_: u16 = 0;
    v_addr_1059_ = lean_ctor_get(v_x_1058_, 0);
    v_port_1060_ = lean_ctor_get_uint16(
        v_addr_1059_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    return v_port_1060_;
}
pub unsafe fn l_Std_Net_SocketAddress_port___boxed(
    mut v_x_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: u16 = 0;
    let mut v_r_1063_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Std_Net_SocketAddress_port(v_x_1061_);
    lean_dec_ref(v_x_1061_);
    v_r_1063_ = lean_box((v_res_1062_) as usize);
    return v_r_1063_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1() -> *mut LeanObject
{
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    v___x_1065_ = l_Std_Net_instInhabitedIPAddr_default;
    v___x_1066_ = 0;
    v___x_1067_ = l_Std_Net_instInhabitedMACAddr_default;
    v___x_1068_ = l_Std_Net_instInhabitedInterfaceAddress_default___closed__0;
    v___x_1069_ = lean_alloc_ctor(0, 4, (1) as u32);
    lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    lean_ctor_set(v___x_1069_, 2, v___x_1065_);
    lean_ctor_set(v___x_1069_, 3, v___x_1065_);
    lean_ctor_set_uint8(
        v___x_1069_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_1066_,
    );
    return v___x_1069_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedInterfaceAddress_default() -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedInterfaceAddress_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once),
        _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1,
    );
    return v___x_1070_;
}
pub unsafe fn _init_l_Std_Net_instInhabitedInterfaceAddress() -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = l_Std_Net_instInhabitedInterfaceAddress_default;
    return v___x_1071_;
}
pub unsafe fn l_Std_Net_instDecidableEqInterfaceAddress_decEq(
    mut v_x_1072_: *mut LeanObject,
    mut v_x_1073_: *mut LeanObject,
) -> u8 {
    let mut v_name_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_physicalAddress_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLoopback_1076_: u8 = 0;
    let mut v_address_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_netMask_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_physicalAddress_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLoopback_1081_: u8 = 0;
    let mut v_address_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_netMask_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1074_ = lean_ctor_get(v_x_1072_, 0);
                v_physicalAddress_1075_ = lean_ctor_get(v_x_1072_, 1);
                v_isLoopback_1076_ = lean_ctor_get_uint8(
                    v_x_1072_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_address_1077_ = lean_ctor_get(v_x_1072_, 2);
                v_netMask_1078_ = lean_ctor_get(v_x_1072_, 3);
                v_name_1079_ = lean_ctor_get(v_x_1073_, 0);
                v_physicalAddress_1080_ = lean_ctor_get(v_x_1073_, 1);
                v_isLoopback_1081_ = lean_ctor_get_uint8(
                    v_x_1073_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_address_1082_ = lean_ctor_get(v_x_1073_, 2);
                v_netMask_1083_ = lean_ctor_get(v_x_1073_, 3);
                v___x_1087_ = lean_string_dec_eq(v_name_1074_, v_name_1079_);
                if v___x_1087_ == 0 {
                    return v___x_1087_;
                } else {
                    v___x_1088_ = l_Std_Net_instDecidableEqMACAddr_decEq(
                        v_physicalAddress_1075_,
                        v_physicalAddress_1080_,
                    );
                    if v___x_1088_ == 0 {
                        return v___x_1088_;
                    } else {
                        if v_isLoopback_1076_ == 0 {
                            if v_isLoopback_1081_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                return v_isLoopback_1076_;
                            }
                        } else {
                            if v_isLoopback_1081_ == 0 {
                                return v_isLoopback_1081_;
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1085_ =
                    l_Std_Net_instDecidableEqIPAddr_decEq(v_address_1077_, v_address_1082_);
                if v___x_1085_ == 0 {
                    return v___x_1085_;
                } else {
                    v___x_1086_ =
                        l_Std_Net_instDecidableEqIPAddr_decEq(v_netMask_1078_, v_netMask_1083_);
                    return v___x_1086_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(
    mut v_x_1089_: *mut LeanObject,
    mut v_x_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1091_: u8 = 0;
    let mut v_r_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_1089_, v_x_1090_);
    lean_dec_ref(v_x_1090_);
    lean_dec_ref(v_x_1089_);
    v_r_1092_ = lean_box((v_res_1091_) as usize);
    return v_r_1092_;
}
pub unsafe fn l_Std_Net_instDecidableEqInterfaceAddress(
    mut v_x_1093_: *mut LeanObject,
    mut v_x_1094_: *mut LeanObject,
) -> u8 {
    let mut v___x_1095_: u8 = 0;
    v___x_1095_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_1093_, v_x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_Std_Net_instDecidableEqInterfaceAddress___boxed(
    mut v_x_1096_: *mut LeanObject,
    mut v_x_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1098_: u8 = 0;
    let mut v_r_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_1096_, v_x_1097_);
    lean_dec_ref(v_x_1097_);
    lean_dec_ref(v_x_1096_);
    v_r_1099_ = lean_box((v_res_1098_) as usize);
    return v_r_1099_;
}
pub unsafe fn l_Std_Net_interfaceAddresses___boxed(
    mut v_a_00___x40___internal___hyg_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1102_: *mut LeanObject = core::ptr::null_mut();
    v_res_1102_ = lean_uv_interface_addresses();
    return v_res_1102_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Net_Addr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Net_instInhabitedMACAddr_default = _init_l_Std_Net_instInhabitedMACAddr_default();
    lean_mark_persistent(l_Std_Net_instInhabitedMACAddr_default);
    l_Std_Net_instInhabitedMACAddr = _init_l_Std_Net_instInhabitedMACAddr();
    lean_mark_persistent(l_Std_Net_instInhabitedMACAddr);
    l_Std_Net_instInhabitedIPv4Addr_default = _init_l_Std_Net_instInhabitedIPv4Addr_default();
    lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr_default);
    l_Std_Net_instInhabitedIPv4Addr = _init_l_Std_Net_instInhabitedIPv4Addr();
    lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr);
    l_Std_Net_instInhabitedSocketAddressV4_default =
        _init_l_Std_Net_instInhabitedSocketAddressV4_default();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4_default);
    l_Std_Net_instInhabitedSocketAddressV4 = _init_l_Std_Net_instInhabitedSocketAddressV4();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4);
    l_Std_Net_instInhabitedIPv6Addr_default = _init_l_Std_Net_instInhabitedIPv6Addr_default();
    lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr_default);
    l_Std_Net_instInhabitedIPv6Addr = _init_l_Std_Net_instInhabitedIPv6Addr();
    lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr);
    l_Std_Net_instInhabitedSocketAddressV6_default =
        _init_l_Std_Net_instInhabitedSocketAddressV6_default();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6_default);
    l_Std_Net_instInhabitedSocketAddressV6 = _init_l_Std_Net_instInhabitedSocketAddressV6();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6);
    l_Std_Net_instInhabitedIPAddr_default = _init_l_Std_Net_instInhabitedIPAddr_default();
    lean_mark_persistent(l_Std_Net_instInhabitedIPAddr_default);
    l_Std_Net_instInhabitedIPAddr = _init_l_Std_Net_instInhabitedIPAddr();
    lean_mark_persistent(l_Std_Net_instInhabitedIPAddr);
    l_Std_Net_instInhabitedSocketAddress_default =
        _init_l_Std_Net_instInhabitedSocketAddress_default();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress_default);
    l_Std_Net_instInhabitedSocketAddress = _init_l_Std_Net_instInhabitedSocketAddress();
    lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress);
    l_Std_Net_instInhabitedAddressFamily_default =
        _init_l_Std_Net_instInhabitedAddressFamily_default();
    l_Std_Net_instInhabitedAddressFamily = _init_l_Std_Net_instInhabitedAddressFamily();
    l_Std_Net_instInhabitedInterfaceAddress_default =
        _init_l_Std_Net_instInhabitedInterfaceAddress_default();
    lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress_default);
    l_Std_Net_instInhabitedInterfaceAddress = _init_l_Std_Net_instInhabitedInterfaceAddress();
    lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Net_Addr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Net_Addr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Net_Addr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Net_Addr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Net_Addr(builtin);
}
