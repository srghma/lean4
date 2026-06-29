// Lean compiler output
// Module: Init.Data.Ord.Basic
// Imports: Init.ByCases Init.Ext Init.PropLemmas Init.Data.Char.Basic Init.Classical
use crate::ffi::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_to_int, lean_uint32_dec_eq, lean_uint32_dec_lt,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static mut l_instInhabitedOrdering_default: u8 = 0;
pub static mut l_instInhabitedOrdering: u8 = 0;
pub static l_instReprOrdering_repr___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [79, 114, 100, 101, 114, 105, 110, 103, 46, 108, 116, 0],
    };
static mut l_instReprOrdering_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprOrdering_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprOrdering_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprOrdering_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instReprOrdering_repr___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [79, 114, 100, 101, 114, 105, 110, 103, 46, 101, 113, 0],
    };
static mut l_instReprOrdering_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instReprOrdering_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprOrdering_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprOrdering_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_instReprOrdering_repr___closed__4_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [79, 114, 100, 101, 114, 105, 110, 103, 46, 103, 116, 0],
    };
static mut l_instReprOrdering_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_instReprOrdering_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprOrdering_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprOrdering_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering_repr___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_instReprOrdering_repr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprOrdering_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instReprOrdering_repr___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprOrdering_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprOrdering___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprOrdering_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprOrdering___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprOrdering: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprOrdering___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instOrdNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrdNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrdNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instOrdInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrdInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrdInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instOrdBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrdBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrdBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdChar___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instOrdChar___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrdChar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrdChar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdOrdering___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Ordering_ctorIdx___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrdOrdering___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdOrdering___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrdOrdering___closed__1_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instOrdNat___closed__0_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instOrdOrdering___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instOrdOrdering___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdOrdering___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrdOrdering: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrdOrdering___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_lexOrd___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_lexOrd___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_lexOrd___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_lexOrd___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_lexOrd___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_lexOrd___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_lexOrd___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_lexOrd___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Ordering_ctorIdx(mut v_x_755_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_755_ {
        0 => {
            let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_756_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_756_;
        }
        1 => {
            let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_757_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_757_;
        }
        _ => {
            let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_758_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_758_;
        }
    }
}
pub unsafe fn l_Ordering_ctorIdx___boxed(
    mut v_x_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_760_: u8 = 0;
    let mut v_res_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_760_ = (crate::leanh::lean_unbox(v_x_759_) as u8);
    v_res_761_ = l_Ordering_ctorIdx(v_x_boxed_760_);
    return v_res_761_;
}
pub unsafe fn l_Ordering_toCtorIdx(mut v_x_762_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Ordering_ctorIdx(v_x_762_);
    return v___x_763_;
}
pub unsafe fn l_Ordering_toCtorIdx___boxed(
    mut v_x_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_765_: u8 = 0;
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_765_ = (crate::leanh::lean_unbox(v_x_764_) as u8);
    v_res_766_ = l_Ordering_toCtorIdx(v_x_4__boxed_765_);
    return v_res_766_;
}
pub unsafe fn l_Ordering_ctorElim___redArg(
    mut v_k_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_767_);
    return v_k_767_;
}
pub unsafe fn l_Ordering_ctorElim___redArg___boxed(
    mut v_k_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_769_ = l_Ordering_ctorElim___redArg(v_k_768_);
    crate::leanh::lean_dec(v_k_768_);
    return v_res_769_;
}
pub unsafe fn l_Ordering_ctorElim(
    mut v_motive_770_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_771_: *mut crate::leanh::LeanObject,
    mut v_t_772_: u8,
    mut v_h_773_: *mut crate::leanh::LeanObject,
    mut v_k_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_774_);
    return v_k_774_;
}
pub unsafe fn l_Ordering_ctorElim___boxed(
    mut v_motive_775_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_776_: *mut crate::leanh::LeanObject,
    mut v_t_777_: *mut crate::leanh::LeanObject,
    mut v_h_778_: *mut crate::leanh::LeanObject,
    mut v_k_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_780_: u8 = 0;
    let mut v_res_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_780_ = (crate::leanh::lean_unbox(v_t_777_) as u8);
    v_res_781_ = l_Ordering_ctorElim(
        v_motive_775_,
        v_ctorIdx_776_,
        v_t_boxed_780_,
        v_h_778_,
        v_k_779_,
    );
    crate::leanh::lean_dec(v_k_779_);
    crate::leanh::lean_dec(v_ctorIdx_776_);
    return v_res_781_;
}
pub unsafe fn l_Ordering_lt_elim___redArg(
    mut v_lt_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lt_782_);
    return v_lt_782_;
}
pub unsafe fn l_Ordering_lt_elim___redArg___boxed(
    mut v_lt_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Ordering_lt_elim___redArg(v_lt_783_);
    crate::leanh::lean_dec(v_lt_783_);
    return v_res_784_;
}
pub unsafe fn l_Ordering_lt_elim(
    mut v_motive_785_: *mut crate::leanh::LeanObject,
    mut v_t_786_: u8,
    mut v_h_787_: *mut crate::leanh::LeanObject,
    mut v_lt_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lt_788_);
    return v_lt_788_;
}
pub unsafe fn l_Ordering_lt_elim___boxed(
    mut v_motive_789_: *mut crate::leanh::LeanObject,
    mut v_t_790_: *mut crate::leanh::LeanObject,
    mut v_h_791_: *mut crate::leanh::LeanObject,
    mut v_lt_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_793_: u8 = 0;
    let mut v_res_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_793_ = (crate::leanh::lean_unbox(v_t_790_) as u8);
    v_res_794_ = l_Ordering_lt_elim(v_motive_789_, v_t_boxed_793_, v_h_791_, v_lt_792_);
    crate::leanh::lean_dec(v_lt_792_);
    return v_res_794_;
}
pub unsafe fn l_Ordering_eq_elim___redArg(
    mut v_eq_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_eq_795_);
    return v_eq_795_;
}
pub unsafe fn l_Ordering_eq_elim___redArg___boxed(
    mut v_eq_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Ordering_eq_elim___redArg(v_eq_796_);
    crate::leanh::lean_dec(v_eq_796_);
    return v_res_797_;
}
pub unsafe fn l_Ordering_eq_elim(
    mut v_motive_798_: *mut crate::leanh::LeanObject,
    mut v_t_799_: u8,
    mut v_h_800_: *mut crate::leanh::LeanObject,
    mut v_eq_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_eq_801_);
    return v_eq_801_;
}
pub unsafe fn l_Ordering_eq_elim___boxed(
    mut v_motive_802_: *mut crate::leanh::LeanObject,
    mut v_t_803_: *mut crate::leanh::LeanObject,
    mut v_h_804_: *mut crate::leanh::LeanObject,
    mut v_eq_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_806_: u8 = 0;
    let mut v_res_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_806_ = (crate::leanh::lean_unbox(v_t_803_) as u8);
    v_res_807_ = l_Ordering_eq_elim(v_motive_802_, v_t_boxed_806_, v_h_804_, v_eq_805_);
    crate::leanh::lean_dec(v_eq_805_);
    return v_res_807_;
}
pub unsafe fn l_Ordering_gt_elim___redArg(
    mut v_gt_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_gt_808_);
    return v_gt_808_;
}
pub unsafe fn l_Ordering_gt_elim___redArg___boxed(
    mut v_gt_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Ordering_gt_elim___redArg(v_gt_809_);
    crate::leanh::lean_dec(v_gt_809_);
    return v_res_810_;
}
pub unsafe fn l_Ordering_gt_elim(
    mut v_motive_811_: *mut crate::leanh::LeanObject,
    mut v_t_812_: u8,
    mut v_h_813_: *mut crate::leanh::LeanObject,
    mut v_gt_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_gt_814_);
    return v_gt_814_;
}
pub unsafe fn l_Ordering_gt_elim___boxed(
    mut v_motive_815_: *mut crate::leanh::LeanObject,
    mut v_t_816_: *mut crate::leanh::LeanObject,
    mut v_h_817_: *mut crate::leanh::LeanObject,
    mut v_gt_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_819_: u8 = 0;
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_819_ = (crate::leanh::lean_unbox(v_t_816_) as u8);
    v_res_820_ = l_Ordering_gt_elim(v_motive_815_, v_t_boxed_819_, v_h_817_, v_gt_818_);
    crate::leanh::lean_dec(v_gt_818_);
    return v_res_820_;
}
pub unsafe fn _init_l_instInhabitedOrdering_default() -> u8 {
    let mut v___x_821_: u8 = 0;
    v___x_821_ = 0;
    return v___x_821_;
}
pub unsafe fn _init_l_instInhabitedOrdering() -> u8 {
    let mut v___x_822_: u8 = 0;
    v___x_822_ = 0;
    return v___x_822_;
}
pub unsafe fn l_Ordering_ofNat(mut v_n_823_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    v___x_824_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_825_ = lean_nat_dec_le(v_n_823_, v___x_824_);
    if v___x_825_ == 0 {
        let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_827_: u8 = 0;
        v___x_826_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_827_ = lean_nat_dec_le(v_n_823_, v___x_826_);
        if v___x_827_ == 0 {
            let mut v___x_828_: u8 = 0;
            v___x_828_ = 2;
            return v___x_828_;
        } else {
            let mut v___x_829_: u8 = 0;
            v___x_829_ = 1;
            return v___x_829_;
        }
    } else {
        let mut v___x_830_: u8 = 0;
        v___x_830_ = 0;
        return v___x_830_;
    }
}
pub unsafe fn l_Ordering_ofNat___boxed(
    mut v_n_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: u8 = 0;
    let mut v_r_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Ordering_ofNat(v_n_831_);
    crate::leanh::lean_dec(v_n_831_);
    v_r_833_ = crate::leanh::lean_box((v_res_832_) as usize);
    return v_r_833_;
}
pub unsafe fn l_instDecidableEqOrdering(mut v_x_834_: u8, mut v_y_835_: u8) -> u8 {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: u8 = 0;
    v___x_836_ = l_Ordering_ctorIdx(v_x_834_);
    v___x_837_ = l_Ordering_ctorIdx(v_y_835_);
    v___x_838_ = lean_nat_dec_eq(v___x_836_, v___x_837_);
    crate::leanh::lean_dec(v___x_837_);
    crate::leanh::lean_dec(v___x_836_);
    return v___x_838_;
}
pub unsafe fn l_instDecidableEqOrdering___boxed(
    mut v_x_839_: *mut crate::leanh::LeanObject,
    mut v_y_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_841_: u8 = 0;
    let mut v_y_14__boxed_842_: u8 = 0;
    let mut v_res_843_: u8 = 0;
    let mut v_r_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_841_ = (crate::leanh::lean_unbox(v_x_839_) as u8);
    v_y_14__boxed_842_ = (crate::leanh::lean_unbox(v_y_840_) as u8);
    v_res_843_ = l_instDecidableEqOrdering(v_x_13__boxed_841_, v_y_14__boxed_842_);
    v_r_844_ = crate::leanh::lean_box((v_res_843_) as usize);
    return v_r_844_;
}
pub unsafe fn _init_l_instReprOrdering_repr___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_855_ = lean_nat_to_int(v___x_854_);
    return v___x_855_;
}
pub unsafe fn _init_l_instReprOrdering_repr___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_857_ = lean_nat_to_int(v___x_856_);
    return v___x_857_;
}
pub unsafe fn l_instReprOrdering_repr(
    mut v_x_858_: u8,
    mut v_prec_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_858_ {
                0 => {
                    v___x_881_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_882_ = lean_nat_dec_le(v___x_881_, v_prec_859_);
                    if v___x_882_ == 0 {
                        v___x_883_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6_once),
                            _init_l_instReprOrdering_repr___closed__6,
                        );
                        v___y_861_ = v___x_883_;
                        state = 1;
                        continue;
                    } else {
                        v___x_884_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7_once),
                            _init_l_instReprOrdering_repr___closed__7,
                        );
                        v___y_861_ = v___x_884_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_885_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_886_ = lean_nat_dec_le(v___x_885_, v_prec_859_);
                    if v___x_886_ == 0 {
                        v___x_887_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6_once),
                            _init_l_instReprOrdering_repr___closed__6,
                        );
                        v___y_868_ = v___x_887_;
                        state = 2;
                        continue;
                    } else {
                        v___x_888_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7_once),
                            _init_l_instReprOrdering_repr___closed__7,
                        );
                        v___y_868_ = v___x_888_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_889_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_890_ = lean_nat_dec_le(v___x_889_, v_prec_859_);
                    if v___x_890_ == 0 {
                        v___x_891_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__6_once),
                            _init_l_instReprOrdering_repr___closed__6,
                        );
                        v___y_875_ = v___x_891_;
                        state = 3;
                        continue;
                    } else {
                        v___x_892_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7),
                            core::ptr::addr_of_mut!(l_instReprOrdering_repr___closed__7_once),
                            _init_l_instReprOrdering_repr___closed__7,
                        );
                        v___y_875_ = v___x_892_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_862_ = l_instReprOrdering_repr___closed__1;
                crate::leanh::lean_inc(v___y_861_);
                v___x_863_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_863_, 0, v___y_861_);
                crate::leanh::lean_ctor_set(v___x_863_, 1, v___x_862_);
                v___x_864_ = 0;
                v___x_865_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_863_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_865_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_864_,
                );
                v___x_866_ = l_Repr_addAppParen(v___x_865_, v_prec_859_);
                return v___x_866_;
            }
            2 => {
                v___x_869_ = l_instReprOrdering_repr___closed__3;
                crate::leanh::lean_inc(v___y_868_);
                v___x_870_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_870_, 0, v___y_868_);
                crate::leanh::lean_ctor_set(v___x_870_, 1, v___x_869_);
                v___x_871_ = 0;
                v___x_872_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_870_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_871_,
                );
                v___x_873_ = l_Repr_addAppParen(v___x_872_, v_prec_859_);
                return v___x_873_;
            }
            3 => {
                v___x_876_ = l_instReprOrdering_repr___closed__5;
                crate::leanh::lean_inc(v___y_875_);
                v___x_877_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_877_, 0, v___y_875_);
                crate::leanh::lean_ctor_set(v___x_877_, 1, v___x_876_);
                v___x_878_ = 0;
                v___x_879_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_879_, 0, v___x_877_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_879_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_878_,
                );
                v___x_880_ = l_Repr_addAppParen(v___x_879_, v_prec_859_);
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprOrdering_repr___boxed(
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v_prec_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_895_: u8 = 0;
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_895_ = (crate::leanh::lean_unbox(v_x_893_) as u8);
    v_res_896_ = l_instReprOrdering_repr(v_x_177__boxed_895_, v_prec_894_);
    crate::leanh::lean_dec(v_prec_894_);
    return v_res_896_;
}
pub unsafe fn l_Ordering_swap(mut v_x_899_: u8) -> u8 {
    match v_x_899_ {
        0 => {
            let mut v___x_900_: u8 = 0;
            v___x_900_ = 2;
            return v___x_900_;
        }
        1 => {
            return v_x_899_;
        }
        _ => {
            let mut v___x_901_: u8 = 0;
            v___x_901_ = 0;
            return v___x_901_;
        }
    }
}
pub unsafe fn l_Ordering_swap___boxed(
    mut v_x_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_25__boxed_903_: u8 = 0;
    let mut v_res_904_: u8 = 0;
    let mut v_r_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_903_ = (crate::leanh::lean_unbox(v_x_902_) as u8);
    v_res_904_ = l_Ordering_swap(v_x_25__boxed_903_);
    v_r_905_ = crate::leanh::lean_box((v_res_904_) as usize);
    return v_r_905_;
}
pub unsafe fn l_Ordering_isEq(mut v_x_906_: u8) -> u8 {
    if v_x_906_ == 1 {
        let mut v___x_907_: u8 = 0;
        v___x_907_ = 1;
        return v___x_907_;
    } else {
        let mut v___x_908_: u8 = 0;
        v___x_908_ = 0;
        return v___x_908_;
    }
}
pub unsafe fn l_Ordering_isEq___boxed(
    mut v_x_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_910_: u8 = 0;
    let mut v_res_911_: u8 = 0;
    let mut v_r_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_910_ = (crate::leanh::lean_unbox(v_x_909_) as u8);
    v_res_911_ = l_Ordering_isEq(v_x_21__boxed_910_);
    v_r_912_ = crate::leanh::lean_box((v_res_911_) as usize);
    return v_r_912_;
}
pub unsafe fn l_Ordering_isNe(mut v_x_913_: u8) -> u8 {
    if v_x_913_ == 1 {
        let mut v___x_914_: u8 = 0;
        v___x_914_ = 0;
        return v___x_914_;
    } else {
        let mut v___x_915_: u8 = 0;
        v___x_915_ = 1;
        return v___x_915_;
    }
}
pub unsafe fn l_Ordering_isNe___boxed(
    mut v_x_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_917_: u8 = 0;
    let mut v_res_918_: u8 = 0;
    let mut v_r_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_917_ = (crate::leanh::lean_unbox(v_x_916_) as u8);
    v_res_918_ = l_Ordering_isNe(v_x_21__boxed_917_);
    v_r_919_ = crate::leanh::lean_box((v_res_918_) as usize);
    return v_r_919_;
}
pub unsafe fn l_Ordering_isLE(mut v_x_920_: u8) -> u8 {
    if v_x_920_ == 2 {
        let mut v___x_921_: u8 = 0;
        v___x_921_ = 0;
        return v___x_921_;
    } else {
        let mut v___x_922_: u8 = 0;
        v___x_922_ = 1;
        return v___x_922_;
    }
}
pub unsafe fn l_Ordering_isLE___boxed(
    mut v_x_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_924_: u8 = 0;
    let mut v_res_925_: u8 = 0;
    let mut v_r_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_924_ = (crate::leanh::lean_unbox(v_x_923_) as u8);
    v_res_925_ = l_Ordering_isLE(v_x_21__boxed_924_);
    v_r_926_ = crate::leanh::lean_box((v_res_925_) as usize);
    return v_r_926_;
}
pub unsafe fn l_Ordering_isLT(mut v_x_927_: u8) -> u8 {
    if v_x_927_ == 0 {
        let mut v___x_928_: u8 = 0;
        v___x_928_ = 1;
        return v___x_928_;
    } else {
        let mut v___x_929_: u8 = 0;
        v___x_929_ = 0;
        return v___x_929_;
    }
}
pub unsafe fn l_Ordering_isLT___boxed(
    mut v_x_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_931_: u8 = 0;
    let mut v_res_932_: u8 = 0;
    let mut v_r_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_931_ = (crate::leanh::lean_unbox(v_x_930_) as u8);
    v_res_932_ = l_Ordering_isLT(v_x_21__boxed_931_);
    v_r_933_ = crate::leanh::lean_box((v_res_932_) as usize);
    return v_r_933_;
}
pub unsafe fn l_Ordering_isGT(mut v_x_934_: u8) -> u8 {
    if v_x_934_ == 2 {
        let mut v___x_935_: u8 = 0;
        v___x_935_ = 1;
        return v___x_935_;
    } else {
        let mut v___x_936_: u8 = 0;
        v___x_936_ = 0;
        return v___x_936_;
    }
}
pub unsafe fn l_Ordering_isGT___boxed(
    mut v_x_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_938_: u8 = 0;
    let mut v_res_939_: u8 = 0;
    let mut v_r_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_938_ = (crate::leanh::lean_unbox(v_x_937_) as u8);
    v_res_939_ = l_Ordering_isGT(v_x_21__boxed_938_);
    v_r_940_ = crate::leanh::lean_box((v_res_939_) as usize);
    return v_r_940_;
}
pub unsafe fn l_Ordering_isGE(mut v_x_941_: u8) -> u8 {
    if v_x_941_ == 0 {
        let mut v___x_942_: u8 = 0;
        v___x_942_ = 0;
        return v___x_942_;
    } else {
        let mut v___x_943_: u8 = 0;
        v___x_943_ = 1;
        return v___x_943_;
    }
}
pub unsafe fn l_Ordering_isGE___boxed(
    mut v_x_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_945_: u8 = 0;
    let mut v_res_946_: u8 = 0;
    let mut v_r_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_945_ = (crate::leanh::lean_unbox(v_x_944_) as u8);
    v_res_946_ = l_Ordering_isGE(v_x_21__boxed_945_);
    v_r_947_ = crate::leanh::lean_box((v_res_946_) as usize);
    return v_r_947_;
}
pub unsafe fn l_Ordering_instDecidableForallOfDecidablePred___redArg(
    mut v_inst_948_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_949_: u8 = 0;
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: u8 = 0;
    v___x_949_ = 0;
    v___x_950_ = crate::leanh::lean_box((v___x_949_) as usize);
    crate::leanh::lean_inc_ref(v_inst_948_);
    v___x_951_ = crate::leanh::lean_apply_1(v_inst_948_, v___x_950_);
    v___x_952_ = (crate::leanh::lean_unbox(v___x_951_) as u8);
    if v___x_952_ == 0 {
        let mut v___x_953_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_948_);
        v___x_953_ = (crate::leanh::lean_unbox(v___x_951_) as u8);
        return v___x_953_;
    } else {
        let mut v___x_954_: u8 = 0;
        let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_957_: u8 = 0;
        v___x_954_ = 1;
        v___x_955_ = crate::leanh::lean_box((v___x_954_) as usize);
        crate::leanh::lean_inc_ref(v_inst_948_);
        v___x_956_ = crate::leanh::lean_apply_1(v_inst_948_, v___x_955_);
        v___x_957_ = (crate::leanh::lean_unbox(v___x_956_) as u8);
        if v___x_957_ == 0 {
            let mut v___x_958_: u8 = 0;
            crate::leanh::lean_dec_ref(v_inst_948_);
            v___x_958_ = (crate::leanh::lean_unbox(v___x_956_) as u8);
            return v___x_958_;
        } else {
            let mut v___x_959_: u8 = 0;
            let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_962_: u8 = 0;
            v___x_959_ = 2;
            v___x_960_ = crate::leanh::lean_box((v___x_959_) as usize);
            v___x_961_ = crate::leanh::lean_apply_1(v_inst_948_, v___x_960_);
            v___x_962_ = (crate::leanh::lean_unbox(v___x_961_) as u8);
            return v___x_962_;
        }
    }
}
pub unsafe fn l_Ordering_instDecidableForallOfDecidablePred___redArg___boxed(
    mut v_inst_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_964_: u8 = 0;
    let mut v_r_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_963_);
    v_r_965_ = crate::leanh::lean_box((v_res_964_) as usize);
    return v_r_965_;
}
pub unsafe fn l_Ordering_instDecidableForallOfDecidablePred(
    mut v_p_966_: *mut crate::leanh::LeanObject,
    mut v_inst_967_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_968_: u8 = 0;
    v___x_968_ = l_Ordering_instDecidableForallOfDecidablePred___redArg(v_inst_967_);
    return v___x_968_;
}
pub unsafe fn l_Ordering_instDecidableForallOfDecidablePred___boxed(
    mut v_p_969_: *mut crate::leanh::LeanObject,
    mut v_inst_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_971_: u8 = 0;
    let mut v_r_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Ordering_instDecidableForallOfDecidablePred(v_p_969_, v_inst_970_);
    v_r_972_ = crate::leanh::lean_box((v_res_971_) as usize);
    return v_r_972_;
}
pub unsafe fn l_Ordering_instDecidableExistsOfDecidablePred___redArg(
    mut v_inst_973_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    v___x_974_ = 0;
    v___x_975_ = crate::leanh::lean_box((v___x_974_) as usize);
    crate::leanh::lean_inc_ref(v_inst_973_);
    v___x_976_ = crate::leanh::lean_apply_1(v_inst_973_, v___x_975_);
    v___x_977_ = (crate::leanh::lean_unbox(v___x_976_) as u8);
    if v___x_977_ == 0 {
        let mut v___x_978_: u8 = 0;
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: u8 = 0;
        v___x_978_ = 1;
        v___x_979_ = crate::leanh::lean_box((v___x_978_) as usize);
        crate::leanh::lean_inc_ref(v_inst_973_);
        v___x_980_ = crate::leanh::lean_apply_1(v_inst_973_, v___x_979_);
        v___x_981_ = (crate::leanh::lean_unbox(v___x_980_) as u8);
        if v___x_981_ == 0 {
            let mut v___x_982_: u8 = 0;
            let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_985_: u8 = 0;
            v___x_982_ = 2;
            v___x_983_ = crate::leanh::lean_box((v___x_982_) as usize);
            v___x_984_ = crate::leanh::lean_apply_1(v_inst_973_, v___x_983_);
            v___x_985_ = (crate::leanh::lean_unbox(v___x_984_) as u8);
            return v___x_985_;
        } else {
            let mut v___x_986_: u8 = 0;
            crate::leanh::lean_dec_ref(v_inst_973_);
            v___x_986_ = (crate::leanh::lean_unbox(v___x_980_) as u8);
            return v___x_986_;
        }
    } else {
        let mut v___x_987_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_973_);
        v___x_987_ = (crate::leanh::lean_unbox(v___x_976_) as u8);
        return v___x_987_;
    }
}
pub unsafe fn l_Ordering_instDecidableExistsOfDecidablePred___redArg___boxed(
    mut v_inst_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_989_: u8 = 0;
    let mut v_r_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_988_);
    v_r_990_ = crate::leanh::lean_box((v_res_989_) as usize);
    return v_r_990_;
}
pub unsafe fn l_Ordering_instDecidableExistsOfDecidablePred(
    mut v_p_991_: *mut crate::leanh::LeanObject,
    mut v_inst_992_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_993_: u8 = 0;
    v___x_993_ = l_Ordering_instDecidableExistsOfDecidablePred___redArg(v_inst_992_);
    return v___x_993_;
}
pub unsafe fn l_Ordering_instDecidableExistsOfDecidablePred___boxed(
    mut v_p_994_: *mut crate::leanh::LeanObject,
    mut v_inst_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_996_: u8 = 0;
    let mut v_r_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Ordering_instDecidableExistsOfDecidablePred(v_p_994_, v_inst_995_);
    v_r_997_ = crate::leanh::lean_box((v_res_996_) as usize);
    return v_r_997_;
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(
    mut v_a_998_: u8,
    mut v_h__1_999_: *mut crate::leanh::LeanObject,
    mut v_h__2_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_998_ == 1 {
        let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1000_);
        v___x_1001_ = crate::leanh::lean_box(0);
        v___x_1002_ = crate::leanh::lean_apply_1(v_h__1_999_, v___x_1001_);
        return v___x_1002_;
    } else {
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_999_);
        v___x_1003_ = crate::leanh::lean_box((v_a_998_) as usize);
        v___x_1004_ =
            crate::leanh::lean_apply_2(v_h__2_1000_, v___x_1003_, crate::leanh::lean_box(0));
        return v___x_1004_;
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg___boxed(
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_h__1_1006_: *mut crate::leanh::LeanObject,
    mut v_h__2_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_17__boxed_1008_: u8 = 0;
    let mut v_res_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_17__boxed_1008_ = (crate::leanh::lean_unbox(v_a_1005_) as u8);
    v_res_1009_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___redArg(
        v_a_17__boxed_1008_,
        v_h__1_1006_,
        v_h__2_1007_,
    );
    return v_res_1009_;
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(
    mut v_motive_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: u8,
    mut v_h__1_1012_: *mut crate::leanh::LeanObject,
    mut v_h__2_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_1011_ == 1 {
        let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1013_);
        v___x_1014_ = crate::leanh::lean_box(0);
        v___x_1015_ = crate::leanh::lean_apply_1(v_h__1_1012_, v___x_1014_);
        return v___x_1015_;
    } else {
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1012_);
        v___x_1016_ = crate::leanh::lean_box((v_a_1011_) as usize);
        v___x_1017_ =
            crate::leanh::lean_apply_2(v_h__2_1013_, v___x_1016_, crate::leanh::lean_box(0));
        return v___x_1017_;
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter___boxed(
    mut v_motive_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_h__1_1020_: *mut crate::leanh::LeanObject,
    mut v_h__2_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_28__boxed_1022_: u8 = 0;
    let mut v_res_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_28__boxed_1022_ = (crate::leanh::lean_unbox(v_a_1019_) as u8);
    v_res_1023_ = l___private_Init_Data_Ord_Basic_0__Ordering_then_match__1_splitter(
        v_motive_1018_,
        v_a_28__boxed_1022_,
        v_h__1_1020_,
        v_h__2_1021_,
    );
    return v_res_1023_;
}
pub unsafe fn l_compareOfLessAndEq___redArg(
    mut v_x_1024_: *mut crate::leanh::LeanObject,
    mut v_y_1025_: *mut crate::leanh::LeanObject,
    mut v_inst_1026_: u8,
    mut v_inst_1027_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_inst_1026_ == 0 {
        let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: u8 = 0;
        v___x_1028_ = crate::leanh::lean_apply_2(v_inst_1027_, v_x_1024_, v_y_1025_);
        v___x_1029_ = (crate::leanh::lean_unbox(v___x_1028_) as u8);
        if v___x_1029_ == 0 {
            let mut v___x_1030_: u8 = 0;
            v___x_1030_ = 2;
            return v___x_1030_;
        } else {
            let mut v___x_1031_: u8 = 0;
            v___x_1031_ = 1;
            return v___x_1031_;
        }
    } else {
        let mut v___x_1032_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_1027_);
        crate::leanh::lean_dec(v_y_1025_);
        crate::leanh::lean_dec(v_x_1024_);
        v___x_1032_ = 0;
        return v___x_1032_;
    }
}
pub unsafe fn l_compareOfLessAndEq___redArg___boxed(
    mut v_x_1033_: *mut crate::leanh::LeanObject,
    mut v_y_1034_: *mut crate::leanh::LeanObject,
    mut v_inst_1035_: *mut crate::leanh::LeanObject,
    mut v_inst_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_23__boxed_1037_: u8 = 0;
    let mut v_res_1038_: u8 = 0;
    let mut v_r_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_23__boxed_1037_ = (crate::leanh::lean_unbox(v_inst_1035_) as u8);
    v_res_1038_ =
        l_compareOfLessAndEq___redArg(v_x_1033_, v_y_1034_, v_inst_23__boxed_1037_, v_inst_1036_);
    v_r_1039_ = crate::leanh::lean_box((v_res_1038_) as usize);
    return v_r_1039_;
}
pub unsafe fn l_compareOfLessAndEq(
    mut v_00_u03b1_1040_: *mut crate::leanh::LeanObject,
    mut v_x_1041_: *mut crate::leanh::LeanObject,
    mut v_y_1042_: *mut crate::leanh::LeanObject,
    mut v_inst_1043_: *mut crate::leanh::LeanObject,
    mut v_inst_1044_: u8,
    mut v_inst_1045_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_inst_1044_ == 0 {
        let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: u8 = 0;
        v___x_1046_ = crate::leanh::lean_apply_2(v_inst_1045_, v_x_1041_, v_y_1042_);
        v___x_1047_ = (crate::leanh::lean_unbox(v___x_1046_) as u8);
        if v___x_1047_ == 0 {
            let mut v___x_1048_: u8 = 0;
            v___x_1048_ = 2;
            return v___x_1048_;
        } else {
            let mut v___x_1049_: u8 = 0;
            v___x_1049_ = 1;
            return v___x_1049_;
        }
    } else {
        let mut v___x_1050_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_1045_);
        crate::leanh::lean_dec(v_y_1042_);
        crate::leanh::lean_dec(v_x_1041_);
        v___x_1050_ = 0;
        return v___x_1050_;
    }
}
pub unsafe fn l_compareOfLessAndEq___boxed(
    mut v_00_u03b1_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: *mut crate::leanh::LeanObject,
    mut v_y_1053_: *mut crate::leanh::LeanObject,
    mut v_inst_1054_: *mut crate::leanh::LeanObject,
    mut v_inst_1055_: *mut crate::leanh::LeanObject,
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_40__boxed_1057_: u8 = 0;
    let mut v_res_1058_: u8 = 0;
    let mut v_r_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_40__boxed_1057_ = (crate::leanh::lean_unbox(v_inst_1055_) as u8);
    v_res_1058_ = l_compareOfLessAndEq(
        v_00_u03b1_1051_,
        v_x_1052_,
        v_y_1053_,
        v_inst_1054_,
        v_inst_40__boxed_1057_,
        v_inst_1056_,
    );
    v_r_1059_ = crate::leanh::lean_box((v_res_1058_) as usize);
    return v_r_1059_;
}
pub unsafe fn l_compareOfLessAndBEq___redArg(
    mut v_x_1060_: *mut crate::leanh::LeanObject,
    mut v_y_1061_: *mut crate::leanh::LeanObject,
    mut v_inst_1062_: u8,
    mut v_inst_1063_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_inst_1062_ == 0 {
        let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: u8 = 0;
        v___x_1064_ = crate::leanh::lean_apply_2(v_inst_1063_, v_x_1060_, v_y_1061_);
        v___x_1065_ = (crate::leanh::lean_unbox(v___x_1064_) as u8);
        if v___x_1065_ == 0 {
            let mut v___x_1066_: u8 = 0;
            v___x_1066_ = 2;
            return v___x_1066_;
        } else {
            let mut v___x_1067_: u8 = 0;
            v___x_1067_ = 1;
            return v___x_1067_;
        }
    } else {
        let mut v___x_1068_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_1063_);
        crate::leanh::lean_dec(v_y_1061_);
        crate::leanh::lean_dec(v_x_1060_);
        v___x_1068_ = 0;
        return v___x_1068_;
    }
}
pub unsafe fn l_compareOfLessAndBEq___redArg___boxed(
    mut v_x_1069_: *mut crate::leanh::LeanObject,
    mut v_y_1070_: *mut crate::leanh::LeanObject,
    mut v_inst_1071_: *mut crate::leanh::LeanObject,
    mut v_inst_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_42__boxed_1073_: u8 = 0;
    let mut v_res_1074_: u8 = 0;
    let mut v_r_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_42__boxed_1073_ = (crate::leanh::lean_unbox(v_inst_1071_) as u8);
    v_res_1074_ =
        l_compareOfLessAndBEq___redArg(v_x_1069_, v_y_1070_, v_inst_42__boxed_1073_, v_inst_1072_);
    v_r_1075_ = crate::leanh::lean_box((v_res_1074_) as usize);
    return v_r_1075_;
}
pub unsafe fn l_compareOfLessAndBEq(
    mut v_00_u03b1_1076_: *mut crate::leanh::LeanObject,
    mut v_x_1077_: *mut crate::leanh::LeanObject,
    mut v_y_1078_: *mut crate::leanh::LeanObject,
    mut v_inst_1079_: *mut crate::leanh::LeanObject,
    mut v_inst_1080_: u8,
    mut v_inst_1081_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_inst_1080_ == 0 {
        let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1083_: u8 = 0;
        v___x_1082_ = crate::leanh::lean_apply_2(v_inst_1081_, v_x_1077_, v_y_1078_);
        v___x_1083_ = (crate::leanh::lean_unbox(v___x_1082_) as u8);
        if v___x_1083_ == 0 {
            let mut v___x_1084_: u8 = 0;
            v___x_1084_ = 2;
            return v___x_1084_;
        } else {
            let mut v___x_1085_: u8 = 0;
            v___x_1085_ = 1;
            return v___x_1085_;
        }
    } else {
        let mut v___x_1086_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_1081_);
        crate::leanh::lean_dec(v_y_1078_);
        crate::leanh::lean_dec(v_x_1077_);
        v___x_1086_ = 0;
        return v___x_1086_;
    }
}
pub unsafe fn l_compareOfLessAndBEq___boxed(
    mut v_00_u03b1_1087_: *mut crate::leanh::LeanObject,
    mut v_x_1088_: *mut crate::leanh::LeanObject,
    mut v_y_1089_: *mut crate::leanh::LeanObject,
    mut v_inst_1090_: *mut crate::leanh::LeanObject,
    mut v_inst_1091_: *mut crate::leanh::LeanObject,
    mut v_inst_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_59__boxed_1093_: u8 = 0;
    let mut v_res_1094_: u8 = 0;
    let mut v_r_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_59__boxed_1093_ = (crate::leanh::lean_unbox(v_inst_1091_) as u8);
    v_res_1094_ = l_compareOfLessAndBEq(
        v_00_u03b1_1087_,
        v_x_1088_,
        v_y_1089_,
        v_inst_1090_,
        v_inst_59__boxed_1093_,
        v_inst_1092_,
    );
    v_r_1095_ = crate::leanh::lean_box((v_res_1094_) as usize);
    return v_r_1095_;
}
pub unsafe fn l_compareLex___redArg(
    mut v_cmp_u2081_1096_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2082_1097_: *mut crate::leanh::LeanObject,
    mut v_a_1098_: *mut crate::leanh::LeanObject,
    mut v_b_1099_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    crate::leanh::lean_inc(v_b_1099_);
    crate::leanh::lean_inc(v_a_1098_);
    v___x_1100_ = crate::leanh::lean_apply_2(v_cmp_u2081_1096_, v_a_1098_, v_b_1099_);
    v___x_1101_ = (crate::leanh::lean_unbox(v___x_1100_) as u8);
    if v___x_1101_ == 1 {
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: u8 = 0;
        v___x_1102_ = crate::leanh::lean_apply_2(v_cmp_u2082_1097_, v_a_1098_, v_b_1099_);
        v___x_1103_ = (crate::leanh::lean_unbox(v___x_1102_) as u8);
        return v___x_1103_;
    } else {
        let mut v___x_1104_: u8 = 0;
        crate::leanh::lean_dec(v_b_1099_);
        crate::leanh::lean_dec(v_a_1098_);
        crate::leanh::lean_dec_ref(v_cmp_u2082_1097_);
        v___x_1104_ = (crate::leanh::lean_unbox(v___x_1100_) as u8);
        return v___x_1104_;
    }
}
pub unsafe fn l_compareLex___redArg___boxed(
    mut v_cmp_u2081_1105_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2082_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_b_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: u8 = 0;
    let mut v_r_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_compareLex___redArg(v_cmp_u2081_1105_, v_cmp_u2082_1106_, v_a_1107_, v_b_1108_);
    v_r_1110_ = crate::leanh::lean_box((v_res_1109_) as usize);
    return v_r_1110_;
}
pub unsafe fn l_compareLex(
    mut v_00_u03b1_1111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1112_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2081_1113_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2082_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_b_1116_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: u8 = 0;
    crate::leanh::lean_inc(v_b_1116_);
    crate::leanh::lean_inc(v_a_1115_);
    v___x_1117_ = crate::leanh::lean_apply_2(v_cmp_u2081_1113_, v_a_1115_, v_b_1116_);
    v___x_1118_ = (crate::leanh::lean_unbox(v___x_1117_) as u8);
    if v___x_1118_ == 1 {
        let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1120_: u8 = 0;
        v___x_1119_ = crate::leanh::lean_apply_2(v_cmp_u2082_1114_, v_a_1115_, v_b_1116_);
        v___x_1120_ = (crate::leanh::lean_unbox(v___x_1119_) as u8);
        return v___x_1120_;
    } else {
        let mut v___x_1121_: u8 = 0;
        crate::leanh::lean_dec(v_b_1116_);
        crate::leanh::lean_dec(v_a_1115_);
        crate::leanh::lean_dec_ref(v_cmp_u2082_1114_);
        v___x_1121_ = (crate::leanh::lean_unbox(v___x_1117_) as u8);
        return v___x_1121_;
    }
}
pub unsafe fn l_compareLex___boxed(
    mut v_00_u03b1_1122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1123_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2081_1124_: *mut crate::leanh::LeanObject,
    mut v_cmp_u2082_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_b_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1128_: u8 = 0;
    let mut v_r_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ = l_compareLex(
        v_00_u03b1_1122_,
        v_00_u03b2_1123_,
        v_cmp_u2081_1124_,
        v_cmp_u2082_1125_,
        v_a_1126_,
        v_b_1127_,
    );
    v_r_1129_ = crate::leanh::lean_box((v_res_1128_) as usize);
    return v_r_1129_;
}
pub unsafe fn l_compareOn___redArg(
    mut v_ord_1130_: *mut crate::leanh::LeanObject,
    mut v_f_1131_: *mut crate::leanh::LeanObject,
    mut v_x_1132_: *mut crate::leanh::LeanObject,
    mut v_y_1133_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    crate::leanh::lean_inc(v_f_1131_);
    v___x_1134_ = crate::leanh::lean_apply_1(v_f_1131_, v_x_1132_);
    v___x_1135_ = crate::leanh::lean_apply_1(v_f_1131_, v_y_1133_);
    v___x_1136_ = crate::leanh::lean_apply_2(v_ord_1130_, v___x_1134_, v___x_1135_);
    v___x_1137_ = (crate::leanh::lean_unbox(v___x_1136_) as u8);
    return v___x_1137_;
}
pub unsafe fn l_compareOn___redArg___boxed(
    mut v_ord_1138_: *mut crate::leanh::LeanObject,
    mut v_f_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v_y_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_compareOn___redArg(v_ord_1138_, v_f_1139_, v_x_1140_, v_y_1141_);
    v_r_1143_ = crate::leanh::lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn l_compareOn(
    mut v_00_u03b2_1144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1145_: *mut crate::leanh::LeanObject,
    mut v_ord_1146_: *mut crate::leanh::LeanObject,
    mut v_f_1147_: *mut crate::leanh::LeanObject,
    mut v_x_1148_: *mut crate::leanh::LeanObject,
    mut v_y_1149_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    crate::leanh::lean_inc(v_f_1147_);
    v___x_1150_ = crate::leanh::lean_apply_1(v_f_1147_, v_x_1148_);
    v___x_1151_ = crate::leanh::lean_apply_1(v_f_1147_, v_y_1149_);
    v___x_1152_ = crate::leanh::lean_apply_2(v_ord_1146_, v___x_1150_, v___x_1151_);
    v___x_1153_ = (crate::leanh::lean_unbox(v___x_1152_) as u8);
    return v___x_1153_;
}
pub unsafe fn l_compareOn___boxed(
    mut v_00_u03b2_1154_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1155_: *mut crate::leanh::LeanObject,
    mut v_ord_1156_: *mut crate::leanh::LeanObject,
    mut v_f_1157_: *mut crate::leanh::LeanObject,
    mut v_x_1158_: *mut crate::leanh::LeanObject,
    mut v_y_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1160_: u8 = 0;
    let mut v_r_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_compareOn(
        v_00_u03b2_1154_,
        v_00_u03b1_1155_,
        v_ord_1156_,
        v_f_1157_,
        v_x_1158_,
        v_y_1159_,
    );
    v_r_1161_ = crate::leanh::lean_box((v_res_1160_) as usize);
    return v_r_1161_;
}
pub unsafe fn l_instOrdNat___lam__0(
    mut v_x_1162_: *mut crate::leanh::LeanObject,
    mut v_y_1163_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1164_: u8 = 0;
    v___x_1164_ = lean_nat_dec_lt(v_x_1162_, v_y_1163_);
    if v___x_1164_ == 0 {
        let mut v___x_1165_: u8 = 0;
        v___x_1165_ = lean_nat_dec_eq(v_x_1162_, v_y_1163_);
        if v___x_1165_ == 0 {
            let mut v___x_1166_: u8 = 0;
            v___x_1166_ = 2;
            return v___x_1166_;
        } else {
            let mut v___x_1167_: u8 = 0;
            v___x_1167_ = 1;
            return v___x_1167_;
        }
    } else {
        let mut v___x_1168_: u8 = 0;
        v___x_1168_ = 0;
        return v___x_1168_;
    }
}
pub unsafe fn l_instOrdNat___lam__0___boxed(
    mut v_x_1169_: *mut crate::leanh::LeanObject,
    mut v_y_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: u8 = 0;
    let mut v_r_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_instOrdNat___lam__0(v_x_1169_, v_y_1170_);
    crate::leanh::lean_dec(v_y_1170_);
    crate::leanh::lean_dec(v_x_1169_);
    v_r_1172_ = crate::leanh::lean_box((v_res_1171_) as usize);
    return v_r_1172_;
}
pub unsafe fn l_instOrdInt___lam__0(
    mut v_x_1175_: *mut crate::leanh::LeanObject,
    mut v_y_1176_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1177_: u8 = 0;
    v___x_1177_ = lean_int_dec_lt(v_x_1175_, v_y_1176_);
    if v___x_1177_ == 0 {
        let mut v___x_1178_: u8 = 0;
        v___x_1178_ = lean_int_dec_eq(v_x_1175_, v_y_1176_);
        if v___x_1178_ == 0 {
            let mut v___x_1179_: u8 = 0;
            v___x_1179_ = 2;
            return v___x_1179_;
        } else {
            let mut v___x_1180_: u8 = 0;
            v___x_1180_ = 1;
            return v___x_1180_;
        }
    } else {
        let mut v___x_1181_: u8 = 0;
        v___x_1181_ = 0;
        return v___x_1181_;
    }
}
pub unsafe fn l_instOrdInt___lam__0___boxed(
    mut v_x_1182_: *mut crate::leanh::LeanObject,
    mut v_y_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1184_: u8 = 0;
    let mut v_r_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1184_ = l_instOrdInt___lam__0(v_x_1182_, v_y_1183_);
    crate::leanh::lean_dec(v_y_1183_);
    crate::leanh::lean_dec(v_x_1182_);
    v_r_1185_ = crate::leanh::lean_box((v_res_1184_) as usize);
    return v_r_1185_;
}
pub unsafe fn l_instOrdBool___lam__0(mut v_x_1188_: u8, mut v_x_1189_: u8) -> u8 {
    if v_x_1188_ == 0 {
        if v_x_1189_ == 1 {
            let mut v___x_1190_: u8 = 0;
            v___x_1190_ = 0;
            return v___x_1190_;
        } else {
            let mut v___x_1191_: u8 = 0;
            v___x_1191_ = 1;
            return v___x_1191_;
        }
    } else {
        if v_x_1189_ == 0 {
            let mut v___x_1192_: u8 = 0;
            v___x_1192_ = 2;
            return v___x_1192_;
        } else {
            let mut v___x_1193_: u8 = 0;
            v___x_1193_ = 1;
            return v___x_1193_;
        }
    }
}
pub unsafe fn l_instOrdBool___lam__0___boxed(
    mut v_x_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_49__boxed_1196_: u8 = 0;
    let mut v_x_50__boxed_1197_: u8 = 0;
    let mut v_res_1198_: u8 = 0;
    let mut v_r_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_49__boxed_1196_ = (crate::leanh::lean_unbox(v_x_1194_) as u8);
    v_x_50__boxed_1197_ = (crate::leanh::lean_unbox(v_x_1195_) as u8);
    v_res_1198_ = l_instOrdBool___lam__0(v_x_49__boxed_1196_, v_x_50__boxed_1197_);
    v_r_1199_ = crate::leanh::lean_box((v_res_1198_) as usize);
    return v_r_1199_;
}
pub unsafe fn l_instOrdFin(
    mut v_n_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1203_ = l_instOrdNat___closed__0;
    return v___f_1203_;
}
pub unsafe fn l_instOrdFin___boxed(
    mut v_n_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_instOrdFin(v_n_1204_);
    crate::leanh::lean_dec(v_n_1204_);
    return v_res_1205_;
}
pub unsafe fn l_instOrdChar___lam__0(mut v_x_1206_: u32, mut v_y_1207_: u32) -> u8 {
    let mut v___x_1208_: u8 = 0;
    v___x_1208_ = lean_uint32_dec_lt(v_x_1206_, v_y_1207_);
    if v___x_1208_ == 0 {
        let mut v___x_1209_: u8 = 0;
        v___x_1209_ = lean_uint32_dec_eq(v_x_1206_, v_y_1207_);
        if v___x_1209_ == 0 {
            let mut v___x_1210_: u8 = 0;
            v___x_1210_ = 2;
            return v___x_1210_;
        } else {
            let mut v___x_1211_: u8 = 0;
            v___x_1211_ = 1;
            return v___x_1211_;
        }
    } else {
        let mut v___x_1212_: u8 = 0;
        v___x_1212_ = 0;
        return v___x_1212_;
    }
}
pub unsafe fn l_instOrdChar___lam__0___boxed(
    mut v_x_1213_: *mut crate::leanh::LeanObject,
    mut v_y_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1215_: u32 = 0;
    let mut v_y_boxed_1216_: u32 = 0;
    let mut v_res_1217_: u8 = 0;
    let mut v_r_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1215_ = crate::leanh::lean_unbox_uint32(v_x_1213_);
    crate::leanh::lean_dec(v_x_1213_);
    v_y_boxed_1216_ = crate::leanh::lean_unbox_uint32(v_y_1214_);
    crate::leanh::lean_dec(v_y_1214_);
    v_res_1217_ = l_instOrdChar___lam__0(v_x_boxed_1215_, v_y_boxed_1216_);
    v_r_1218_ = crate::leanh::lean_box((v_res_1217_) as usize);
    return v_r_1218_;
}
pub unsafe fn l_instOrdBitVec(
    mut v_n_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1222_ = l_instOrdNat___closed__0;
    return v___f_1222_;
}
pub unsafe fn l_instOrdBitVec___boxed(
    mut v_n_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_instOrdBitVec(v_n_1223_);
    crate::leanh::lean_dec(v_n_1223_);
    return v_res_1224_;
}
pub unsafe fn l_instOrdOption___redArg___lam__0(
    mut v_inst_1225_: *mut crate::leanh::LeanObject,
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_x_1227_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1226_) == 0 {
        crate::leanh::lean_dec_ref(v_inst_1225_);
        if crate::leanh::lean_obj_tag(v_x_1227_) == 0 {
            let mut v___x_1228_: u8 = 0;
            v___x_1228_ = 1;
            return v___x_1228_;
        } else {
            let mut v___x_1229_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1227_, 1);
            v___x_1229_ = 0;
            return v___x_1229_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1227_) == 0 {
            let mut v___x_1230_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1226_, 1);
            crate::leanh::lean_dec_ref(v_inst_1225_);
            v___x_1230_ = 2;
            return v___x_1230_;
        } else {
            let mut v_val_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1234_: u8 = 0;
            v_val_1231_ = crate::leanh::lean_ctor_get(v_x_1226_, 0);
            crate::leanh::lean_inc(v_val_1231_);
            crate::leanh::lean_dec_ref_known(v_x_1226_, 1);
            v_val_1232_ = crate::leanh::lean_ctor_get(v_x_1227_, 0);
            crate::leanh::lean_inc(v_val_1232_);
            crate::leanh::lean_dec_ref_known(v_x_1227_, 1);
            v___x_1233_ = crate::leanh::lean_apply_2(v_inst_1225_, v_val_1231_, v_val_1232_);
            v___x_1234_ = (crate::leanh::lean_unbox(v___x_1233_) as u8);
            return v___x_1234_;
        }
    }
}
pub unsafe fn l_instOrdOption___redArg___lam__0___boxed(
    mut v_inst_1235_: *mut crate::leanh::LeanObject,
    mut v_x_1236_: *mut crate::leanh::LeanObject,
    mut v_x_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: u8 = 0;
    let mut v_r_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_instOrdOption___redArg___lam__0(v_inst_1235_, v_x_1236_, v_x_1237_);
    v_r_1239_ = crate::leanh::lean_box((v_res_1238_) as usize);
    return v_r_1239_;
}
pub unsafe fn l_instOrdOption___redArg(
    mut v_inst_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1241_ = crate::leanh::lean_alloc_closure(
        l_instOrdOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1241_, 0, v_inst_1240_);
    return v___f_1241_;
}
pub unsafe fn l_instOrdOption(
    mut v_00_u03b1_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1244_ = crate::leanh::lean_alloc_closure(
        l_instOrdOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1244_, 0, v_inst_1243_);
    return v___f_1244_;
}
pub unsafe fn l_List_compareLex___redArg(
    mut v_cmp_1250_: *mut crate::leanh::LeanObject,
    mut v_x_1251_: *mut crate::leanh::LeanObject,
    mut v_x_1252_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: u8 = 0;
    let mut v_head_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1251_) == 0 {
                    crate::leanh::lean_dec_ref(v_cmp_1250_);
                    if crate::leanh::lean_obj_tag(v_x_1252_) == 0 {
                        v___x_1253_ = 1;
                        return v___x_1253_;
                    } else {
                        crate::leanh::lean_dec(v_x_1252_);
                        v___x_1254_ = 0;
                        return v___x_1254_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1252_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_1251_, 2);
                        crate::leanh::lean_dec_ref(v_cmp_1250_);
                        v___x_1255_ = 2;
                        return v___x_1255_;
                    } else {
                        v_head_1256_ = crate::leanh::lean_ctor_get(v_x_1251_, 0);
                        crate::leanh::lean_inc(v_head_1256_);
                        v_tail_1257_ = crate::leanh::lean_ctor_get(v_x_1251_, 1);
                        crate::leanh::lean_inc(v_tail_1257_);
                        crate::leanh::lean_dec_ref_known(v_x_1251_, 2);
                        v_head_1258_ = crate::leanh::lean_ctor_get(v_x_1252_, 0);
                        crate::leanh::lean_inc(v_head_1258_);
                        v_tail_1259_ = crate::leanh::lean_ctor_get(v_x_1252_, 1);
                        crate::leanh::lean_inc(v_tail_1259_);
                        crate::leanh::lean_dec_ref_known(v_x_1252_, 2);
                        crate::leanh::lean_inc_ref(v_cmp_1250_);
                        v___x_1260_ =
                            crate::leanh::lean_apply_2(v_cmp_1250_, v_head_1256_, v_head_1258_);
                        v___x_1261_ = (crate::leanh::lean_unbox(v___x_1260_) as u8);
                        if v___x_1261_ == 1 {
                            v_x_1251_ = v_tail_1257_;
                            v_x_1252_ = v_tail_1259_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_tail_1259_);
                            crate::leanh::lean_dec(v_tail_1257_);
                            crate::leanh::lean_dec_ref(v_cmp_1250_);
                            v___x_1263_ = (crate::leanh::lean_unbox(v___x_1260_) as u8);
                            return v___x_1263_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_compareLex___redArg___boxed(
    mut v_cmp_1264_: *mut crate::leanh::LeanObject,
    mut v_x_1265_: *mut crate::leanh::LeanObject,
    mut v_x_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: u8 = 0;
    let mut v_r_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_List_compareLex___redArg(v_cmp_1264_, v_x_1265_, v_x_1266_);
    v_r_1268_ = crate::leanh::lean_box((v_res_1267_) as usize);
    return v_r_1268_;
}
pub unsafe fn l_List_compareLex(
    mut v_00_u03b1_1269_: *mut crate::leanh::LeanObject,
    mut v_cmp_1270_: *mut crate::leanh::LeanObject,
    mut v_x_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1273_: u8 = 0;
    v___x_1273_ = l_List_compareLex___redArg(v_cmp_1270_, v_x_1271_, v_x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_List_compareLex___boxed(
    mut v_00_u03b1_1274_: *mut crate::leanh::LeanObject,
    mut v_cmp_1275_: *mut crate::leanh::LeanObject,
    mut v_x_1276_: *mut crate::leanh::LeanObject,
    mut v_x_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1278_: u8 = 0;
    let mut v_r_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_List_compareLex(v_00_u03b1_1274_, v_cmp_1275_, v_x_1276_, v_x_1277_);
    v_r_1279_ = crate::leanh::lean_box((v_res_1278_) as usize);
    return v_r_1279_;
}
pub unsafe fn l_List_instOrd___redArg(
    mut v_inst_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ =
        crate::leanh::lean_alloc_closure(l_List_compareLex___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1281_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1281_, 1, v_inst_1280_);
    return v___x_1281_;
}
pub unsafe fn l_List_instOrd(
    mut v_00_u03b1_1282_: *mut crate::leanh::LeanObject,
    mut v_inst_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ =
        crate::leanh::lean_alloc_closure(l_List_compareLex___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1284_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1284_, 1, v_inst_1283_);
    return v___x_1284_;
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter___redArg(
    mut v_x_1285_: *mut crate::leanh::LeanObject,
    mut v_x_1286_: *mut crate::leanh::LeanObject,
    mut v_h__1_1287_: *mut crate::leanh::LeanObject,
    mut v_h__2_1288_: *mut crate::leanh::LeanObject,
    mut v_h__3_1289_: *mut crate::leanh::LeanObject,
    mut v_h__4_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1285_) == 0 {
        crate::leanh::lean_dec(v_h__4_1290_);
        crate::leanh::lean_dec(v_h__3_1289_);
        if crate::leanh::lean_obj_tag(v_x_1286_) == 0 {
            let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1288_);
            v___x_1291_ = crate::leanh::lean_box(0);
            v___x_1292_ = crate::leanh::lean_apply_1(v_h__1_1287_, v___x_1291_);
            return v___x_1292_;
        } else {
            let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1287_);
            v___x_1293_ =
                crate::leanh::lean_apply_2(v_h__2_1288_, v_x_1286_, crate::leanh::lean_box(0));
            return v___x_1293_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1288_);
        crate::leanh::lean_dec(v_h__1_1287_);
        if crate::leanh::lean_obj_tag(v_x_1286_) == 0 {
            let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1290_);
            v___x_1294_ =
                crate::leanh::lean_apply_2(v_h__3_1289_, v_x_1285_, crate::leanh::lean_box(0));
            return v___x_1294_;
        } else {
            let mut v_head_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1289_);
            v_head_1295_ = crate::leanh::lean_ctor_get(v_x_1285_, 0);
            crate::leanh::lean_inc(v_head_1295_);
            v_tail_1296_ = crate::leanh::lean_ctor_get(v_x_1285_, 1);
            crate::leanh::lean_inc(v_tail_1296_);
            crate::leanh::lean_dec_ref_known(v_x_1285_, 2);
            v_head_1297_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
            crate::leanh::lean_inc(v_head_1297_);
            v_tail_1298_ = crate::leanh::lean_ctor_get(v_x_1286_, 1);
            crate::leanh::lean_inc(v_tail_1298_);
            crate::leanh::lean_dec_ref_known(v_x_1286_, 2);
            v___x_1299_ = crate::leanh::lean_apply_4(
                v_h__4_1290_,
                v_head_1295_,
                v_tail_1296_,
                v_head_1297_,
                v_tail_1298_,
            );
            return v___x_1299_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__List_compareLex_match__1_splitter(
    mut v_00_u03b1_1300_: *mut crate::leanh::LeanObject,
    mut v_motive_1301_: *mut crate::leanh::LeanObject,
    mut v_x_1302_: *mut crate::leanh::LeanObject,
    mut v_x_1303_: *mut crate::leanh::LeanObject,
    mut v_h__1_1304_: *mut crate::leanh::LeanObject,
    mut v_h__2_1305_: *mut crate::leanh::LeanObject,
    mut v_h__3_1306_: *mut crate::leanh::LeanObject,
    mut v_h__4_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1302_) == 0 {
        crate::leanh::lean_dec(v_h__4_1307_);
        crate::leanh::lean_dec(v_h__3_1306_);
        if crate::leanh::lean_obj_tag(v_x_1303_) == 0 {
            let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1305_);
            v___x_1308_ = crate::leanh::lean_box(0);
            v___x_1309_ = crate::leanh::lean_apply_1(v_h__1_1304_, v___x_1308_);
            return v___x_1309_;
        } else {
            let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1304_);
            v___x_1310_ =
                crate::leanh::lean_apply_2(v_h__2_1305_, v_x_1303_, crate::leanh::lean_box(0));
            return v___x_1310_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1305_);
        crate::leanh::lean_dec(v_h__1_1304_);
        if crate::leanh::lean_obj_tag(v_x_1303_) == 0 {
            let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1307_);
            v___x_1311_ =
                crate::leanh::lean_apply_2(v_h__3_1306_, v_x_1302_, crate::leanh::lean_box(0));
            return v___x_1311_;
        } else {
            let mut v_head_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1306_);
            v_head_1312_ = crate::leanh::lean_ctor_get(v_x_1302_, 0);
            crate::leanh::lean_inc(v_head_1312_);
            v_tail_1313_ = crate::leanh::lean_ctor_get(v_x_1302_, 1);
            crate::leanh::lean_inc(v_tail_1313_);
            crate::leanh::lean_dec_ref_known(v_x_1302_, 2);
            v_head_1314_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
            crate::leanh::lean_inc(v_head_1314_);
            v_tail_1315_ = crate::leanh::lean_ctor_get(v_x_1303_, 1);
            crate::leanh::lean_inc(v_tail_1315_);
            crate::leanh::lean_dec_ref_known(v_x_1303_, 2);
            v___x_1316_ = crate::leanh::lean_apply_4(
                v_h__4_1307_,
                v_head_1312_,
                v_tail_1313_,
                v_head_1314_,
                v_tail_1315_,
            );
            return v___x_1316_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(
    mut v_x_1317_: u8,
    mut v_h__1_1318_: *mut crate::leanh::LeanObject,
    mut v_h__2_1319_: *mut crate::leanh::LeanObject,
    mut v_h__3_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1317_ {
        0 => {
            let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1320_);
            crate::leanh::lean_dec(v_h__2_1319_);
            v___x_1321_ = crate::leanh::lean_box(0);
            v___x_1322_ = crate::leanh::lean_apply_1(v_h__1_1318_, v___x_1321_);
            return v___x_1322_;
        }
        1 => {
            let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1320_);
            crate::leanh::lean_dec(v_h__1_1318_);
            v___x_1323_ = crate::leanh::lean_box(0);
            v___x_1324_ = crate::leanh::lean_apply_1(v_h__2_1319_, v___x_1323_);
            return v___x_1324_;
        }
        _ => {
            let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1319_);
            crate::leanh::lean_dec(v_h__1_1318_);
            v___x_1325_ = crate::leanh::lean_box(0);
            v___x_1326_ = crate::leanh::lean_apply_1(v_h__3_1320_, v___x_1325_);
            return v___x_1326_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg___boxed(
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_h__1_1328_: *mut crate::leanh::LeanObject,
    mut v_h__2_1329_: *mut crate::leanh::LeanObject,
    mut v_h__3_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_1331_: u8 = 0;
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1331_ = (crate::leanh::lean_unbox(v_x_1327_) as u8);
    v_res_1332_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___redArg(
        v_x_36__boxed_1331_,
        v_h__1_1328_,
        v_h__2_1329_,
        v_h__3_1330_,
    );
    return v_res_1332_;
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(
    mut v_motive_1333_: *mut crate::leanh::LeanObject,
    mut v_x_1334_: u8,
    mut v_h__1_1335_: *mut crate::leanh::LeanObject,
    mut v_h__2_1336_: *mut crate::leanh::LeanObject,
    mut v_h__3_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1334_ {
        0 => {
            let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1337_);
            crate::leanh::lean_dec(v_h__2_1336_);
            v___x_1338_ = crate::leanh::lean_box(0);
            v___x_1339_ = crate::leanh::lean_apply_1(v_h__1_1335_, v___x_1338_);
            return v___x_1339_;
        }
        1 => {
            let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1337_);
            crate::leanh::lean_dec(v_h__1_1335_);
            v___x_1340_ = crate::leanh::lean_box(0);
            v___x_1341_ = crate::leanh::lean_apply_1(v_h__2_1336_, v___x_1340_);
            return v___x_1341_;
        }
        _ => {
            let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1336_);
            crate::leanh::lean_dec(v_h__1_1335_);
            v___x_1342_ = crate::leanh::lean_box(0);
            v___x_1343_ = crate::leanh::lean_apply_1(v_h__3_1337_, v___x_1342_);
            return v___x_1343_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter___boxed(
    mut v_motive_1344_: *mut crate::leanh::LeanObject,
    mut v_x_1345_: *mut crate::leanh::LeanObject,
    mut v_h__1_1346_: *mut crate::leanh::LeanObject,
    mut v_h__2_1347_: *mut crate::leanh::LeanObject,
    mut v_h__3_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_1349_: u8 = 0;
    let mut v_res_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1349_ = (crate::leanh::lean_unbox(v_x_1345_) as u8);
    v_res_1350_ = l___private_Init_Data_Ord_Basic_0__Ordering_swap_match__1_splitter(
        v_motive_1344_,
        v_x_51__boxed_1349_,
        v_h__1_1346_,
        v_h__2_1347_,
        v_h__3_1348_,
    );
    return v_res_1350_;
}
pub unsafe fn l_lexOrd___redArg___lam__0(
    mut v_x_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1352_ = crate::leanh::lean_ctor_get(v_x_1351_, 0);
    crate::leanh::lean_inc(v_fst_1352_);
    return v_fst_1352_;
}
pub unsafe fn l_lexOrd___redArg___lam__0___boxed(
    mut v_x_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_lexOrd___redArg___lam__0(v_x_1353_);
    crate::leanh::lean_dec_ref(v_x_1353_);
    return v_res_1354_;
}
pub unsafe fn l_lexOrd___redArg___lam__1(
    mut v_x_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_1356_ = crate::leanh::lean_ctor_get(v_x_1355_, 1);
    crate::leanh::lean_inc(v_snd_1356_);
    return v_snd_1356_;
}
pub unsafe fn l_lexOrd___redArg___lam__1___boxed(
    mut v_x_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_lexOrd___redArg___lam__1(v_x_1357_);
    crate::leanh::lean_dec_ref(v_x_1357_);
    return v_res_1358_;
}
pub unsafe fn l_lexOrd___redArg(
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1363_ = l_lexOrd___redArg___closed__0;
    v___f_1364_ = l_lexOrd___redArg___closed__1;
    v___x_1365_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1365_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1365_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1365_, 2, v_inst_1361_);
    crate::leanh::lean_closure_set(v___x_1365_, 3, v___f_1363_);
    v___x_1366_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1366_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1366_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1366_, 2, v_inst_1362_);
    crate::leanh::lean_closure_set(v___x_1366_, 3, v___f_1364_);
    v___x_1367_ =
        crate::leanh::lean_alloc_closure(l_compareLex___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1367_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1367_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1367_, 2, v___x_1365_);
    crate::leanh::lean_closure_set(v___x_1367_, 3, v___x_1366_);
    return v___x_1367_;
}
pub unsafe fn l_lexOrd(
    mut v_00_u03b1_1368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1369_: *mut crate::leanh::LeanObject,
    mut v_inst_1370_: *mut crate::leanh::LeanObject,
    mut v_inst_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_lexOrd___redArg(v_inst_1370_, v_inst_1371_);
    return v___x_1372_;
}
pub unsafe fn l_beqOfOrd___redArg___lam__0(
    mut v_inst_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_b_1375_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    v___x_1376_ = crate::leanh::lean_apply_2(v_inst_1373_, v_a_1374_, v_b_1375_);
    v___x_1377_ = (crate::leanh::lean_unbox(v___x_1376_) as u8);
    if v___x_1377_ == 1 {
        let mut v___x_1378_: u8 = 0;
        v___x_1378_ = 1;
        return v___x_1378_;
    } else {
        let mut v___x_1379_: u8 = 0;
        v___x_1379_ = 0;
        return v___x_1379_;
    }
}
pub unsafe fn l_beqOfOrd___redArg___lam__0___boxed(
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_b_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1383_: u8 = 0;
    let mut v_r_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ = l_beqOfOrd___redArg___lam__0(v_inst_1380_, v_a_1381_, v_b_1382_);
    v_r_1384_ = crate::leanh::lean_box((v_res_1383_) as usize);
    return v_r_1384_;
}
pub unsafe fn l_beqOfOrd___redArg(
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1386_ = crate::leanh::lean_alloc_closure(
        l_beqOfOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1386_, 0, v_inst_1385_);
    return v___f_1386_;
}
pub unsafe fn l_beqOfOrd(
    mut v_00_u03b1_1387_: *mut crate::leanh::LeanObject,
    mut v_inst_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1389_ = crate::leanh::lean_alloc_closure(
        l_beqOfOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1389_, 0, v_inst_1388_);
    return v___f_1389_;
}
pub unsafe fn l_ltOfOrd(
    mut v_00_u03b1_1390_: *mut crate::leanh::LeanObject,
    mut v_inst_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = crate::leanh::lean_box(0);
    return v___x_1392_;
}
pub unsafe fn l_ltOfOrd___boxed(
    mut v_00_u03b1_1393_: *mut crate::leanh::LeanObject,
    mut v_inst_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1395_ = l_ltOfOrd(v_00_u03b1_1393_, v_inst_1394_);
    crate::leanh::lean_dec_ref(v_inst_1394_);
    return v_res_1395_;
}
pub unsafe fn l_instDecidableRelLt___redArg(
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_b_1398_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    v___x_1399_ = crate::leanh::lean_apply_2(v_inst_1396_, v_a_1397_, v_b_1398_);
    v___x_1400_ = (crate::leanh::lean_unbox(v___x_1399_) as u8);
    if v___x_1400_ == 0 {
        let mut v___x_1401_: u8 = 0;
        v___x_1401_ = 1;
        return v___x_1401_;
    } else {
        let mut v___x_1402_: u8 = 0;
        v___x_1402_ = 0;
        return v___x_1402_;
    }
}
pub unsafe fn l_instDecidableRelLt___redArg___boxed(
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_b_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: u8 = 0;
    let mut v_r_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_instDecidableRelLt___redArg(v_inst_1403_, v_a_1404_, v_b_1405_);
    v_r_1407_ = crate::leanh::lean_box((v_res_1406_) as usize);
    return v_r_1407_;
}
pub unsafe fn l_instDecidableRelLt(
    mut v_00_u03b1_1408_: *mut crate::leanh::LeanObject,
    mut v_inst_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_b_1411_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    v___x_1412_ = crate::leanh::lean_apply_2(v_inst_1409_, v_a_1410_, v_b_1411_);
    v___x_1413_ = (crate::leanh::lean_unbox(v___x_1412_) as u8);
    if v___x_1413_ == 0 {
        let mut v___x_1414_: u8 = 0;
        v___x_1414_ = 1;
        return v___x_1414_;
    } else {
        let mut v___x_1415_: u8 = 0;
        v___x_1415_ = 0;
        return v___x_1415_;
    }
}
pub unsafe fn l_instDecidableRelLt___boxed(
    mut v_00_u03b1_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_b_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1420_: u8 = 0;
    let mut v_r_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1420_ = l_instDecidableRelLt(v_00_u03b1_1416_, v_inst_1417_, v_a_1418_, v_b_1419_);
    v_r_1421_ = crate::leanh::lean_box((v_res_1420_) as usize);
    return v_r_1421_;
}
pub unsafe fn l_leOfOrd(
    mut v_00_u03b1_1422_: *mut crate::leanh::LeanObject,
    mut v_inst_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = crate::leanh::lean_box(0);
    return v___x_1424_;
}
pub unsafe fn l_leOfOrd___boxed(
    mut v_00_u03b1_1425_: *mut crate::leanh::LeanObject,
    mut v_inst_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_leOfOrd(v_00_u03b1_1425_, v_inst_1426_);
    crate::leanh::lean_dec_ref(v_inst_1426_);
    return v_res_1427_;
}
pub unsafe fn l_instDecidableRelLe___redArg(
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_x_1429_: *mut crate::leanh::LeanObject,
    mut v_x_1430_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    v___x_1431_ = crate::leanh::lean_apply_2(v_inst_1428_, v_x_1429_, v_x_1430_);
    v___x_1432_ = (crate::leanh::lean_unbox(v___x_1431_) as u8);
    if v___x_1432_ == 2 {
        let mut v___x_1433_: u8 = 0;
        v___x_1433_ = 0;
        return v___x_1433_;
    } else {
        let mut v___x_1434_: u8 = 0;
        v___x_1434_ = 1;
        return v___x_1434_;
    }
}
pub unsafe fn l_instDecidableRelLe___redArg___boxed(
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1438_: u8 = 0;
    let mut v_r_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_instDecidableRelLe___redArg(v_inst_1435_, v_x_1436_, v_x_1437_);
    v_r_1439_ = crate::leanh::lean_box((v_res_1438_) as usize);
    return v_r_1439_;
}
pub unsafe fn l_instDecidableRelLe(
    mut v_00_u03b1_1440_: *mut crate::leanh::LeanObject,
    mut v_inst_1441_: *mut crate::leanh::LeanObject,
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v_x_1443_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    v___x_1444_ = crate::leanh::lean_apply_2(v_inst_1441_, v_x_1442_, v_x_1443_);
    v___x_1445_ = (crate::leanh::lean_unbox(v___x_1444_) as u8);
    if v___x_1445_ == 2 {
        let mut v___x_1446_: u8 = 0;
        v___x_1446_ = 0;
        return v___x_1446_;
    } else {
        let mut v___x_1447_: u8 = 0;
        v___x_1447_ = 1;
        return v___x_1447_;
    }
}
pub unsafe fn l_instDecidableRelLe___boxed(
    mut v_00_u03b1_1448_: *mut crate::leanh::LeanObject,
    mut v_inst_1449_: *mut crate::leanh::LeanObject,
    mut v_x_1450_: *mut crate::leanh::LeanObject,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: u8 = 0;
    let mut v_r_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_instDecidableRelLe(v_00_u03b1_1448_, v_inst_1449_, v_x_1450_, v_x_1451_);
    v_r_1453_ = crate::leanh::lean_box((v_res_1452_) as usize);
    return v_r_1453_;
}
pub unsafe fn l_Ord_toBEq___redArg(
    mut v_ord_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1455_ = crate::leanh::lean_alloc_closure(
        l_beqOfOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1455_, 0, v_ord_1454_);
    return v___f_1455_;
}
pub unsafe fn l_Ord_toBEq(
    mut v_00_u03b1_1456_: *mut crate::leanh::LeanObject,
    mut v_ord_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1458_ = crate::leanh::lean_alloc_closure(
        l_beqOfOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1458_, 0, v_ord_1457_);
    return v___f_1458_;
}
pub unsafe fn l_Ord_toLT(
    mut v_00_u03b1_1459_: *mut crate::leanh::LeanObject,
    mut v_ord_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = crate::leanh::lean_box(0);
    return v___x_1461_;
}
pub unsafe fn l_Ord_toLT___boxed(
    mut v_00_u03b1_1462_: *mut crate::leanh::LeanObject,
    mut v_ord_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Ord_toLT(v_00_u03b1_1462_, v_ord_1463_);
    crate::leanh::lean_dec_ref(v_ord_1463_);
    return v_res_1464_;
}
pub unsafe fn l_Ord_toLE(
    mut v_00_u03b1_1465_: *mut crate::leanh::LeanObject,
    mut v_ord_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = crate::leanh::lean_box(0);
    return v___x_1467_;
}
pub unsafe fn l_Ord_toLE___boxed(
    mut v_00_u03b1_1468_: *mut crate::leanh::LeanObject,
    mut v_ord_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Ord_toLE(v_00_u03b1_1468_, v_ord_1469_);
    crate::leanh::lean_dec_ref(v_ord_1469_);
    return v_res_1470_;
}
pub unsafe fn l_Ord_opposite___redArg___lam__0(
    mut v_ord_1471_: *mut crate::leanh::LeanObject,
    mut v_x_1472_: *mut crate::leanh::LeanObject,
    mut v_y_1473_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: u8 = 0;
    v___x_1474_ = crate::leanh::lean_apply_2(v_ord_1471_, v_y_1473_, v_x_1472_);
    v___x_1475_ = (crate::leanh::lean_unbox(v___x_1474_) as u8);
    return v___x_1475_;
}
pub unsafe fn l_Ord_opposite___redArg___lam__0___boxed(
    mut v_ord_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
    mut v_y_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1479_: u8 = 0;
    let mut v_r_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Ord_opposite___redArg___lam__0(v_ord_1476_, v_x_1477_, v_y_1478_);
    v_r_1480_ = crate::leanh::lean_box((v_res_1479_) as usize);
    return v_r_1480_;
}
pub unsafe fn l_Ord_opposite___redArg(
    mut v_ord_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1482_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1482_, 0, v_ord_1481_);
    return v___f_1482_;
}
pub unsafe fn l_Ord_opposite(
    mut v_00_u03b1_1483_: *mut crate::leanh::LeanObject,
    mut v_ord_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1485_ = crate::leanh::lean_alloc_closure(
        l_Ord_opposite___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1485_, 0, v_ord_1484_);
    return v___f_1485_;
}
pub unsafe fn l_Ord_on___redArg(
    mut v_x_1486_: *mut crate::leanh::LeanObject,
    mut v_f_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1488_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1488_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1488_, 2, v_x_1486_);
    crate::leanh::lean_closure_set(v___x_1488_, 3, v_f_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Ord_on(
    mut v_00_u03b2_1489_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
    mut v_f_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1493_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1493_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1493_, 2, v_x_1491_);
    crate::leanh::lean_closure_set(v___x_1493_, 3, v_f_1492_);
    return v___x_1493_;
}
pub unsafe fn l_Ord_lex___redArg(
    mut v_x_1494_: *mut crate::leanh::LeanObject,
    mut v_x_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = l_lexOrd___redArg(v_x_1494_, v_x_1495_);
    return v___x_1496_;
}
pub unsafe fn l_Ord_lex(
    mut v_00_u03b1_1497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = l_lexOrd___redArg(v_x_1499_, v_x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Ord_lex_x27___redArg(
    mut v_ord_u2081_1502_: *mut crate::leanh::LeanObject,
    mut v_ord_u2082_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ =
        crate::leanh::lean_alloc_closure(l_compareLex___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1504_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1504_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1504_, 2, v_ord_u2081_1502_);
    crate::leanh::lean_closure_set(v___x_1504_, 3, v_ord_u2082_1503_);
    return v___x_1504_;
}
pub unsafe fn l_Ord_lex_x27(
    mut v_00_u03b1_1505_: *mut crate::leanh::LeanObject,
    mut v_ord_u2081_1506_: *mut crate::leanh::LeanObject,
    mut v_ord_u2082_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ =
        crate::leanh::lean_alloc_closure(l_compareLex___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1508_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1508_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1508_, 2, v_ord_u2081_1506_);
    crate::leanh::lean_closure_set(v___x_1508_, 3, v_ord_u2082_1507_);
    return v___x_1508_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Ord_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_instInhabitedOrdering_default = _init_l_instInhabitedOrdering_default();
    l_instInhabitedOrdering = _init_l_instInhabitedOrdering();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Ord_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Ord_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Ord_Basic(builtin);
}
