// Lean compiler output
// Module: Init.Data.Hashable
// Imports: Init.Data.Array.Basic Init.Data.UInt.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, l_USize_toUInt64___boxed,
    runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    l_UInt8_toUInt64___boxed, l_UInt16_toUInt64___boxed, l_UInt32_toUInt64___boxed,
    l_UInt64_ofNat___boxed,
};
use crate::r#gen::Init::Prelude::l_List_foldl___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_uint64_of_nat, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_box_uint64,
    lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_instHashableNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableNat___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableNat: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableNat___closed__0_value) as *mut LeanObject;
pub static l_instHashableBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableBool___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableBool: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableBool___closed__0_value) as *mut LeanObject;
pub static l_instHashablePEmpty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashablePEmpty___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashablePEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashablePEmpty___closed__0_value) as *mut LeanObject;
pub static mut l_instHashablePEmpty: *mut LeanObject =
    core::ptr::addr_of!(l_instHashablePEmpty___closed__0_value) as *mut LeanObject;
pub static l_instHashablePUnit___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashablePUnit___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashablePUnit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashablePUnit___closed__0_value) as *mut LeanObject;
pub static mut l_instHashablePUnit: *mut LeanObject =
    core::ptr::addr_of!(l_instHashablePUnit___closed__0_value) as *mut LeanObject;
pub static l_instHashableList___redArg___lam__1___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [7 as *mut LeanObject],
    };
pub static mut l_instHashableList___redArg___lam__1___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableList___redArg___lam__1___boxed__const__1_value)
        as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__2_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__3_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__4_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__5_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableArray___redArg___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__6_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_instHashableArray___redArg___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__7_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_instHashableArray___redArg___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__8_value) as *mut LeanObject;
pub static l_instHashableArray___redArg___lam__1___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_instHashableArray___redArg___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableArray___redArg___lam__1___closed__9_value) as *mut LeanObject;
pub static l_instHashableUInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableUInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableUInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt8___closed__0_value) as *mut LeanObject;
pub static l_instHashableUInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableUInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableUInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt16___closed__0_value) as *mut LeanObject;
pub static l_instHashableUInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut LeanObject;
pub static l_instHashableUInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableUInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableUInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableUInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt64___closed__0_value) as *mut LeanObject;
pub static l_instHashableUSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUSize___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableUSize: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUSize___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableChar: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableUInt32___closed__0_value) as *mut LeanObject;
static mut l_instHashableInt___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instHashableInt___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableInt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableInt: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt___closed__0_value) as *mut LeanObject;
pub static l_instHashable___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashable___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashable___closed__0_value) as *mut LeanObject;
pub unsafe fn l_instHashableProd___redArg___lam__0(
    mut v_inst_212_: *mut LeanObject,
    mut v_inst_213_: *mut LeanObject,
    mut v_x_214_: *mut LeanObject,
) -> u64 {
    let mut v_fst_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u64 = 0;
    let mut v___x_220_: u64 = 0;
    let mut v___x_221_: u64 = 0;
    v_fst_215_ = lean_ctor_get(v_x_214_, 0);
    lean_inc(v_fst_215_);
    v_snd_216_ = lean_ctor_get(v_x_214_, 1);
    lean_inc(v_snd_216_);
    lean_dec_ref(v_x_214_);
    v___x_217_ = lean_apply_1(v_inst_212_, v_fst_215_);
    v___x_218_ = lean_apply_1(v_inst_213_, v_snd_216_);
    v___x_219_ = lean_unbox_uint64(v___x_217_);
    lean_dec_ref(v___x_217_);
    v___x_220_ = lean_unbox_uint64(v___x_218_);
    lean_dec_ref(v___x_218_);
    v___x_221_ = lean_uint64_mix_hash(v___x_219_, v___x_220_);
    return v___x_221_;
}
pub unsafe fn l_instHashableProd___redArg___lam__0___boxed(
    mut v_inst_222_: *mut LeanObject,
    mut v_inst_223_: *mut LeanObject,
    mut v_x_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_225_: u64 = 0;
    let mut v_r_226_: *mut LeanObject = core::ptr::null_mut();
    v_res_225_ = l_instHashableProd___redArg___lam__0(v_inst_222_, v_inst_223_, v_x_224_);
    v_r_226_ = lean_box_uint64(v_res_225_);
    return v_r_226_;
}
pub unsafe fn l_instHashableProd___redArg(
    mut v_inst_227_: *mut LeanObject,
    mut v_inst_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_229_: *mut LeanObject = core::ptr::null_mut();
    v___f_229_ = lean_alloc_closure(
        l_instHashableProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_229_, 0, v_inst_227_);
    lean_closure_set(v___f_229_, 1, v_inst_228_);
    return v___f_229_;
}
pub unsafe fn l_instHashableProd(
    mut v_00_u03b1_230_: *mut LeanObject,
    mut v_00_u03b2_231_: *mut LeanObject,
    mut v_inst_232_: *mut LeanObject,
    mut v_inst_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_234_: *mut LeanObject = core::ptr::null_mut();
    v___f_234_ = lean_alloc_closure(
        l_instHashableProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_234_, 0, v_inst_232_);
    lean_closure_set(v___f_234_, 1, v_inst_233_);
    return v___f_234_;
}
pub unsafe fn l_instHashableBool___lam__0(mut v_x_235_: u8) -> u64 {
    if v_x_235_ == 0 {
        let mut v___x_236_: u64 = 0;
        v___x_236_ = 13u64;
        return v___x_236_;
    } else {
        let mut v___x_237_: u64 = 0;
        v___x_237_ = 11u64;
        return v___x_237_;
    }
}
pub unsafe fn l_instHashableBool___lam__0___boxed(
    mut v_x_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_32__boxed_239_: u8 = 0;
    let mut v_res_240_: u64 = 0;
    let mut v_r_241_: *mut LeanObject = core::ptr::null_mut();
    v_x_32__boxed_239_ = (lean_unbox(v_x_238_) as u8);
    v_res_240_ = l_instHashableBool___lam__0(v_x_32__boxed_239_);
    v_r_241_ = lean_box_uint64(v_res_240_);
    return v_r_241_;
}
pub unsafe fn l_instHashablePEmpty___lam__0(mut v_x_244_: u8) -> u64 {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instHashablePEmpty___lam__0___boxed(
    mut v_x_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_246_: u8 = 0;
    let mut v_res_247_: u64 = 0;
    let mut v_r_248_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_246_ = (lean_unbox(v_x_245_) as u8);
    v_res_247_ = l_instHashablePEmpty___lam__0(v_x_boxed_246_);
    v_r_248_ = lean_box_uint64(v_res_247_);
    return v_r_248_;
}
pub unsafe fn l_instHashablePUnit___lam__0(mut v_x_251_: *mut LeanObject) -> u64 {
    let mut v___x_252_: u64 = 0;
    v___x_252_ = 11u64;
    return v___x_252_;
}
pub unsafe fn l_instHashablePUnit___lam__0___boxed(
    mut v_x_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: u64 = 0;
    let mut v_r_255_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_instHashablePUnit___lam__0(v_x_253_);
    v_r_255_ = lean_box_uint64(v_res_254_);
    return v_r_255_;
}
pub unsafe fn l_instHashableOption___redArg___lam__0(
    mut v_inst_258_: *mut LeanObject,
    mut v_x_259_: *mut LeanObject,
) -> u64 {
    if lean_obj_tag(v_x_259_) == 0 {
        let mut v___x_260_: u64 = 0;
        lean_dec_ref(v_inst_258_);
        v___x_260_ = 11u64;
        return v___x_260_;
    } else {
        let mut v_val_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: u64 = 0;
        let mut v___x_264_: u64 = 0;
        let mut v___x_265_: u64 = 0;
        v_val_261_ = lean_ctor_get(v_x_259_, 0);
        lean_inc(v_val_261_);
        lean_dec_ref_known(v_x_259_, 1);
        v___x_262_ = lean_apply_1(v_inst_258_, v_val_261_);
        v___x_263_ = 13u64;
        v___x_264_ = lean_unbox_uint64(v___x_262_);
        lean_dec_ref(v___x_262_);
        v___x_265_ = lean_uint64_mix_hash(v___x_264_, v___x_263_);
        return v___x_265_;
    }
}
pub unsafe fn l_instHashableOption___redArg___lam__0___boxed(
    mut v_inst_266_: *mut LeanObject,
    mut v_x_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: u64 = 0;
    let mut v_r_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_instHashableOption___redArg___lam__0(v_inst_266_, v_x_267_);
    v_r_269_ = lean_box_uint64(v_res_268_);
    return v_r_269_;
}
pub unsafe fn l_instHashableOption___redArg(mut v_inst_270_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_271_: *mut LeanObject = core::ptr::null_mut();
    v___f_271_ = lean_alloc_closure(
        l_instHashableOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_271_, 0, v_inst_270_);
    return v___f_271_;
}
pub unsafe fn l_instHashableOption(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_inst_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_274_: *mut LeanObject = core::ptr::null_mut();
    v___f_274_ = lean_alloc_closure(
        l_instHashableOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_274_, 0, v_inst_273_);
    return v___f_274_;
}
pub unsafe fn l_instHashableList___redArg___lam__0(
    mut v_inst_275_: *mut LeanObject,
    mut v_r_276_: u64,
    mut v_a_277_: *mut LeanObject,
) -> u64 {
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: u64 = 0;
    let mut v___x_280_: u64 = 0;
    v___x_278_ = lean_apply_1(v_inst_275_, v_a_277_);
    v___x_279_ = lean_unbox_uint64(v___x_278_);
    lean_dec_ref(v___x_278_);
    v___x_280_ = lean_uint64_mix_hash(v_r_276_, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_instHashableList___redArg___lam__0___boxed(
    mut v_inst_281_: *mut LeanObject,
    mut v_r_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_284_: u64 = 0;
    let mut v_res_285_: u64 = 0;
    let mut v_r_286_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_284_ = lean_unbox_uint64(v_r_282_);
    lean_dec_ref(v_r_282_);
    v_res_285_ = l_instHashableList___redArg___lam__0(v_inst_281_, v_r_boxed_284_, v_a_283_);
    v_r_286_ = lean_box_uint64(v_res_285_);
    return v_r_286_;
}
pub unsafe fn l_instHashableList___redArg___lam__1(
    mut v___f_289_: *mut LeanObject,
    mut v_as_290_: *mut LeanObject,
) -> u64 {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: u64 = 0;
    v___x_291_ = l_instHashableList___redArg___lam__1___boxed__const__1;
    v___x_292_ = l_List_foldl___redArg(v___f_289_, v___x_291_, v_as_290_);
    v___x_293_ = lean_unbox_uint64(v___x_292_);
    lean_dec(v___x_292_);
    return v___x_293_;
}
pub unsafe fn l_instHashableList___redArg___lam__1___boxed(
    mut v___f_294_: *mut LeanObject,
    mut v_as_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_296_: u64 = 0;
    let mut v_r_297_: *mut LeanObject = core::ptr::null_mut();
    v_res_296_ = l_instHashableList___redArg___lam__1(v___f_294_, v_as_295_);
    v_r_297_ = lean_box_uint64(v_res_296_);
    return v_r_297_;
}
pub unsafe fn l_instHashableList___redArg(mut v_inst_298_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_300_: *mut LeanObject = core::ptr::null_mut();
    v___f_299_ = lean_alloc_closure(
        l_instHashableList___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_299_, 0, v_inst_298_);
    v___f_300_ = lean_alloc_closure(
        l_instHashableList___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_300_, 0, v___f_299_);
    return v___f_300_;
}
pub unsafe fn l_instHashableList(
    mut v_00_u03b1_301_: *mut LeanObject,
    mut v_inst_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_303_ = l_instHashableList___redArg(v_inst_302_);
    return v___x_303_;
}
pub unsafe fn l_instHashableArray___redArg___lam__0(
    mut v_inst_304_: *mut LeanObject,
    mut v_x1_305_: u64,
    mut v_x2_306_: *mut LeanObject,
) -> u64 {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u64 = 0;
    let mut v___x_309_: u64 = 0;
    v___x_307_ = lean_apply_1(v_inst_304_, v_x2_306_);
    v___x_308_ = lean_unbox_uint64(v___x_307_);
    lean_dec_ref(v___x_307_);
    v___x_309_ = lean_uint64_mix_hash(v_x1_305_, v___x_308_);
    return v___x_309_;
}
pub unsafe fn l_instHashableArray___redArg___lam__0___boxed(
    mut v_inst_310_: *mut LeanObject,
    mut v_x1_311_: *mut LeanObject,
    mut v_x2_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x1_84__boxed_313_: u64 = 0;
    let mut v_res_314_: u64 = 0;
    let mut v_r_315_: *mut LeanObject = core::ptr::null_mut();
    v_x1_84__boxed_313_ = lean_unbox_uint64(v_x1_311_);
    lean_dec_ref(v_x1_311_);
    v_res_314_ = l_instHashableArray___redArg___lam__0(v_inst_310_, v_x1_84__boxed_313_, v_x2_312_);
    v_r_315_ = lean_box_uint64(v_res_314_);
    return v_r_315_;
}
pub unsafe fn l_instHashableArray___redArg___lam__1(
    mut v___f_335_: *mut LeanObject,
    mut v_as_336_: *mut LeanObject,
) -> u64 {
    let mut v___x_337_: u64 = 0;
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    v___x_337_ = 7u64;
    v___x_338_ = lean_unsigned_to_nat(0);
    v___x_339_ = lean_array_get_size(v_as_336_);
    v___x_340_ = l_instHashableArray___redArg___lam__1___closed__9;
    v___x_341_ = lean_nat_dec_lt(v___x_338_, v___x_339_);
    if v___x_341_ == 0 {
        lean_dec_ref(v_as_336_);
        lean_dec_ref(v___f_335_);
        return v___x_337_;
    } else {
        let mut v___x_342_: u8 = 0;
        v___x_342_ = lean_nat_dec_le(v___x_339_, v___x_339_);
        if v___x_342_ == 0 {
            if v___x_341_ == 0 {
                lean_dec_ref(v_as_336_);
                lean_dec_ref(v___f_335_);
                return v___x_337_;
            } else {
                let mut v___x_343_: usize = 0;
                let mut v___x_344_: usize = 0;
                let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_347_: u64 = 0;
                v___x_343_ = 0usize;
                v___x_344_ = lean_usize_of_nat(v___x_339_);
                v___x_345_ = l_instHashableList___redArg___lam__1___boxed__const__1;
                v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_340_,
                    v___f_335_,
                    v_as_336_,
                    v___x_343_,
                    v___x_344_,
                    v___x_345_,
                );
                v___x_347_ = lean_unbox_uint64(v___x_346_);
                lean_dec(v___x_346_);
                return v___x_347_;
            }
        } else {
            let mut v___x_348_: usize = 0;
            let mut v___x_349_: usize = 0;
            let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_352_: u64 = 0;
            v___x_348_ = 0usize;
            v___x_349_ = lean_usize_of_nat(v___x_339_);
            v___x_350_ = l_instHashableList___redArg___lam__1___boxed__const__1;
            v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_340_,
                v___f_335_,
                v_as_336_,
                v___x_348_,
                v___x_349_,
                v___x_350_,
            );
            v___x_352_ = lean_unbox_uint64(v___x_351_);
            lean_dec(v___x_351_);
            return v___x_352_;
        }
    }
}
pub unsafe fn l_instHashableArray___redArg___lam__1___boxed(
    mut v___f_353_: *mut LeanObject,
    mut v_as_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_355_: u64 = 0;
    let mut v_r_356_: *mut LeanObject = core::ptr::null_mut();
    v_res_355_ = l_instHashableArray___redArg___lam__1(v___f_353_, v_as_354_);
    v_r_356_ = lean_box_uint64(v_res_355_);
    return v_r_356_;
}
pub unsafe fn l_instHashableArray___redArg(mut v_inst_357_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_359_: *mut LeanObject = core::ptr::null_mut();
    v___f_358_ = lean_alloc_closure(
        l_instHashableArray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_358_, 0, v_inst_357_);
    v___f_359_ = lean_alloc_closure(
        l_instHashableArray___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_359_, 0, v___f_358_);
    return v___f_359_;
}
pub unsafe fn l_instHashableArray(
    mut v_00_u03b1_360_: *mut LeanObject,
    mut v_inst_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = l_instHashableArray___redArg(v_inst_361_);
    return v___x_362_;
}
pub unsafe fn l_instHashableUInt64___lam__0(mut v_n_369_: u64) -> u64 {
    return v_n_369_;
}
pub unsafe fn l_instHashableUInt64___lam__0___boxed(
    mut v_n_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_371_: u64 = 0;
    let mut v_res_372_: u64 = 0;
    let mut v_r_373_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_371_ = lean_unbox_uint64(v_n_370_);
    lean_dec_ref(v_n_370_);
    v_res_372_ = l_instHashableUInt64___lam__0(v_n_boxed_371_);
    v_r_373_ = lean_box_uint64(v_res_372_);
    return v_r_373_;
}
pub unsafe fn l_instHashableFin(mut v_n_378_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_379_: *mut LeanObject = core::ptr::null_mut();
    v___f_379_ = l_instHashableNat___closed__0;
    return v___f_379_;
}
pub unsafe fn l_instHashableFin___boxed(mut v_n_380_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_381_: *mut LeanObject = core::ptr::null_mut();
    v_res_381_ = l_instHashableFin(v_n_380_);
    lean_dec(v_n_380_);
    return v_res_381_;
}
pub unsafe fn _init_l_instHashableInt___lam__0___closed__0() -> *mut LeanObject {
    let mut v_natZero_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_384_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_383_ = lean_unsigned_to_nat(0);
    v_intZero_384_ = lean_nat_to_int(v_natZero_383_);
    return v_intZero_384_;
}
pub unsafe fn l_instHashableInt___lam__0(mut v_x_385_: *mut LeanObject) -> u64 {
    let mut v_intZero_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_387_: u8 = 0;
    v_intZero_386_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instHashableInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instHashableInt___lam__0___closed__0_once),
        _init_l_instHashableInt___lam__0___closed__0,
    );
    v_isNeg_387_ = lean_int_dec_lt(v_x_385_, v_intZero_386_);
    if v_isNeg_387_ == 0 {
        let mut v_a_388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_391_: u64 = 0;
        v_a_388_ = lean_nat_abs(v_x_385_);
        v___x_389_ = lean_unsigned_to_nat(2);
        v___x_390_ = lean_nat_mul(v___x_389_, v_a_388_);
        lean_dec(v_a_388_);
        v___x_391_ = lean_uint64_of_nat(v___x_390_);
        lean_dec(v___x_390_);
        return v___x_391_;
    } else {
        let mut v_abs_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_393_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_398_: u64 = 0;
        v_abs_392_ = lean_nat_abs(v_x_385_);
        v_one_393_ = lean_unsigned_to_nat(1);
        v_a_394_ = lean_nat_sub(v_abs_392_, v_one_393_);
        lean_dec(v_abs_392_);
        v___x_395_ = lean_unsigned_to_nat(2);
        v___x_396_ = lean_nat_mul(v___x_395_, v_a_394_);
        lean_dec(v_a_394_);
        v___x_397_ = lean_nat_add(v___x_396_, v_one_393_);
        lean_dec(v___x_396_);
        v___x_398_ = lean_uint64_of_nat(v___x_397_);
        lean_dec(v___x_397_);
        return v___x_398_;
    }
}
pub unsafe fn l_instHashableInt___lam__0___boxed(mut v_x_399_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_400_: u64 = 0;
    let mut v_r_401_: *mut LeanObject = core::ptr::null_mut();
    v_res_400_ = l_instHashableInt___lam__0(v_x_399_);
    lean_dec(v_x_399_);
    v_r_401_ = lean_box_uint64(v_res_400_);
    return v_r_401_;
}
pub unsafe fn l_instHashable___lam__0(mut v_x_404_: *mut LeanObject) -> u64 {
    let mut v___x_405_: u64 = 0;
    v___x_405_ = 0u64;
    return v___x_405_;
}
pub unsafe fn l_instHashable___lam__0___boxed(mut v_x_406_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_407_: u64 = 0;
    let mut v_r_408_: *mut LeanObject = core::ptr::null_mut();
    v_res_407_ = l_instHashable___lam__0(v_x_406_);
    v_r_408_ = lean_box_uint64(v_res_407_);
    return v_r_408_;
}
pub unsafe fn l_instHashable(mut v_P_410_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
    v___f_411_ = l_instHashable___closed__0;
    return v___f_411_;
}
pub unsafe fn l_hash64(mut v_u_412_: u64) -> u64 {
    let mut v___x_413_: u64 = 0;
    let mut v___x_414_: u64 = 0;
    v___x_413_ = 11u64;
    v___x_414_ = lean_uint64_mix_hash(v_u_412_, v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_hash64___boxed(mut v_u_415_: *mut LeanObject) -> *mut LeanObject {
    let mut v_u_boxed_416_: u64 = 0;
    let mut v_res_417_: u64 = 0;
    let mut v_r_418_: *mut LeanObject = core::ptr::null_mut();
    v_u_boxed_416_ = lean_unbox_uint64(v_u_415_);
    lean_dec_ref(v_u_415_);
    v_res_417_ = l_hash64(v_u_boxed_416_);
    v_r_418_ = lean_box_uint64(v_res_417_);
    return v_r_418_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Hashable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Hashable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Hashable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Hashable(builtin);
}
