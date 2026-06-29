// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Char
// Imports: Init.Data.Char.Ordinal Init.Data.Range.Polymorphic.Fin Init.Data.Range.Polymorphic.Map Init.Data.Char.Order Init.Data.Fin.Lemmas Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Char::Order::{
    initialize_Init_Data_Char_Order, runtime_initialize_Init_Data_Char_Order,
};
use crate::r#gen::Init::Data::Char::Ordinal::{
    initialize_Init_Data_Char_Ordinal, l_Char_ordinal, l_Char_ordinal___boxed,
    l_Char_succ_x3f___boxed, l_Char_succMany_x3f___boxed,
    runtime_initialize_Init_Data_Char_Ordinal,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Fin::{
    initialize_Init_Data_Range_Polymorphic_Fin, runtime_initialize_Init_Data_Range_Polymorphic_Fin,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Map::{
    initialize_Init_Data_Range_Polymorphic_Map, runtime_initialize_Init_Data_Range_Polymorphic_Map,
};
use crate::ffi::{lean_nat_add, lean_nat_sub};
pub static l_Char_instUpwardEnumerable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_succ_x3f___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instUpwardEnumerable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Char_instUpwardEnumerable___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_succMany_x3f___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instUpwardEnumerable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Char_instUpwardEnumerable___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Char_instUpwardEnumerable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Char_instUpwardEnumerable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Char_instHasSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Char_instHasSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Char_instHasSize__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Char_instHasSize__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Char_instHasSize__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Char_instHasSize__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Char_instLeast_x3f___closed__0___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_instLeast_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_instLeast_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_instLeast_x3f: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Char_ordinal___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_Char_0__Char_map:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Char_instHasSize___lam__0(
    mut v_lo_58_: u32,
    mut v_hi_59_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = l_Char_ordinal(v_lo_58_);
    v___x_61_ = l_Char_ordinal(v_hi_59_);
    v___x_62_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_63_ = lean_nat_add(v___x_61_, v___x_62_);
    crate::leanh::lean_dec(v___x_61_);
    v___x_64_ = lean_nat_sub(v___x_63_, v___x_60_);
    crate::leanh::lean_dec(v___x_60_);
    crate::leanh::lean_dec(v___x_63_);
    return v___x_64_;
}
pub unsafe fn l_Char_instHasSize___lam__0___boxed(
    mut v_lo_65_: *mut crate::leanh::LeanObject,
    mut v_hi_66_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_67_: u32 = 0;
    let mut v_hi_boxed_68_: u32 = 0;
    let mut v_res_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_67_ = crate::leanh::lean_unbox_uint32(v_lo_65_);
    crate::leanh::lean_dec(v_lo_65_);
    v_hi_boxed_68_ = crate::leanh::lean_unbox_uint32(v_hi_66_);
    crate::leanh::lean_dec(v_hi_66_);
    v_res_69_ = l_Char_instHasSize___lam__0(v_lo_boxed_67_, v_hi_boxed_68_);
    return v_res_69_;
}
pub unsafe fn l_Char_instHasSize__1___lam__0(
    mut v_lo_72_: u32,
    mut v_hi_73_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = l_Char_ordinal(v_lo_72_);
    v___x_75_ = l_Char_ordinal(v_hi_73_);
    v___x_76_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_77_ = lean_nat_add(v___x_75_, v___x_76_);
    crate::leanh::lean_dec(v___x_75_);
    v___x_78_ = lean_nat_sub(v___x_77_, v___x_74_);
    crate::leanh::lean_dec(v___x_74_);
    crate::leanh::lean_dec(v___x_77_);
    v___x_79_ = lean_nat_sub(v___x_78_, v___x_76_);
    crate::leanh::lean_dec(v___x_78_);
    return v___x_79_;
}
pub unsafe fn l_Char_instHasSize__1___lam__0___boxed(
    mut v_lo_80_: *mut crate::leanh::LeanObject,
    mut v_hi_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lo_boxed_82_: u32 = 0;
    let mut v_hi_boxed_83_: u32 = 0;
    let mut v_res_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_82_ = crate::leanh::lean_unbox_uint32(v_lo_80_);
    crate::leanh::lean_dec(v_lo_80_);
    v_hi_boxed_83_ = crate::leanh::lean_unbox_uint32(v_hi_81_);
    crate::leanh::lean_dec(v_hi_81_);
    v_res_84_ = l_Char_instHasSize__1___lam__0(v_lo_boxed_82_, v_hi_boxed_83_);
    return v_res_84_;
}
pub unsafe fn l_Char_instHasSize__2___lam__0(mut v_hi_87_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = crate::leanh::lean_unsigned_to_nat(1112064);
    v___x_89_ = l_Char_ordinal(v_hi_87_);
    v___x_90_ = lean_nat_sub(v___x_88_, v___x_89_);
    crate::leanh::lean_dec(v___x_89_);
    return v___x_90_;
}
pub unsafe fn l_Char_instHasSize__2___lam__0___boxed(
    mut v_hi_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hi_boxed_92_: u32 = 0;
    let mut v_res_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hi_boxed_92_ = crate::leanh::lean_unbox_uint32(v_hi_91_);
    crate::leanh::lean_dec(v_hi_91_);
    v_res_93_ = l_Char_instHasSize__2___lam__0(v_hi_boxed_92_);
    return v_res_93_;
}
pub unsafe fn _init_l_Char_instLeast_x3f___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_96_: u32 = 0;
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = 0;
    v___x_97_ = crate::leanh::lean_box_uint32(v___x_96_);
    return v___x_97_;
}
pub unsafe fn _init_l_Char_instLeast_x3f___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_98_ = l_Char_instLeast_x3f___closed__0___boxed__const__1;
    v___x_99_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_99_, 0, v___x_98_);
    return v___x_99_;
}
pub unsafe fn _init_l_Char_instLeast_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_instLeast_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Char_instLeast_x3f___closed__0_once),
        _init_l_Char_instLeast_x3f___closed__0,
    );
    return v___x_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Char_Ordinal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Map(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Char_instLeast_x3f___closed__0___boxed__const__1 =
        _init_l_Char_instLeast_x3f___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_Char_instLeast_x3f___closed__0___boxed__const__1);
    l_Char_instLeast_x3f = _init_l_Char_instLeast_x3f();
    crate::leanh::lean_mark_persistent(l_Char_instLeast_x3f);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Char_Ordinal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Map(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Char(builtin);
}
