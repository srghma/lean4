// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Char
// Imports: Init.Data.Char.Ordinal Init.Data.Range.Polymorphic.Fin Init.Data.Range.Polymorphic.Map Init.Data.Char.Order Init.Data.Fin.Lemmas Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_add, lean_nat_sub};
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
pub static l_Char_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_succ_x3f___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_succMany_x3f___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Char_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Char_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Char_instHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Char_instHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_Char_instHasSize__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__1___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Char_instHasSize__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Char_instHasSize__2___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_instHasSize__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Char_instHasSize__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__2___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Char_instHasSize__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_instHasSize__2___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Char_instLeast_x3f___closed__0___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_instLeast_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_instLeast_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_instLeast_x3f: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value:
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
    m_fun: l_Char_ordinal___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_Char_0__Char_map:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Char_instHasSize___lam__0(
    mut v_lo_58_: u32,
    mut v_hi_59_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = l_Char_ordinal(v_lo_58_);
    v___x_61_ = l_Char_ordinal(v_hi_59_);
    v___x_62_ = leanh::lean_unsigned_to_nat(1);
    v___x_63_ = lean_nat_add(v___x_61_, v___x_62_);
    leanh::lean_dec(v___x_61_);
    v___x_64_ = lean_nat_sub(v___x_63_, v___x_60_);
    leanh::lean_dec(v___x_60_);
    leanh::lean_dec(v___x_63_);
    return v___x_64_;
}
pub unsafe fn l_Char_instHasSize___lam__0___boxed(
    mut v_lo_65_: *mut leanh::LeanObject,
    mut v_hi_66_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_67_: u32 = 0;
    let mut v_hi_boxed_68_: u32 = 0;
    let mut v_res_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_67_ = leanh::lean_unbox_uint32(v_lo_65_);
    leanh::lean_dec(v_lo_65_);
    v_hi_boxed_68_ = leanh::lean_unbox_uint32(v_hi_66_);
    leanh::lean_dec(v_hi_66_);
    v_res_69_ = l_Char_instHasSize___lam__0(v_lo_boxed_67_, v_hi_boxed_68_);
    return v_res_69_;
}
pub unsafe fn l_Char_instHasSize__1___lam__0(
    mut v_lo_72_: u32,
    mut v_hi_73_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = l_Char_ordinal(v_lo_72_);
    v___x_75_ = l_Char_ordinal(v_hi_73_);
    v___x_76_ = leanh::lean_unsigned_to_nat(1);
    v___x_77_ = lean_nat_add(v___x_75_, v___x_76_);
    leanh::lean_dec(v___x_75_);
    v___x_78_ = lean_nat_sub(v___x_77_, v___x_74_);
    leanh::lean_dec(v___x_74_);
    leanh::lean_dec(v___x_77_);
    v___x_79_ = lean_nat_sub(v___x_78_, v___x_76_);
    leanh::lean_dec(v___x_78_);
    return v___x_79_;
}
pub unsafe fn l_Char_instHasSize__1___lam__0___boxed(
    mut v_lo_80_: *mut leanh::LeanObject,
    mut v_hi_81_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_82_: u32 = 0;
    let mut v_hi_boxed_83_: u32 = 0;
    let mut v_res_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_82_ = leanh::lean_unbox_uint32(v_lo_80_);
    leanh::lean_dec(v_lo_80_);
    v_hi_boxed_83_ = leanh::lean_unbox_uint32(v_hi_81_);
    leanh::lean_dec(v_hi_81_);
    v_res_84_ = l_Char_instHasSize__1___lam__0(v_lo_boxed_82_, v_hi_boxed_83_);
    return v_res_84_;
}
pub unsafe fn l_Char_instHasSize__2___lam__0(mut v_hi_87_: u32) -> *mut leanh::LeanObject {
    let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = leanh::lean_unsigned_to_nat(1112064);
    v___x_89_ = l_Char_ordinal(v_hi_87_);
    v___x_90_ = lean_nat_sub(v___x_88_, v___x_89_);
    leanh::lean_dec(v___x_89_);
    return v___x_90_;
}
pub unsafe fn l_Char_instHasSize__2___lam__0___boxed(
    mut v_hi_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hi_boxed_92_: u32 = 0;
    let mut v_res_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hi_boxed_92_ = leanh::lean_unbox_uint32(v_hi_91_);
    leanh::lean_dec(v_hi_91_);
    v_res_93_ = l_Char_instHasSize__2___lam__0(v_hi_boxed_92_);
    return v_res_93_;
}
pub unsafe fn _init_l_Char_instLeast_x3f___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_96_: u32 = 0;
    let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = 0;
    v___x_97_ = leanh::lean_box_uint32(v___x_96_);
    return v___x_97_;
}
pub unsafe fn _init_l_Char_instLeast_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_98_ = l_Char_instLeast_x3f___closed__0___boxed__const__1;
    v___x_99_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_99_, 0, v___x_98_);
    return v___x_99_;
}
pub unsafe fn _init_l_Char_instLeast_x3f() -> *mut leanh::LeanObject {
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_instLeast_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Char_instLeast_x3f___closed__0_once),
        _init_l_Char_instLeast_x3f___closed__0,
    );
    return v___x_100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Char(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Char_Ordinal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Map(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Char_instLeast_x3f___closed__0___boxed__const__1 =
        _init_l_Char_instLeast_x3f___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l_Char_instLeast_x3f___closed__0___boxed__const__1);
    l_Char_instLeast_x3f = _init_l_Char_instLeast_x3f();
    leanh::lean_mark_persistent(l_Char_instLeast_x3f);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Char(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Char(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Char_Ordinal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Fin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Map(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Char(builtin);
}