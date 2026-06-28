// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Action
// Imports: Lean.Meta.Tactic.Grind.Action Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    initialize_Lean_Meta_Tactic_Grind_Action, l_Lean_Meta_Grind_Action_solverAction,
    runtime_initialize_Lean_Meta_Tactic_Grind_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::EqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr,
    l_Lean_Meta_Grind_Arith_CommRing_check___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [114, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__4_value)
                as *mut LeanObject,
            16893285825895468094 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_ring___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_ring___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_ring___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ring___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Arith_CommRing_check___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_ring___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ring___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Action_ring___lam__0(
    mut v___y_84_: *mut LeanObject,
    mut v___y_85_: *mut LeanObject,
    mut v___y_86_: *mut LeanObject,
    mut v___y_87_: *mut LeanObject,
    mut v___y_88_: *mut LeanObject,
    mut v___y_89_: *mut LeanObject,
    mut v___y_90_: *mut LeanObject,
    mut v___y_91_: *mut LeanObject,
    mut v___y_92_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_94_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_95_: u8 = 0;
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v_ref_94_ = lean_ctor_get(v___y_91_, 5);
    v___x_95_ = 0;
    v___x_96_ = l_Lean_SourceInfo_fromRef(v_ref_94_, v___x_95_);
    v___x_97_ = l_Lean_Meta_Grind_Action_ring___lam__0___closed__4;
    v___x_98_ = l_Lean_Meta_Grind_Action_ring___lam__0___closed__5;
    lean_inc(v___x_96_);
    v___x_99_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_99_, 0, v___x_96_);
    lean_ctor_set(v___x_99_, 1, v___x_97_);
    v___x_100_ = l_Lean_Syntax_node1(v___x_96_, v___x_98_, v___x_99_);
    v___x_101_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_101_, 0, v___x_100_);
    return v___x_101_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ring___lam__0___boxed(
    mut v___y_102_: *mut LeanObject,
    mut v___y_103_: *mut LeanObject,
    mut v___y_104_: *mut LeanObject,
    mut v___y_105_: *mut LeanObject,
    mut v___y_106_: *mut LeanObject,
    mut v___y_107_: *mut LeanObject,
    mut v___y_108_: *mut LeanObject,
    mut v___y_109_: *mut LeanObject,
    mut v___y_110_: *mut LeanObject,
    mut v___y_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_112_: *mut LeanObject = core::ptr::null_mut();
    v_res_112_ = l_Lean_Meta_Grind_Action_ring___lam__0(
        v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_,
        v___y_109_, v___y_110_,
    );
    lean_dec(v___y_110_);
    lean_dec_ref(v___y_109_);
    lean_dec(v___y_108_);
    lean_dec_ref(v___y_107_);
    lean_dec(v___y_106_);
    lean_dec_ref(v___y_105_);
    lean_dec(v___y_104_);
    lean_dec_ref(v___y_103_);
    lean_dec(v___y_102_);
    return v_res_112_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ring(
    mut v_a_115_: *mut LeanObject,
    mut v_kna_116_: *mut LeanObject,
    mut v_kp_117_: *mut LeanObject,
    mut v_a_118_: *mut LeanObject,
    mut v_a_119_: *mut LeanObject,
    mut v_a_120_: *mut LeanObject,
    mut v_a_121_: *mut LeanObject,
    mut v_a_122_: *mut LeanObject,
    mut v_a_123_: *mut LeanObject,
    mut v_a_124_: *mut LeanObject,
    mut v_a_125_: *mut LeanObject,
    mut v_a_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    v___f_128_ = l_Lean_Meta_Grind_Action_ring___closed__0;
    v___x_129_ = l_Lean_Meta_Grind_Action_ring___closed__1;
    v___x_130_ = l_Lean_Meta_Grind_Action_solverAction(
        v___x_129_, v___f_128_, v_a_115_, v_kna_116_, v_kp_117_, v_a_118_, v_a_119_, v_a_120_,
        v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_,
    );
    return v___x_130_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ring___boxed(
    mut v_a_131_: *mut LeanObject,
    mut v_kna_132_: *mut LeanObject,
    mut v_kp_133_: *mut LeanObject,
    mut v_a_134_: *mut LeanObject,
    mut v_a_135_: *mut LeanObject,
    mut v_a_136_: *mut LeanObject,
    mut v_a_137_: *mut LeanObject,
    mut v_a_138_: *mut LeanObject,
    mut v_a_139_: *mut LeanObject,
    mut v_a_140_: *mut LeanObject,
    mut v_a_141_: *mut LeanObject,
    mut v_a_142_: *mut LeanObject,
    mut v_a_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_144_: *mut LeanObject = core::ptr::null_mut();
    v_res_144_ = l_Lean_Meta_Grind_Action_ring(
        v_a_131_, v_kna_132_, v_kp_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_,
        v_a_139_, v_a_140_, v_a_141_, v_a_142_,
    );
    lean_dec(v_a_142_);
    lean_dec_ref(v_a_141_);
    lean_dec(v_a_140_);
    lean_dec_ref(v_a_139_);
    lean_dec(v_a_138_);
    lean_dec_ref(v_a_137_);
    lean_dec(v_a_136_);
    lean_dec_ref(v_a_135_);
    lean_dec(v_a_134_);
    return v_res_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
}
