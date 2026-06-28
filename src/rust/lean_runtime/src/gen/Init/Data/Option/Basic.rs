// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: Init.Control.Basic Init.Grind.Tactics
use crate::r#gen::Init::Control::Basic::{
    initialize_Init_Control_Basic, runtime_initialize_Init_Control_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::l_Option_map;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Option_mapM___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_mapM___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Option_mapM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_mapM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Option_instOrElse___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_instOrElse___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Option_instOrElse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_instOrElse___closed__0_value) as *mut LeanObject;
pub static l_Option_toArray___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Option_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_instFunctorOption___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instFunctorOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__0_value) as *mut LeanObject;
pub static l_instFunctorOption___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_map as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instFunctorOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__1_value) as *mut LeanObject;
pub static l_instFunctorOption___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instFunctorOption___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instFunctorOption___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_instFunctorOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut LeanObject;
pub static mut l_instFunctorOption: *mut LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut LeanObject;
pub static l_instMonadOption___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__0_value) as *mut LeanObject;
pub static l_instMonadOption___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__1_value) as *mut LeanObject;
pub static l_instMonadOption___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__2_value) as *mut LeanObject;
pub static l_instMonadOption___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadOption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__3_value) as *mut LeanObject;
pub static l_instMonadOption___closed__4_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadOption___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadOption___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadOption___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadOption___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_instMonadOption___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__4_value) as *mut LeanObject;
pub static l_instMonadOption___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_bind as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadOption___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__5_value) as *mut LeanObject;
pub static l_instMonadOption___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadOption___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadOption___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_instMonadOption___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut LeanObject;
pub static mut l_instMonadOption: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut LeanObject;
pub static l_instAlternativeOption___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instAlternativeOption___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAlternativeOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__0_value) as *mut LeanObject;
pub static l_instAlternativeOption___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instAlternativeOption___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAlternativeOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__1_value) as *mut LeanObject;
pub static l_instAlternativeOption___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadOption___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instAlternativeOption___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instAlternativeOption___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instAlternativeOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut LeanObject;
pub static mut l_instAlternativeOption: *mut LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadExceptOfUnitOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value) as *mut LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Option_tryCatch___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value) as *mut LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadExceptOfUnitOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value) as *mut LeanObject;
pub static mut l_instMonadExceptOfUnitOption: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Option_instDecidableEq___redArg(
    mut v_inst_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_b_732_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_a_731_) == 0 {
        lean_dec_ref(v_inst_730_);
        if lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_733_: u8 = 0;
            v___x_733_ = 1;
            return v___x_733_;
        } else {
            let mut v___x_734_: u8 = 0;
            lean_dec_ref_known(v_b_732_, 1);
            v___x_734_ = 0;
            return v___x_734_;
        }
    } else {
        if lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_735_: u8 = 0;
            lean_dec_ref_known(v_a_731_, 1);
            lean_dec_ref(v_inst_730_);
            v___x_735_ = 0;
            return v___x_735_;
        } else {
            let mut v_val_736_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_737_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_739_: u8 = 0;
            v_val_736_ = lean_ctor_get(v_a_731_, 0);
            lean_inc(v_val_736_);
            lean_dec_ref_known(v_a_731_, 1);
            v_val_737_ = lean_ctor_get(v_b_732_, 0);
            lean_inc(v_val_737_);
            lean_dec_ref_known(v_b_732_, 1);
            v___x_738_ = lean_apply_2(v_inst_730_, v_val_736_, v_val_737_);
            v___x_739_ = (lean_unbox(v___x_738_) as u8);
            return v___x_739_;
        }
    }
}
pub unsafe fn l_Option_instDecidableEq___redArg___boxed(
    mut v_inst_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_b_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_743_: u8 = 0;
    let mut v_r_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_743_ = l_Option_instDecidableEq___redArg(v_inst_740_, v_a_741_, v_b_742_);
    v_r_744_ = lean_box((v_res_743_) as usize);
    return v_r_744_;
}
pub unsafe fn l_Option_instDecidableEq(
    mut v_00_u03b1_745_: *mut LeanObject,
    mut v_inst_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_b_748_: *mut LeanObject,
) -> u8 {
    let mut v___x_749_: u8 = 0;
    v___x_749_ = l_Option_instDecidableEq___redArg(v_inst_746_, v_a_747_, v_b_748_);
    return v___x_749_;
}
pub unsafe fn l_Option_instDecidableEq___boxed(
    mut v_00_u03b1_750_: *mut LeanObject,
    mut v_inst_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
    mut v_b_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_754_: u8 = 0;
    let mut v_r_755_: *mut LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Option_instDecidableEq(v_00_u03b1_750_, v_inst_751_, v_a_752_, v_b_753_);
    v_r_755_ = lean_box((v_res_754_) as usize);
    return v_r_755_;
}
pub unsafe fn l_Option_decidableEqNone___redArg(mut v_o_756_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_o_756_) == 0 {
        let mut v___x_757_: u8 = 0;
        v___x_757_ = 1;
        return v___x_757_;
    } else {
        let mut v___x_758_: u8 = 0;
        v___x_758_ = 0;
        return v___x_758_;
    }
}
pub unsafe fn l_Option_decidableEqNone___redArg___boxed(
    mut v_o_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Option_decidableEqNone___redArg(v_o_759_);
    lean_dec(v_o_759_);
    v_r_761_ = lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_Option_decidableEqNone(
    mut v_00_u03b1_762_: *mut LeanObject,
    mut v_o_763_: *mut LeanObject,
) -> u8 {
    let mut v___x_764_: u8 = 0;
    v___x_764_ = l_Option_decidableEqNone___redArg(v_o_763_);
    return v___x_764_;
}
pub unsafe fn l_Option_decidableEqNone___boxed(
    mut v_00_u03b1_765_: *mut LeanObject,
    mut v_o_766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_767_: u8 = 0;
    let mut v_r_768_: *mut LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Option_decidableEqNone(v_00_u03b1_765_, v_o_766_);
    lean_dec(v_o_766_);
    v_r_768_ = lean_box((v_res_767_) as usize);
    return v_r_768_;
}
pub unsafe fn l_Option_decidableNoneEq___redArg(mut v_o_769_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_o_769_) == 0 {
        let mut v___x_770_: u8 = 0;
        v___x_770_ = 1;
        return v___x_770_;
    } else {
        let mut v___x_771_: u8 = 0;
        v___x_771_ = 0;
        return v___x_771_;
    }
}
pub unsafe fn l_Option_decidableNoneEq___redArg___boxed(
    mut v_o_772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_773_: u8 = 0;
    let mut v_r_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Option_decidableNoneEq___redArg(v_o_772_);
    lean_dec(v_o_772_);
    v_r_774_ = lean_box((v_res_773_) as usize);
    return v_r_774_;
}
pub unsafe fn l_Option_decidableNoneEq(
    mut v_00_u03b1_775_: *mut LeanObject,
    mut v_o_776_: *mut LeanObject,
) -> u8 {
    let mut v___x_777_: u8 = 0;
    v___x_777_ = l_Option_decidableNoneEq___redArg(v_o_776_);
    return v___x_777_;
}
pub unsafe fn l_Option_decidableNoneEq___boxed(
    mut v_00_u03b1_778_: *mut LeanObject,
    mut v_o_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Option_decidableNoneEq(v_00_u03b1_778_, v_o_779_);
    lean_dec(v_o_779_);
    v_r_781_ = lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Option_instBEq_beq___redArg(
    mut v_inst_782_: *mut LeanObject,
    mut v_x_783_: *mut LeanObject,
    mut v_x_784_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_783_) == 0 {
        lean_dec_ref(v_inst_782_);
        if lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_785_: u8 = 0;
            v___x_785_ = 1;
            return v___x_785_;
        } else {
            let mut v___x_786_: u8 = 0;
            lean_dec_ref_known(v_x_784_, 1);
            v___x_786_ = 0;
            return v___x_786_;
        }
    } else {
        if lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_787_: u8 = 0;
            lean_dec_ref_known(v_x_783_, 1);
            lean_dec_ref(v_inst_782_);
            v___x_787_ = 0;
            return v___x_787_;
        } else {
            let mut v_val_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v_val_788_ = lean_ctor_get(v_x_783_, 0);
            lean_inc(v_val_788_);
            lean_dec_ref_known(v_x_783_, 1);
            v_val_789_ = lean_ctor_get(v_x_784_, 0);
            lean_inc(v_val_789_);
            lean_dec_ref_known(v_x_784_, 1);
            v___x_790_ = lean_apply_2(v_inst_782_, v_val_788_, v_val_789_);
            v___x_791_ = (lean_unbox(v___x_790_) as u8);
            return v___x_791_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___redArg___boxed(
    mut v_inst_792_: *mut LeanObject,
    mut v_x_793_: *mut LeanObject,
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_795_: u8 = 0;
    let mut v_r_796_: *mut LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Option_instBEq_beq___redArg(v_inst_792_, v_x_793_, v_x_794_);
    v_r_796_ = lean_box((v_res_795_) as usize);
    return v_r_796_;
}
pub unsafe fn l_Option_instBEq_beq(
    mut v_00_u03b1_797_: *mut LeanObject,
    mut v_inst_798_: *mut LeanObject,
    mut v_x_799_: *mut LeanObject,
    mut v_x_800_: *mut LeanObject,
) -> u8 {
    let mut v___x_801_: u8 = 0;
    v___x_801_ = l_Option_instBEq_beq___redArg(v_inst_798_, v_x_799_, v_x_800_);
    return v___x_801_;
}
pub unsafe fn l_Option_instBEq_beq___boxed(
    mut v_00_u03b1_802_: *mut LeanObject,
    mut v_inst_803_: *mut LeanObject,
    mut v_x_804_: *mut LeanObject,
    mut v_x_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Option_instBEq_beq(v_00_u03b1_802_, v_inst_803_, v_x_804_, v_x_805_);
    v_r_807_ = lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Option_instBEq___redArg(mut v_inst_808_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    v___x_809_ = lean_alloc_closure(l_Option_instBEq_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_809_, 0, lean_box(0));
    lean_closure_set(v___x_809_, 1, v_inst_808_);
    return v___x_809_;
}
pub unsafe fn l_Option_instBEq(
    mut v_00_u03b1_810_: *mut LeanObject,
    mut v_inst_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = lean_alloc_closure(l_Option_instBEq_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_812_, 0, lean_box(0));
    lean_closure_set(v___x_812_, 1, v_inst_811_);
    return v___x_812_;
}
pub unsafe fn l_Option_getM___redArg(
    mut v_inst_813_: *mut LeanObject,
    mut v_x_814_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_814_) == 0 {
        let mut v_failure_815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
        v_failure_815_ = lean_ctor_get(v_inst_813_, 1);
        lean_inc(v_failure_815_);
        lean_dec_ref(v_inst_813_);
        v___x_816_ = lean_apply_1(v_failure_815_, lean_box(0));
        return v___x_816_;
    } else {
        let mut v_toApplicative_817_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_818_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_817_ = lean_ctor_get(v_inst_813_, 0);
        lean_inc_ref(v_toApplicative_817_);
        lean_dec_ref(v_inst_813_);
        v_toPure_818_ = lean_ctor_get(v_toApplicative_817_, 1);
        lean_inc(v_toPure_818_);
        lean_dec_ref(v_toApplicative_817_);
        v_val_819_ = lean_ctor_get(v_x_814_, 0);
        lean_inc(v_val_819_);
        lean_dec_ref_known(v_x_814_, 1);
        v___x_820_ = lean_apply_2(v_toPure_818_, lean_box(0), v_val_819_);
        return v___x_820_;
    }
}
pub unsafe fn l_Option_getM(
    mut v_m_821_: *mut LeanObject,
    mut v_00_u03b1_822_: *mut LeanObject,
    mut v_inst_823_: *mut LeanObject,
    mut v_x_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_825_ = l_Option_getM___redArg(v_inst_823_, v_x_824_);
    return v___x_825_;
}
pub unsafe fn l_Option_isSome___redArg(mut v_x_826_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_826_) == 0 {
        let mut v___x_827_: u8 = 0;
        v___x_827_ = 0;
        return v___x_827_;
    } else {
        let mut v___x_828_: u8 = 0;
        v___x_828_ = 1;
        return v___x_828_;
    }
}
pub unsafe fn l_Option_isSome___redArg___boxed(mut v_x_829_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_830_: u8 = 0;
    let mut v_r_831_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Option_isSome___redArg(v_x_829_);
    lean_dec(v_x_829_);
    v_r_831_ = lean_box((v_res_830_) as usize);
    return v_r_831_;
}
pub unsafe fn l_Option_isSome(
    mut v_00_u03b1_832_: *mut LeanObject,
    mut v_x_833_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_833_) == 0 {
        let mut v___x_834_: u8 = 0;
        v___x_834_ = 0;
        return v___x_834_;
    } else {
        let mut v___x_835_: u8 = 0;
        v___x_835_ = 1;
        return v___x_835_;
    }
}
pub unsafe fn l_Option_isSome___boxed(
    mut v_00_u03b1_836_: *mut LeanObject,
    mut v_x_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Option_isSome(v_00_u03b1_836_, v_x_837_);
    lean_dec(v_x_837_);
    v_r_839_ = lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_Option_isNone___redArg(mut v_x_840_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_840_) == 0 {
        let mut v___x_841_: u8 = 0;
        v___x_841_ = 1;
        return v___x_841_;
    } else {
        let mut v___x_842_: u8 = 0;
        v___x_842_ = 0;
        return v___x_842_;
    }
}
pub unsafe fn l_Option_isNone___redArg___boxed(mut v_x_843_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_844_: u8 = 0;
    let mut v_r_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Option_isNone___redArg(v_x_843_);
    lean_dec(v_x_843_);
    v_r_845_ = lean_box((v_res_844_) as usize);
    return v_r_845_;
}
pub unsafe fn l_Option_isNone(
    mut v_00_u03b1_846_: *mut LeanObject,
    mut v_x_847_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_847_) == 0 {
        let mut v___x_848_: u8 = 0;
        v___x_848_ = 1;
        return v___x_848_;
    } else {
        let mut v___x_849_: u8 = 0;
        v___x_849_ = 0;
        return v___x_849_;
    }
}
pub unsafe fn l_Option_isNone___boxed(
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_x_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_852_: u8 = 0;
    let mut v_r_853_: *mut LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Option_isNone(v_00_u03b1_850_, v_x_851_);
    lean_dec(v_x_851_);
    v_r_853_ = lean_box((v_res_852_) as usize);
    return v_r_853_;
}
pub unsafe fn l_Option_isEqSome___redArg(
    mut v_inst_854_: *mut LeanObject,
    mut v_x_855_: *mut LeanObject,
    mut v_x_856_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_855_) == 0 {
        let mut v___x_857_: u8 = 0;
        lean_dec(v_x_856_);
        lean_dec_ref(v_inst_854_);
        v___x_857_ = 0;
        return v___x_857_;
    } else {
        let mut v_val_858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_860_: u8 = 0;
        v_val_858_ = lean_ctor_get(v_x_855_, 0);
        lean_inc(v_val_858_);
        lean_dec_ref_known(v_x_855_, 1);
        v___x_859_ = lean_apply_2(v_inst_854_, v_val_858_, v_x_856_);
        v___x_860_ = (lean_unbox(v___x_859_) as u8);
        return v___x_860_;
    }
}
pub unsafe fn l_Option_isEqSome___redArg___boxed(
    mut v_inst_861_: *mut LeanObject,
    mut v_x_862_: *mut LeanObject,
    mut v_x_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_864_: u8 = 0;
    let mut v_r_865_: *mut LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Option_isEqSome___redArg(v_inst_861_, v_x_862_, v_x_863_);
    v_r_865_ = lean_box((v_res_864_) as usize);
    return v_r_865_;
}
pub unsafe fn l_Option_isEqSome(
    mut v_00_u03b1_866_: *mut LeanObject,
    mut v_inst_867_: *mut LeanObject,
    mut v_x_868_: *mut LeanObject,
    mut v_x_869_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_868_) == 0 {
        let mut v___x_870_: u8 = 0;
        lean_dec(v_x_869_);
        lean_dec_ref(v_inst_867_);
        v___x_870_ = 0;
        return v___x_870_;
    } else {
        let mut v_val_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_873_: u8 = 0;
        v_val_871_ = lean_ctor_get(v_x_868_, 0);
        lean_inc(v_val_871_);
        lean_dec_ref_known(v_x_868_, 1);
        v___x_872_ = lean_apply_2(v_inst_867_, v_val_871_, v_x_869_);
        v___x_873_ = (lean_unbox(v___x_872_) as u8);
        return v___x_873_;
    }
}
pub unsafe fn l_Option_isEqSome___boxed(
    mut v_00_u03b1_874_: *mut LeanObject,
    mut v_inst_875_: *mut LeanObject,
    mut v_x_876_: *mut LeanObject,
    mut v_x_877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_878_: u8 = 0;
    let mut v_r_879_: *mut LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Option_isEqSome(v_00_u03b1_874_, v_inst_875_, v_x_876_, v_x_877_);
    v_r_879_ = lean_box((v_res_878_) as usize);
    return v_r_879_;
}
pub unsafe fn l_Option_bind___redArg(
    mut v_x_880_: *mut LeanObject,
    mut v_x_881_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_880_) == 0 {
        let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_881_);
        v___x_882_ = lean_box(0);
        return v___x_882_;
    } else {
        let mut v_val_883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
        v_val_883_ = lean_ctor_get(v_x_880_, 0);
        lean_inc(v_val_883_);
        lean_dec_ref_known(v_x_880_, 1);
        v___x_884_ = lean_apply_1(v_x_881_, v_val_883_);
        return v___x_884_;
    }
}
pub unsafe fn l_Option_bind(
    mut v_00_u03b1_885_: *mut LeanObject,
    mut v_00_u03b2_886_: *mut LeanObject,
    mut v_x_887_: *mut LeanObject,
    mut v_x_888_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_887_) == 0 {
        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_888_);
        v___x_889_ = lean_box(0);
        return v___x_889_;
    } else {
        let mut v_val_890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
        v_val_890_ = lean_ctor_get(v_x_887_, 0);
        lean_inc(v_val_890_);
        lean_dec_ref_known(v_x_887_, 1);
        v___x_891_ = lean_apply_1(v_x_888_, v_val_890_);
        return v___x_891_;
    }
}
pub unsafe fn l_Option_bindM___redArg(
    mut v_inst_892_: *mut LeanObject,
    mut v_f_893_: *mut LeanObject,
    mut v_x_894_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_894_) == 0 {
        let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_893_);
        v___x_895_ = lean_box(0);
        v___x_896_ = lean_apply_2(v_inst_892_, lean_box(0), v___x_895_);
        return v___x_896_;
    } else {
        let mut v_val_897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_892_);
        v_val_897_ = lean_ctor_get(v_x_894_, 0);
        lean_inc(v_val_897_);
        lean_dec_ref_known(v_x_894_, 1);
        v___x_898_ = lean_apply_1(v_f_893_, v_val_897_);
        return v___x_898_;
    }
}
pub unsafe fn l_Option_bindM(
    mut v_m_899_: *mut LeanObject,
    mut v_00_u03b1_900_: *mut LeanObject,
    mut v_00_u03b2_901_: *mut LeanObject,
    mut v_inst_902_: *mut LeanObject,
    mut v_f_903_: *mut LeanObject,
    mut v_x_904_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_904_) == 0 {
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_903_);
        v___x_905_ = lean_box(0);
        v___x_906_ = lean_apply_2(v_inst_902_, lean_box(0), v___x_905_);
        return v___x_906_;
    } else {
        let mut v_val_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_902_);
        v_val_907_ = lean_ctor_get(v_x_904_, 0);
        lean_inc(v_val_907_);
        lean_dec_ref_known(v_x_904_, 1);
        v___x_908_ = lean_apply_1(v_f_903_, v_val_907_);
        return v___x_908_;
    }
}
pub unsafe fn l_Option_mapM___redArg___lam__0(mut v_val_909_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_910_, 0, v_val_909_);
    return v___x_910_;
}
pub unsafe fn l_Option_mapM___redArg(
    mut v_inst_912_: *mut LeanObject,
    mut v_f_913_: *mut LeanObject,
    mut v_x_914_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_914_) == 0 {
        let mut v_toPure_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_913_);
        v_toPure_915_ = lean_ctor_get(v_inst_912_, 1);
        lean_inc(v_toPure_915_);
        lean_dec_ref(v_inst_912_);
        v___x_916_ = lean_box(0);
        v___x_917_ = lean_apply_2(v_toPure_915_, lean_box(0), v___x_916_);
        return v___x_917_;
    } else {
        let mut v_toFunctor_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_918_ = lean_ctor_get(v_inst_912_, 0);
        lean_inc_ref(v_toFunctor_918_);
        lean_dec_ref(v_inst_912_);
        v_val_919_ = lean_ctor_get(v_x_914_, 0);
        lean_inc(v_val_919_);
        lean_dec_ref_known(v_x_914_, 1);
        v_map_920_ = lean_ctor_get(v_toFunctor_918_, 0);
        lean_inc(v_map_920_);
        lean_dec_ref(v_toFunctor_918_);
        v___f_921_ = l_Option_mapM___redArg___closed__0;
        v___x_922_ = lean_apply_1(v_f_913_, v_val_919_);
        v___x_923_ = lean_apply_4(v_map_920_, lean_box(0), lean_box(0), v___f_921_, v___x_922_);
        return v___x_923_;
    }
}
pub unsafe fn l_Option_mapM(
    mut v_m_924_: *mut LeanObject,
    mut v_00_u03b1_925_: *mut LeanObject,
    mut v_00_u03b2_926_: *mut LeanObject,
    mut v_inst_927_: *mut LeanObject,
    mut v_f_928_: *mut LeanObject,
    mut v_x_929_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_929_) == 0 {
        let mut v_toPure_930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_928_);
        v_toPure_930_ = lean_ctor_get(v_inst_927_, 1);
        lean_inc(v_toPure_930_);
        lean_dec_ref(v_inst_927_);
        v___x_931_ = lean_box(0);
        v___x_932_ = lean_apply_2(v_toPure_930_, lean_box(0), v___x_931_);
        return v___x_932_;
    } else {
        let mut v_toFunctor_933_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_934_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_933_ = lean_ctor_get(v_inst_927_, 0);
        lean_inc_ref(v_toFunctor_933_);
        lean_dec_ref(v_inst_927_);
        v_val_934_ = lean_ctor_get(v_x_929_, 0);
        lean_inc(v_val_934_);
        lean_dec_ref_known(v_x_929_, 1);
        v_map_935_ = lean_ctor_get(v_toFunctor_933_, 0);
        lean_inc(v_map_935_);
        lean_dec_ref(v_toFunctor_933_);
        v___f_936_ = l_Option_mapM___redArg___closed__0;
        v___x_937_ = lean_apply_1(v_f_928_, v_val_934_);
        v___x_938_ = lean_apply_4(v_map_935_, lean_box(0), lean_box(0), v___f_936_, v___x_937_);
        return v___x_938_;
    }
}
pub unsafe fn l_Option_mapA___redArg(
    mut v_inst_939_: *mut LeanObject,
    mut v_f_940_: *mut LeanObject,
    mut v_a_941_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_941_) == 0 {
        let mut v_toPure_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_940_);
        v_toPure_942_ = lean_ctor_get(v_inst_939_, 1);
        lean_inc(v_toPure_942_);
        lean_dec_ref(v_inst_939_);
        v___x_943_ = lean_box(0);
        v___x_944_ = lean_apply_2(v_toPure_942_, lean_box(0), v___x_943_);
        return v___x_944_;
    } else {
        let mut v_toFunctor_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_945_ = lean_ctor_get(v_inst_939_, 0);
        lean_inc_ref(v_toFunctor_945_);
        lean_dec_ref(v_inst_939_);
        v_val_946_ = lean_ctor_get(v_a_941_, 0);
        lean_inc(v_val_946_);
        lean_dec_ref_known(v_a_941_, 1);
        v_map_947_ = lean_ctor_get(v_toFunctor_945_, 0);
        lean_inc(v_map_947_);
        lean_dec_ref(v_toFunctor_945_);
        v___f_948_ = l_Option_mapM___redArg___closed__0;
        v___x_949_ = lean_apply_1(v_f_940_, v_val_946_);
        v___x_950_ = lean_apply_4(v_map_947_, lean_box(0), lean_box(0), v___f_948_, v___x_949_);
        return v___x_950_;
    }
}
pub unsafe fn l_Option_mapA(
    mut v_m_951_: *mut LeanObject,
    mut v_00_u03b1_952_: *mut LeanObject,
    mut v_00_u03b2_953_: *mut LeanObject,
    mut v_inst_954_: *mut LeanObject,
    mut v_f_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_956_) == 0 {
        let mut v_toPure_957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_955_);
        v_toPure_957_ = lean_ctor_get(v_inst_954_, 1);
        lean_inc(v_toPure_957_);
        lean_dec_ref(v_inst_954_);
        v___x_958_ = lean_box(0);
        v___x_959_ = lean_apply_2(v_toPure_957_, lean_box(0), v___x_958_);
        return v___x_959_;
    } else {
        let mut v_toFunctor_960_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_960_ = lean_ctor_get(v_inst_954_, 0);
        lean_inc_ref(v_toFunctor_960_);
        lean_dec_ref(v_inst_954_);
        v_val_961_ = lean_ctor_get(v_a_956_, 0);
        lean_inc(v_val_961_);
        lean_dec_ref_known(v_a_956_, 1);
        v_map_962_ = lean_ctor_get(v_toFunctor_960_, 0);
        lean_inc(v_map_962_);
        lean_dec_ref(v_toFunctor_960_);
        v___f_963_ = l_Option_mapM___redArg___closed__0;
        v___x_964_ = lean_apply_1(v_f_955_, v_val_961_);
        v___x_965_ = lean_apply_4(v_map_962_, lean_box(0), lean_box(0), v___f_963_, v___x_964_);
        return v___x_965_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0(
    mut v_x_966_: *mut LeanObject,
    mut v_b_967_: u8,
) -> *mut LeanObject {
    if v_b_967_ == 0 {
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        v___x_968_ = lean_box(0);
        return v___x_968_;
    } else {
        lean_inc(v_x_966_);
        return v_x_966_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0___boxed(
    mut v_x_969_: *mut LeanObject,
    mut v_b_970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_971_: u8 = 0;
    let mut v_res_972_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_971_ = (lean_unbox(v_b_970_) as u8);
    v_res_972_ = l_Option_filterM___redArg___lam__0(v_x_969_, v_b_boxed_971_);
    lean_dec(v_x_969_);
    return v_res_972_;
}
pub unsafe fn l_Option_filterM___redArg(
    mut v_inst_973_: *mut LeanObject,
    mut v_p_974_: *mut LeanObject,
    mut v_x_975_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_975_) == 0 {
        let mut v_toPure_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_974_);
        v_toPure_976_ = lean_ctor_get(v_inst_973_, 1);
        lean_inc(v_toPure_976_);
        lean_dec_ref(v_inst_973_);
        v___x_977_ = lean_apply_2(v_toPure_976_, lean_box(0), v_x_975_);
        return v___x_977_;
    } else {
        let mut v_toFunctor_978_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_978_ = lean_ctor_get(v_inst_973_, 0);
        lean_inc_ref(v_toFunctor_978_);
        lean_dec_ref(v_inst_973_);
        v_val_979_ = lean_ctor_get(v_x_975_, 0);
        lean_inc(v_val_979_);
        v_map_980_ = lean_ctor_get(v_toFunctor_978_, 0);
        lean_inc(v_map_980_);
        lean_dec_ref(v_toFunctor_978_);
        v___f_981_ = lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_981_, 0, v_x_975_);
        v___x_982_ = lean_apply_1(v_p_974_, v_val_979_);
        v___x_983_ = lean_apply_4(v_map_980_, lean_box(0), lean_box(0), v___f_981_, v___x_982_);
        return v___x_983_;
    }
}
pub unsafe fn l_Option_filterM(
    mut v_m_984_: *mut LeanObject,
    mut v_00_u03b1_985_: *mut LeanObject,
    mut v_inst_986_: *mut LeanObject,
    mut v_p_987_: *mut LeanObject,
    mut v_x_988_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_988_) == 0 {
        let mut v_toPure_989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_987_);
        v_toPure_989_ = lean_ctor_get(v_inst_986_, 1);
        lean_inc(v_toPure_989_);
        lean_dec_ref(v_inst_986_);
        v___x_990_ = lean_apply_2(v_toPure_989_, lean_box(0), v_x_988_);
        return v___x_990_;
    } else {
        let mut v_toFunctor_991_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_992_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_991_ = lean_ctor_get(v_inst_986_, 0);
        lean_inc_ref(v_toFunctor_991_);
        lean_dec_ref(v_inst_986_);
        v_val_992_ = lean_ctor_get(v_x_988_, 0);
        lean_inc(v_val_992_);
        v_map_993_ = lean_ctor_get(v_toFunctor_991_, 0);
        lean_inc(v_map_993_);
        lean_dec_ref(v_toFunctor_991_);
        v___f_994_ = lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_994_, 0, v_x_988_);
        v___x_995_ = lean_apply_1(v_p_987_, v_val_992_);
        v___x_996_ = lean_apply_4(v_map_993_, lean_box(0), lean_box(0), v___f_994_, v___x_995_);
        return v___x_996_;
    }
}
pub unsafe fn l_Option_filter___redArg(
    mut v_p_997_: *mut LeanObject,
    mut v_x_998_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_998_) == 0 {
        lean_dec_ref(v_p_997_);
        return v_x_998_;
    } else {
        let mut v_val_999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: u8 = 0;
        v_val_999_ = lean_ctor_get(v_x_998_, 0);
        lean_inc(v_val_999_);
        v___x_1000_ = lean_apply_1(v_p_997_, v_val_999_);
        v___x_1001_ = (lean_unbox(v___x_1000_) as u8);
        if v___x_1001_ == 0 {
            let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_x_998_, 1);
            v___x_1002_ = lean_box(0);
            return v___x_1002_;
        } else {
            return v_x_998_;
        }
    }
}
pub unsafe fn l_Option_filter(
    mut v_00_u03b1_1003_: *mut LeanObject,
    mut v_p_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1005_) == 0 {
        lean_dec_ref(v_p_1004_);
        return v_x_1005_;
    } else {
        let mut v_val_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_val_1006_ = lean_ctor_get(v_x_1005_, 0);
        lean_inc(v_val_1006_);
        v___x_1007_ = lean_apply_1(v_p_1004_, v_val_1006_);
        v___x_1008_ = (lean_unbox(v___x_1007_) as u8);
        if v___x_1008_ == 0 {
            let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_x_1005_, 1);
            v___x_1009_ = lean_box(0);
            return v___x_1009_;
        } else {
            return v_x_1005_;
        }
    }
}
pub unsafe fn l_Option_all___redArg(
    mut v_p_1010_: *mut LeanObject,
    mut v_x_1011_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1011_) == 0 {
        let mut v___x_1012_: u8 = 0;
        lean_dec_ref(v_p_1010_);
        v___x_1012_ = 1;
        return v___x_1012_;
    } else {
        let mut v_val_1013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: u8 = 0;
        v_val_1013_ = lean_ctor_get(v_x_1011_, 0);
        lean_inc(v_val_1013_);
        lean_dec_ref_known(v_x_1011_, 1);
        v___x_1014_ = lean_apply_1(v_p_1010_, v_val_1013_);
        v___x_1015_ = (lean_unbox(v___x_1014_) as u8);
        return v___x_1015_;
    }
}
pub unsafe fn l_Option_all___redArg___boxed(
    mut v_p_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: u8 = 0;
    let mut v_r_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Option_all___redArg(v_p_1016_, v_x_1017_);
    v_r_1019_ = lean_box((v_res_1018_) as usize);
    return v_r_1019_;
}
pub unsafe fn l_Option_all(
    mut v_00_u03b1_1020_: *mut LeanObject,
    mut v_p_1021_: *mut LeanObject,
    mut v_x_1022_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1022_) == 0 {
        let mut v___x_1023_: u8 = 0;
        lean_dec_ref(v_p_1021_);
        v___x_1023_ = 1;
        return v___x_1023_;
    } else {
        let mut v_val_1024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: u8 = 0;
        v_val_1024_ = lean_ctor_get(v_x_1022_, 0);
        lean_inc(v_val_1024_);
        lean_dec_ref_known(v_x_1022_, 1);
        v___x_1025_ = lean_apply_1(v_p_1021_, v_val_1024_);
        v___x_1026_ = (lean_unbox(v___x_1025_) as u8);
        return v___x_1026_;
    }
}
pub unsafe fn l_Option_all___boxed(
    mut v_00_u03b1_1027_: *mut LeanObject,
    mut v_p_1028_: *mut LeanObject,
    mut v_x_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: u8 = 0;
    let mut v_r_1031_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Option_all(v_00_u03b1_1027_, v_p_1028_, v_x_1029_);
    v_r_1031_ = lean_box((v_res_1030_) as usize);
    return v_r_1031_;
}
pub unsafe fn l_Option_any___redArg(
    mut v_p_1032_: *mut LeanObject,
    mut v_x_1033_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1033_) == 0 {
        let mut v___x_1034_: u8 = 0;
        lean_dec_ref(v_p_1032_);
        v___x_1034_ = 0;
        return v___x_1034_;
    } else {
        let mut v_val_1035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: u8 = 0;
        v_val_1035_ = lean_ctor_get(v_x_1033_, 0);
        lean_inc(v_val_1035_);
        lean_dec_ref_known(v_x_1033_, 1);
        v___x_1036_ = lean_apply_1(v_p_1032_, v_val_1035_);
        v___x_1037_ = (lean_unbox(v___x_1036_) as u8);
        return v___x_1037_;
    }
}
pub unsafe fn l_Option_any___redArg___boxed(
    mut v_p_1038_: *mut LeanObject,
    mut v_x_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1040_: u8 = 0;
    let mut v_r_1041_: *mut LeanObject = core::ptr::null_mut();
    v_res_1040_ = l_Option_any___redArg(v_p_1038_, v_x_1039_);
    v_r_1041_ = lean_box((v_res_1040_) as usize);
    return v_r_1041_;
}
pub unsafe fn l_Option_any(
    mut v_00_u03b1_1042_: *mut LeanObject,
    mut v_p_1043_: *mut LeanObject,
    mut v_x_1044_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1044_) == 0 {
        let mut v___x_1045_: u8 = 0;
        lean_dec_ref(v_p_1043_);
        v___x_1045_ = 0;
        return v___x_1045_;
    } else {
        let mut v_val_1046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: u8 = 0;
        v_val_1046_ = lean_ctor_get(v_x_1044_, 0);
        lean_inc(v_val_1046_);
        lean_dec_ref_known(v_x_1044_, 1);
        v___x_1047_ = lean_apply_1(v_p_1043_, v_val_1046_);
        v___x_1048_ = (lean_unbox(v___x_1047_) as u8);
        return v___x_1048_;
    }
}
pub unsafe fn l_Option_any___boxed(
    mut v_00_u03b1_1049_: *mut LeanObject,
    mut v_p_1050_: *mut LeanObject,
    mut v_x_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1052_: u8 = 0;
    let mut v_r_1053_: *mut LeanObject = core::ptr::null_mut();
    v_res_1052_ = l_Option_any(v_00_u03b1_1049_, v_p_1050_, v_x_1051_);
    v_r_1053_ = lean_box((v_res_1052_) as usize);
    return v_r_1053_;
}
pub unsafe fn l_Option_instOrElse___lam__0(
    mut v_x_1054_: *mut LeanObject,
    mut v_x_1055_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1054_) == 0 {
        let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
        v___x_1056_ = lean_box(0);
        v___x_1057_ = lean_apply_1(v_x_1055_, v___x_1056_);
        return v___x_1057_;
    } else {
        lean_dec_ref(v_x_1055_);
        lean_inc_ref(v_x_1054_);
        return v_x_1054_;
    }
}
pub unsafe fn l_Option_instOrElse___lam__0___boxed(
    mut v_x_1058_: *mut LeanObject,
    mut v_x_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Option_instOrElse___lam__0(v_x_1058_, v_x_1059_);
    lean_dec(v_x_1058_);
    return v_res_1060_;
}
pub unsafe fn l_Option_instOrElse(mut v_00_u03b1_1062_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1063_: *mut LeanObject = core::ptr::null_mut();
    v___f_1063_ = l_Option_instOrElse___closed__0;
    return v___f_1063_;
}
pub unsafe fn l_Option_instDecidableRelLt___redArg(
    mut v_s_1064_: *mut LeanObject,
    mut v_x_1065_: *mut LeanObject,
    mut v_x_1066_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1065_) == 0 {
        lean_dec_ref(v_s_1064_);
        if lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1067_: u8 = 0;
            v___x_1067_ = 0;
            return v___x_1067_;
        } else {
            let mut v___x_1068_: u8 = 0;
            lean_dec_ref_known(v_x_1066_, 1);
            v___x_1068_ = 1;
            return v___x_1068_;
        }
    } else {
        if lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1069_: u8 = 0;
            lean_dec_ref_known(v_x_1065_, 1);
            lean_dec_ref(v_s_1064_);
            v___x_1069_ = 0;
            return v___x_1069_;
        } else {
            let mut v_val_1070_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1071_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1073_: u8 = 0;
            v_val_1070_ = lean_ctor_get(v_x_1065_, 0);
            lean_inc(v_val_1070_);
            lean_dec_ref_known(v_x_1065_, 1);
            v_val_1071_ = lean_ctor_get(v_x_1066_, 0);
            lean_inc(v_val_1071_);
            lean_dec_ref_known(v_x_1066_, 1);
            v___x_1072_ = lean_apply_2(v_s_1064_, v_val_1070_, v_val_1071_);
            v___x_1073_ = (lean_unbox(v___x_1072_) as u8);
            return v___x_1073_;
        }
    }
}
pub unsafe fn l_Option_instDecidableRelLt___redArg___boxed(
    mut v_s_1074_: *mut LeanObject,
    mut v_x_1075_: *mut LeanObject,
    mut v_x_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: u8 = 0;
    let mut v_r_1078_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Option_instDecidableRelLt___redArg(v_s_1074_, v_x_1075_, v_x_1076_);
    v_r_1078_ = lean_box((v_res_1077_) as usize);
    return v_r_1078_;
}
pub unsafe fn l_Option_instDecidableRelLt(
    mut v_00_u03b1_1079_: *mut LeanObject,
    mut v_00_u03b2_1080_: *mut LeanObject,
    mut v_r_1081_: *mut LeanObject,
    mut v_s_1082_: *mut LeanObject,
    mut v_x_1083_: *mut LeanObject,
    mut v_x_1084_: *mut LeanObject,
) -> u8 {
    let mut v___x_1085_: u8 = 0;
    v___x_1085_ = l_Option_instDecidableRelLt___redArg(v_s_1082_, v_x_1083_, v_x_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Option_instDecidableRelLt___boxed(
    mut v_00_u03b1_1086_: *mut LeanObject,
    mut v_00_u03b2_1087_: *mut LeanObject,
    mut v_r_1088_: *mut LeanObject,
    mut v_s_1089_: *mut LeanObject,
    mut v_x_1090_: *mut LeanObject,
    mut v_x_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: u8 = 0;
    let mut v_r_1093_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Option_instDecidableRelLt(
        v_00_u03b1_1086_,
        v_00_u03b2_1087_,
        v_r_1088_,
        v_s_1089_,
        v_x_1090_,
        v_x_1091_,
    );
    v_r_1093_ = lean_box((v_res_1092_) as usize);
    return v_r_1093_;
}
pub unsafe fn l_Option_merge___redArg(
    mut v_fn_1094_: *mut LeanObject,
    mut v_x_1095_: *mut LeanObject,
    mut v_x_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1095_) == 0 {
                    lean_dec(v_fn_1094_);
                    return v_x_1096_;
                } else {
                    if lean_obj_tag(v_x_1096_) == 0 {
                        lean_dec(v_fn_1094_);
                        return v_x_1095_;
                    } else {
                        v_val_1097_ = lean_ctor_get(v_x_1095_, 0);
                        lean_inc(v_val_1097_);
                        lean_dec_ref_known(v_x_1095_, 1);
                        v_val_1098_ = lean_ctor_get(v_x_1096_, 0);
                        v_isSharedCheck_1106_ = (!lean_is_exclusive(v_x_1096_)) as u8;
                        if v_isSharedCheck_1106_ == 0 {
                            v___x_1100_ = v_x_1096_;
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1098_);
                            lean_dec(v_x_1096_);
                            v___x_1100_ = lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1102_ = lean_apply_2(v_fn_1094_, v_val_1097_, v_val_1098_);
                if v_isShared_1101_ == 0 {
                    lean_ctor_set(v___x_1100_, 0, v___x_1102_);
                    v___x_1104_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_merge(
    mut v_00_u03b1_1107_: *mut LeanObject,
    mut v_fn_1108_: *mut LeanObject,
    mut v_x_1109_: *mut LeanObject,
    mut v_x_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Option_merge___redArg(v_fn_1108_, v_x_1109_, v_x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Option_elim___redArg(
    mut v_x_1112_: *mut LeanObject,
    mut v_x_1113_: *mut LeanObject,
    mut v_x_1114_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1112_) == 0 {
        lean_dec(v_x_1114_);
        lean_inc(v_x_1113_);
        return v_x_1113_;
    } else {
        let mut v_val_1115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
        v_val_1115_ = lean_ctor_get(v_x_1112_, 0);
        lean_inc(v_val_1115_);
        lean_dec_ref_known(v_x_1112_, 1);
        v___x_1116_ = lean_apply_1(v_x_1114_, v_val_1115_);
        return v___x_1116_;
    }
}
pub unsafe fn l_Option_elim___redArg___boxed(
    mut v_x_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
    mut v_x_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1120_: *mut LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Option_elim___redArg(v_x_1117_, v_x_1118_, v_x_1119_);
    lean_dec(v_x_1118_);
    return v_res_1120_;
}
pub unsafe fn l_Option_elim(
    mut v_00_u03b1_1121_: *mut LeanObject,
    mut v_00_u03b2_1122_: *mut LeanObject,
    mut v_x_1123_: *mut LeanObject,
    mut v_x_1124_: *mut LeanObject,
    mut v_x_1125_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1123_) == 0 {
        lean_dec(v_x_1125_);
        lean_inc(v_x_1124_);
        return v_x_1124_;
    } else {
        let mut v_val_1126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
        v_val_1126_ = lean_ctor_get(v_x_1123_, 0);
        lean_inc(v_val_1126_);
        lean_dec_ref_known(v_x_1123_, 1);
        v___x_1127_ = lean_apply_1(v_x_1125_, v_val_1126_);
        return v___x_1127_;
    }
}
pub unsafe fn l_Option_elim___boxed(
    mut v_00_u03b1_1128_: *mut LeanObject,
    mut v_00_u03b2_1129_: *mut LeanObject,
    mut v_x_1130_: *mut LeanObject,
    mut v_x_1131_: *mut LeanObject,
    mut v_x_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1133_: *mut LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Option_elim(
        v_00_u03b1_1128_,
        v_00_u03b2_1129_,
        v_x_1130_,
        v_x_1131_,
        v_x_1132_,
    );
    lean_dec(v_x_1131_);
    return v_res_1133_;
}
pub unsafe fn l_Option_get___redArg(mut v_x_1134_: *mut LeanObject) -> *mut LeanObject {
    let mut v_val_1135_: *mut LeanObject = core::ptr::null_mut();
    v_val_1135_ = lean_ctor_get(v_x_1134_, 0);
    lean_inc(v_val_1135_);
    return v_val_1135_;
}
pub unsafe fn l_Option_get___redArg___boxed(mut v_x_1136_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Option_get___redArg(v_x_1136_);
    lean_dec(v_x_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Option_get(
    mut v_00_u03b1_1138_: *mut LeanObject,
    mut v_x_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1141_: *mut LeanObject = core::ptr::null_mut();
    v_val_1141_ = lean_ctor_get(v_x_1139_, 0);
    lean_inc(v_val_1141_);
    return v_val_1141_;
}
pub unsafe fn l_Option_get___boxed(
    mut v_00_u03b1_1142_: *mut LeanObject,
    mut v_x_1143_: *mut LeanObject,
    mut v_x_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1145_: *mut LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Option_get(v_00_u03b1_1142_, v_x_1143_, v_x_1144_);
    lean_dec(v_x_1143_);
    return v_res_1145_;
}
pub unsafe fn l_Option_guard___redArg(
    mut v_p_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    lean_inc(v_a_1147_);
    v___x_1148_ = lean_apply_1(v_p_1146_, v_a_1147_);
    v___x_1149_ = (lean_unbox(v___x_1148_) as u8);
    if v___x_1149_ == 0 {
        let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1147_);
        v___x_1150_ = lean_box(0);
        return v___x_1150_;
    } else {
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        v___x_1151_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1151_, 0, v_a_1147_);
        return v___x_1151_;
    }
}
pub unsafe fn l_Option_guard(
    mut v_00_u03b1_1152_: *mut LeanObject,
    mut v_p_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    lean_inc(v_a_1154_);
    v___x_1155_ = lean_apply_1(v_p_1153_, v_a_1154_);
    v___x_1156_ = (lean_unbox(v___x_1155_) as u8);
    if v___x_1156_ == 0 {
        let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_1154_);
        v___x_1157_ = lean_box(0);
        return v___x_1157_;
    } else {
        let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
        v___x_1158_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1158_, 0, v_a_1154_);
        return v___x_1158_;
    }
}
pub unsafe fn l_Option_toList___redArg(mut v_x_1159_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1159_) == 0 {
        let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
        v___x_1160_ = lean_box(0);
        return v___x_1160_;
    } else {
        let mut v_val_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
        v_val_1161_ = lean_ctor_get(v_x_1159_, 0);
        v___x_1162_ = lean_box(0);
        lean_inc(v_val_1161_);
        v___x_1163_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1163_, 0, v_val_1161_);
        lean_ctor_set(v___x_1163_, 1, v___x_1162_);
        return v___x_1163_;
    }
}
pub unsafe fn l_Option_toList___redArg___boxed(mut v_x_1164_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1165_: *mut LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Option_toList___redArg(v_x_1164_);
    lean_dec(v_x_1164_);
    return v_res_1165_;
}
pub unsafe fn l_Option_toList(
    mut v_00_u03b1_1166_: *mut LeanObject,
    mut v_x_1167_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1167_) == 0 {
        let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
        v___x_1168_ = lean_box(0);
        return v___x_1168_;
    } else {
        let mut v_val_1169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
        v_val_1169_ = lean_ctor_get(v_x_1167_, 0);
        v___x_1170_ = lean_box(0);
        lean_inc(v_val_1169_);
        v___x_1171_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1171_, 0, v_val_1169_);
        lean_ctor_set(v___x_1171_, 1, v___x_1170_);
        return v___x_1171_;
    }
}
pub unsafe fn l_Option_toList___boxed(
    mut v_00_u03b1_1172_: *mut LeanObject,
    mut v_x_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1174_: *mut LeanObject = core::ptr::null_mut();
    v_res_1174_ = l_Option_toList(v_00_u03b1_1172_, v_x_1173_);
    lean_dec(v_x_1173_);
    return v_res_1174_;
}
pub unsafe fn l_Option_toArray___redArg(mut v_x_1177_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1177_) == 0 {
        let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
        v___x_1178_ = l_Option_toArray___redArg___closed__0;
        return v___x_1178_;
    } else {
        let mut v_val_1179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
        v_val_1179_ = lean_ctor_get(v_x_1177_, 0);
        lean_inc(v_val_1179_);
        lean_dec_ref_known(v_x_1177_, 1);
        v___x_1180_ = lean_unsigned_to_nat(1);
        v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
        v___x_1182_ = lean_array_push(v___x_1181_, v_val_1179_);
        return v___x_1182_;
    }
}
pub unsafe fn l_Option_toArray(
    mut v_00_u03b1_1183_: *mut LeanObject,
    mut v_x_1184_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1184_) == 0 {
        let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
        v___x_1185_ = l_Option_toArray___redArg___closed__0;
        return v___x_1185_;
    } else {
        let mut v_val_1186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
        v_val_1186_ = lean_ctor_get(v_x_1184_, 0);
        lean_inc(v_val_1186_);
        lean_dec_ref_known(v_x_1184_, 1);
        v___x_1187_ = lean_unsigned_to_nat(1);
        v___x_1188_ = lean_mk_empty_array_with_capacity(v___x_1187_);
        v___x_1189_ = lean_array_push(v___x_1188_, v_val_1186_);
        return v___x_1189_;
    }
}
pub unsafe fn l_Option_join___redArg(mut v_x_1190_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1190_) == 0 {
        let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
        v___x_1191_ = lean_box(0);
        return v___x_1191_;
    } else {
        let mut v_val_1192_: *mut LeanObject = core::ptr::null_mut();
        v_val_1192_ = lean_ctor_get(v_x_1190_, 0);
        lean_inc(v_val_1192_);
        return v_val_1192_;
    }
}
pub unsafe fn l_Option_join___redArg___boxed(mut v_x_1193_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1194_: *mut LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Option_join___redArg(v_x_1193_);
    lean_dec(v_x_1193_);
    return v_res_1194_;
}
pub unsafe fn l_Option_join(
    mut v_00_u03b1_1195_: *mut LeanObject,
    mut v_x_1196_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1196_) == 0 {
        let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
        v___x_1197_ = lean_box(0);
        return v___x_1197_;
    } else {
        let mut v_val_1198_: *mut LeanObject = core::ptr::null_mut();
        v_val_1198_ = lean_ctor_get(v_x_1196_, 0);
        lean_inc(v_val_1198_);
        return v_val_1198_;
    }
}
pub unsafe fn l_Option_join___boxed(
    mut v_00_u03b1_1199_: *mut LeanObject,
    mut v_x_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1201_: *mut LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Option_join(v_00_u03b1_1199_, v_x_1200_);
    lean_dec(v_x_1200_);
    return v_res_1201_;
}
pub unsafe fn l_Option_sequence___redArg(
    mut v_inst_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1203_) == 0 {
        let mut v_toPure_1204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
        v_toPure_1204_ = lean_ctor_get(v_inst_1202_, 1);
        lean_inc(v_toPure_1204_);
        lean_dec_ref(v_inst_1202_);
        v___x_1205_ = lean_box(0);
        v___x_1206_ = lean_apply_2(v_toPure_1204_, lean_box(0), v___x_1205_);
        return v___x_1206_;
    } else {
        let mut v_toFunctor_1207_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1208_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_1209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_1207_ = lean_ctor_get(v_inst_1202_, 0);
        lean_inc_ref(v_toFunctor_1207_);
        lean_dec_ref(v_inst_1202_);
        v_val_1208_ = lean_ctor_get(v_x_1203_, 0);
        lean_inc(v_val_1208_);
        lean_dec_ref_known(v_x_1203_, 1);
        v_map_1209_ = lean_ctor_get(v_toFunctor_1207_, 0);
        lean_inc(v_map_1209_);
        lean_dec_ref(v_toFunctor_1207_);
        v___f_1210_ = l_Option_mapM___redArg___closed__0;
        v___x_1211_ = lean_apply_4(
            v_map_1209_,
            lean_box(0),
            lean_box(0),
            v___f_1210_,
            v_val_1208_,
        );
        return v___x_1211_;
    }
}
pub unsafe fn l_Option_sequence(
    mut v_m_1212_: *mut LeanObject,
    mut v_inst_1213_: *mut LeanObject,
    mut v_00_u03b1_1214_: *mut LeanObject,
    mut v_x_1215_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1215_) == 0 {
        let mut v_toPure_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
        v_toPure_1216_ = lean_ctor_get(v_inst_1213_, 1);
        lean_inc(v_toPure_1216_);
        lean_dec_ref(v_inst_1213_);
        v___x_1217_ = lean_box(0);
        v___x_1218_ = lean_apply_2(v_toPure_1216_, lean_box(0), v___x_1217_);
        return v___x_1218_;
    } else {
        let mut v_toFunctor_1219_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1220_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_1221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_1219_ = lean_ctor_get(v_inst_1213_, 0);
        lean_inc_ref(v_toFunctor_1219_);
        lean_dec_ref(v_inst_1213_);
        v_val_1220_ = lean_ctor_get(v_x_1215_, 0);
        lean_inc(v_val_1220_);
        lean_dec_ref_known(v_x_1215_, 1);
        v_map_1221_ = lean_ctor_get(v_toFunctor_1219_, 0);
        lean_inc(v_map_1221_);
        lean_dec_ref(v_toFunctor_1219_);
        v___f_1222_ = l_Option_mapM___redArg___closed__0;
        v___x_1223_ = lean_apply_4(
            v_map_1221_,
            lean_box(0),
            lean_box(0),
            v___f_1222_,
            v_val_1220_,
        );
        return v___x_1223_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0(
    mut v_y_1224_: *mut LeanObject,
    mut v_z_1225_: *mut LeanObject,
    mut v_____do__lift_1226_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1226_) == 0 {
        lean_dec(v_z_1225_);
        lean_inc(v_y_1224_);
        return v_y_1224_;
    } else {
        let mut v_val_1227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
        v_val_1227_ = lean_ctor_get(v_____do__lift_1226_, 0);
        lean_inc(v_val_1227_);
        lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1228_ = lean_apply_1(v_z_1225_, v_val_1227_);
        return v___x_1228_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0___boxed(
    mut v_y_1229_: *mut LeanObject,
    mut v_z_1230_: *mut LeanObject,
    mut v_____do__lift_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Option_elimM___redArg___lam__0(v_y_1229_, v_z_1230_, v_____do__lift_1231_);
    lean_dec(v_y_1229_);
    return v_res_1232_;
}
pub unsafe fn l_Option_elimM___redArg(
    mut v_inst_1233_: *mut LeanObject,
    mut v_x_1234_: *mut LeanObject,
    mut v_y_1235_: *mut LeanObject,
    mut v_z_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1237_ = lean_ctor_get(v_inst_1233_, 1);
    lean_inc(v_toBind_1237_);
    lean_dec_ref(v_inst_1233_);
    v___f_1238_ = lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1238_, 0, v_y_1235_);
    lean_closure_set(v___f_1238_, 1, v_z_1236_);
    v___x_1239_ = lean_apply_4(
        v_toBind_1237_,
        lean_box(0),
        lean_box(0),
        v_x_1234_,
        v___f_1238_,
    );
    return v___x_1239_;
}
pub unsafe fn l_Option_elimM(
    mut v_m_1240_: *mut LeanObject,
    mut v_00_u03b1_1241_: *mut LeanObject,
    mut v_00_u03b2_1242_: *mut LeanObject,
    mut v_inst_1243_: *mut LeanObject,
    mut v_x_1244_: *mut LeanObject,
    mut v_y_1245_: *mut LeanObject,
    mut v_z_1246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1247_ = lean_ctor_get(v_inst_1243_, 1);
    lean_inc(v_toBind_1247_);
    lean_dec_ref(v_inst_1243_);
    v___f_1248_ = lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1248_, 0, v_y_1245_);
    lean_closure_set(v___f_1248_, 1, v_z_1246_);
    v___x_1249_ = lean_apply_4(
        v_toBind_1247_,
        lean_box(0),
        lean_box(0),
        v_x_1244_,
        v___f_1248_,
    );
    return v___x_1249_;
}
pub unsafe fn l_Option_getDM___redArg(
    mut v_inst_1250_: *mut LeanObject,
    mut v_x_1251_: *mut LeanObject,
    mut v_y_1252_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1251_) == 0 {
        lean_dec(v_inst_1250_);
        lean_inc(v_y_1252_);
        return v_y_1252_;
    } else {
        let mut v_val_1253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
        v_val_1253_ = lean_ctor_get(v_x_1251_, 0);
        lean_inc(v_val_1253_);
        lean_dec_ref_known(v_x_1251_, 1);
        v___x_1254_ = lean_apply_2(v_inst_1250_, lean_box(0), v_val_1253_);
        return v___x_1254_;
    }
}
pub unsafe fn l_Option_getDM___redArg___boxed(
    mut v_inst_1255_: *mut LeanObject,
    mut v_x_1256_: *mut LeanObject,
    mut v_y_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Option_getDM___redArg(v_inst_1255_, v_x_1256_, v_y_1257_);
    lean_dec(v_y_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Option_getDM(
    mut v_m_1259_: *mut LeanObject,
    mut v_00_u03b1_1260_: *mut LeanObject,
    mut v_inst_1261_: *mut LeanObject,
    mut v_x_1262_: *mut LeanObject,
    mut v_y_1263_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1262_) == 0 {
        lean_dec(v_inst_1261_);
        lean_inc(v_y_1263_);
        return v_y_1263_;
    } else {
        let mut v_val_1264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
        v_val_1264_ = lean_ctor_get(v_x_1262_, 0);
        lean_inc(v_val_1264_);
        lean_dec_ref_known(v_x_1262_, 1);
        v___x_1265_ = lean_apply_2(v_inst_1261_, lean_box(0), v_val_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l_Option_getDM___boxed(
    mut v_m_1266_: *mut LeanObject,
    mut v_00_u03b1_1267_: *mut LeanObject,
    mut v_inst_1268_: *mut LeanObject,
    mut v_x_1269_: *mut LeanObject,
    mut v_y_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Option_getDM(
        v_m_1266_,
        v_00_u03b1_1267_,
        v_inst_1268_,
        v_x_1269_,
        v_y_1270_,
    );
    lean_dec(v_y_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Option_min___redArg(
    mut v_inst_1272_: *mut LeanObject,
    mut v_x_1273_: *mut LeanObject,
    mut v_x_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1273_) == 0 {
                    lean_dec(v_inst_1272_);
                    if lean_obj_tag(v_x_1274_) == 0 {
                        return v_x_1274_;
                    } else {
                        lean_dec_ref_known(v_x_1274_, 1);
                        return v_x_1273_;
                    }
                } else {
                    if lean_obj_tag(v_x_1274_) == 0 {
                        lean_dec_ref_known(v_x_1273_, 1);
                        lean_dec(v_inst_1272_);
                        return v_x_1274_;
                    } else {
                        v_val_1275_ = lean_ctor_get(v_x_1273_, 0);
                        lean_inc(v_val_1275_);
                        lean_dec_ref_known(v_x_1273_, 1);
                        v_val_1276_ = lean_ctor_get(v_x_1274_, 0);
                        v_isSharedCheck_1284_ = (!lean_is_exclusive(v_x_1274_)) as u8;
                        if v_isSharedCheck_1284_ == 0 {
                            v___x_1278_ = v_x_1274_;
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1276_);
                            lean_dec(v_x_1274_);
                            v___x_1278_ = lean_box(0);
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1280_ = lean_apply_2(v_inst_1272_, v_val_1275_, v_val_1276_);
                if v_isShared_1279_ == 0 {
                    lean_ctor_set(v___x_1278_, 0, v___x_1280_);
                    v___x_1282_ = v___x_1278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
                    v___x_1282_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_min(
    mut v_00_u03b1_1285_: *mut LeanObject,
    mut v_inst_1286_: *mut LeanObject,
    mut v_x_1287_: *mut LeanObject,
    mut v_x_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1289_ = l_Option_min___redArg(v_inst_1286_, v_x_1287_, v_x_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Option_instMin___redArg(mut v_inst_1290_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1291_, 0, lean_box(0));
    lean_closure_set(v___x_1291_, 1, v_inst_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Option_instMin(
    mut v_00_u03b1_1292_: *mut LeanObject,
    mut v_inst_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1294_, 0, lean_box(0));
    lean_closure_set(v___x_1294_, 1, v_inst_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Option_max___redArg(
    mut v_inst_1295_: *mut LeanObject,
    mut v_x_1296_: *mut LeanObject,
    mut v_x_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1296_) == 0 {
                    lean_dec(v_inst_1295_);
                    return v_x_1297_;
                } else {
                    if lean_obj_tag(v_x_1297_) == 0 {
                        lean_dec(v_inst_1295_);
                        return v_x_1296_;
                    } else {
                        v_val_1298_ = lean_ctor_get(v_x_1296_, 0);
                        lean_inc(v_val_1298_);
                        lean_dec_ref_known(v_x_1296_, 1);
                        v_val_1299_ = lean_ctor_get(v_x_1297_, 0);
                        v_isSharedCheck_1307_ = (!lean_is_exclusive(v_x_1297_)) as u8;
                        if v_isSharedCheck_1307_ == 0 {
                            v___x_1301_ = v_x_1297_;
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1299_);
                            lean_dec(v_x_1297_);
                            v___x_1301_ = lean_box(0);
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1303_ = lean_apply_2(v_inst_1295_, v_val_1298_, v_val_1299_);
                if v_isShared_1302_ == 0 {
                    lean_ctor_set(v___x_1301_, 0, v___x_1303_);
                    v___x_1305_ = v___x_1301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
                    v___x_1305_ = v_reuseFailAlloc_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_max(
    mut v_00_u03b1_1308_: *mut LeanObject,
    mut v_inst_1309_: *mut LeanObject,
    mut v_x_1310_: *mut LeanObject,
    mut v_x_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Option_max___redArg(v_inst_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Option_instMax___redArg(mut v_inst_1313_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1314_, 0, lean_box(0));
    lean_closure_set(v___x_1314_, 1, v_inst_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Option_instMax(
    mut v_00_u03b1_1315_: *mut LeanObject,
    mut v_inst_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_1317_, 0, lean_box(0));
    lean_closure_set(v___x_1317_, 1, v_inst_1316_);
    return v___x_1317_;
}
pub unsafe fn l_instLTOption(
    mut v_00_u03b1_1318_: *mut LeanObject,
    mut v_inst_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = lean_box(0);
    return v___x_1320_;
}
pub unsafe fn l_instLEOption(
    mut v_00_u03b1_1321_: *mut LeanObject,
    mut v_inst_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1323_ = lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_instFunctorOption___lam__0(
    mut v_00_u03b1_1324_: *mut LeanObject,
    mut v_00_u03b2_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v_unused_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1327_) == 0 {
                    lean_dec(v___y_1326_);
                    v___x_1328_ = lean_box(0);
                    return v___x_1328_;
                } else {
                    v_isSharedCheck_1335_ = (!lean_is_exclusive(v___y_1327_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v_unused_1336_ = lean_ctor_get(v___y_1327_, 0);
                        lean_dec(v_unused_1336_);
                        v___x_1330_ = v___y_1327_;
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_1327_);
                        v___x_1330_ = lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1331_ == 0 {
                    lean_ctor_set(v___x_1330_, 0, v___y_1326_);
                    v___x_1333_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___y_1326_);
                    v___x_1333_ = v_reuseFailAlloc_1334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadOption___lam__0(
    mut v_00_u03b1_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1345_, 0, v___y_1344_);
    return v___x_1345_;
}
pub unsafe fn l_instMonadOption___lam__1(
    mut v_00_u03b1_1346_: *mut LeanObject,
    mut v_00_u03b2_1347_: *mut LeanObject,
    mut v_f_1348_: *mut LeanObject,
    mut v_x_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_1348_) == 0 {
                    lean_dec_ref(v_x_1349_);
                    v___x_1350_ = lean_box(0);
                    return v___x_1350_;
                } else {
                    v_val_1351_ = lean_ctor_get(v_f_1348_, 0);
                    lean_inc(v_val_1351_);
                    lean_dec_ref_known(v_f_1348_, 1);
                    v___x_1352_ = lean_box(0);
                    v___x_1353_ = lean_apply_1(v_x_1349_, v___x_1352_);
                    if lean_obj_tag(v___x_1353_) == 0 {
                        lean_dec(v_val_1351_);
                        v___x_1354_ = lean_box(0);
                        return v___x_1354_;
                    } else {
                        v_val_1355_ = lean_ctor_get(v___x_1353_, 0);
                        v_isSharedCheck_1363_ = (!lean_is_exclusive(v___x_1353_)) as u8;
                        if v_isSharedCheck_1363_ == 0 {
                            v___x_1357_ = v___x_1353_;
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1355_);
                            lean_dec(v___x_1353_);
                            v___x_1357_ = lean_box(0);
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1359_ = lean_apply_1(v_val_1351_, v_val_1355_);
                if v_isShared_1358_ == 0 {
                    lean_ctor_set(v___x_1357_, 0, v___x_1359_);
                    v___x_1361_ = v___x_1357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadOption___lam__2(
    mut v_00_u03b1_1364_: *mut LeanObject,
    mut v_00_u03b2_1365_: *mut LeanObject,
    mut v_x_1366_: *mut LeanObject,
    mut v_y_1367_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1366_) == 0 {
        lean_dec_ref(v_y_1367_);
        return v_x_1366_;
    } else {
        let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
        v___x_1368_ = lean_box(0);
        v___x_1369_ = lean_apply_1(v_y_1367_, v___x_1368_);
        if lean_obj_tag(v___x_1369_) == 0 {
            let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
            v___x_1370_ = lean_box(0);
            return v___x_1370_;
        } else {
            lean_dec_ref_known(v___x_1369_, 1);
            lean_inc_ref(v_x_1366_);
            return v_x_1366_;
        }
    }
}
pub unsafe fn l_instMonadOption___lam__2___boxed(
    mut v_00_u03b1_1371_: *mut LeanObject,
    mut v_00_u03b2_1372_: *mut LeanObject,
    mut v_x_1373_: *mut LeanObject,
    mut v_y_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_instMonadOption___lam__2(v_00_u03b1_1371_, v_00_u03b2_1372_, v_x_1373_, v_y_1374_);
    lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_instMonadOption___lam__3(
    mut v_00_u03b1_1376_: *mut LeanObject,
    mut v_00_u03b2_1377_: *mut LeanObject,
    mut v_x_1378_: *mut LeanObject,
    mut v_y_1379_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1378_) == 0 {
        let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_y_1379_);
        v___x_1380_ = lean_box(0);
        return v___x_1380_;
    } else {
        let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
        v___x_1381_ = lean_box(0);
        v___x_1382_ = lean_apply_1(v_y_1379_, v___x_1381_);
        return v___x_1382_;
    }
}
pub unsafe fn l_instMonadOption___lam__3___boxed(
    mut v_00_u03b1_1383_: *mut LeanObject,
    mut v_00_u03b2_1384_: *mut LeanObject,
    mut v_x_1385_: *mut LeanObject,
    mut v_y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1387_: *mut LeanObject = core::ptr::null_mut();
    v_res_1387_ =
        l_instMonadOption___lam__3(v_00_u03b1_1383_, v_00_u03b2_1384_, v_x_1385_, v_y_1386_);
    lean_dec(v_x_1385_);
    return v_res_1387_;
}
pub unsafe fn l_instAlternativeOption___lam__0(
    mut v_00_u03b1_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = lean_box(0);
    return v___x_1404_;
}
pub unsafe fn l_instAlternativeOption___lam__1(
    mut v_00_u03b1_1405_: *mut LeanObject,
    mut v_x_1406_: *mut LeanObject,
    mut v_x_1407_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1406_) == 0 {
        let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
        v___x_1408_ = lean_box(0);
        v___x_1409_ = lean_apply_1(v_x_1407_, v___x_1408_);
        return v___x_1409_;
    } else {
        lean_dec_ref(v_x_1407_);
        lean_inc_ref(v_x_1406_);
        return v_x_1406_;
    }
}
pub unsafe fn l_instAlternativeOption___lam__1___boxed(
    mut v_00_u03b1_1410_: *mut LeanObject,
    mut v_x_1411_: *mut LeanObject,
    mut v_x_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1413_: *mut LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_instAlternativeOption___lam__1(v_00_u03b1_1410_, v_x_1411_, v_x_1412_);
    lean_dec(v_x_1411_);
    return v_res_1413_;
}
pub unsafe fn l_liftOption___redArg(
    mut v_inst_1421_: *mut LeanObject,
    mut v_x_1422_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1422_) == 0 {
        let mut v_failure_1423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
        v_failure_1423_ = lean_ctor_get(v_inst_1421_, 1);
        lean_inc(v_failure_1423_);
        lean_dec_ref(v_inst_1421_);
        v___x_1424_ = lean_apply_1(v_failure_1423_, lean_box(0));
        return v___x_1424_;
    } else {
        let mut v_toApplicative_1425_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1426_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_1427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1425_ = lean_ctor_get(v_inst_1421_, 0);
        lean_inc_ref(v_toApplicative_1425_);
        lean_dec_ref(v_inst_1421_);
        v_toPure_1426_ = lean_ctor_get(v_toApplicative_1425_, 1);
        lean_inc(v_toPure_1426_);
        lean_dec_ref(v_toApplicative_1425_);
        v_val_1427_ = lean_ctor_get(v_x_1422_, 0);
        lean_inc(v_val_1427_);
        lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ = lean_apply_2(v_toPure_1426_, lean_box(0), v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l_liftOption(
    mut v_m_1429_: *mut LeanObject,
    mut v_00_u03b1_1430_: *mut LeanObject,
    mut v_inst_1431_: *mut LeanObject,
    mut v_x_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_liftOption___redArg(v_inst_1431_, v_x_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Option_tryCatch___redArg(
    mut v_x_1434_: *mut LeanObject,
    mut v_handle_1435_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1434_) == 0 {
        let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
        v___x_1436_ = lean_box(0);
        v___x_1437_ = lean_apply_1(v_handle_1435_, v___x_1436_);
        return v___x_1437_;
    } else {
        lean_dec_ref(v_handle_1435_);
        lean_inc_ref(v_x_1434_);
        return v_x_1434_;
    }
}
pub unsafe fn l_Option_tryCatch___redArg___boxed(
    mut v_x_1438_: *mut LeanObject,
    mut v_handle_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1440_: *mut LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Option_tryCatch___redArg(v_x_1438_, v_handle_1439_);
    lean_dec(v_x_1438_);
    return v_res_1440_;
}
pub unsafe fn l_Option_tryCatch(
    mut v_00_u03b1_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v_handle_1443_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1442_) == 0 {
        let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
        v___x_1444_ = lean_box(0);
        v___x_1445_ = lean_apply_1(v_handle_1443_, v___x_1444_);
        return v___x_1445_;
    } else {
        lean_dec_ref(v_handle_1443_);
        lean_inc_ref(v_x_1442_);
        return v_x_1442_;
    }
}
pub unsafe fn l_Option_tryCatch___boxed(
    mut v_00_u03b1_1446_: *mut LeanObject,
    mut v_x_1447_: *mut LeanObject,
    mut v_handle_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1449_: *mut LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Option_tryCatch(v_00_u03b1_1446_, v_x_1447_, v_handle_1448_);
    lean_dec(v_x_1447_);
    return v_res_1449_;
}
pub unsafe fn l_instMonadExceptOfUnitOption___lam__0(
    mut v_00_u03b1_1450_: *mut LeanObject,
    mut v_x_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = lean_box(0);
    return v___x_1452_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Option_Basic(builtin);
}
