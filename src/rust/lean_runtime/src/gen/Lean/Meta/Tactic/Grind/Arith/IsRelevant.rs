// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.IsRelevant
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt Lean.Meta.Tactic.Grind.Arith.Linear.StructId
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToInt::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
    l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::StructId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
    l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    l_Lean_Meta_Grind_Arith_isIntType, l_Lean_Meta_Grind_Arith_isNatType,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value: LeanStringObject<3> =
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
        m_data: [79, 114, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value)
                as *mut LeanObject,
            14181099489592536354 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [65, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value)
                as *mut LeanObject,
            9743492140944907313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value: LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [68, 118, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 118, 100, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value)
                as *mut LeanObject,
            4493959381811283967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value)
                as *mut LeanObject,
            1297950917268934889 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value: LeanStringObject<3> =
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
        m_data: [76, 84, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value: LeanStringObject<3> =
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
        m_data: [108, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value: LeanStringObject<3> =
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
        m_data: [76, 69, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value: LeanStringObject<3> =
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
        m_data: [108, 101, 0],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__14_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__15_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_isSupportedType(
    mut v_00_u03b1_177_: *mut LeanObject,
    mut v_a_178_: *mut LeanObject,
    mut v_a_179_: *mut LeanObject,
    mut v_a_180_: *mut LeanObject,
    mut v_a_181_: *mut LeanObject,
    mut v_a_182_: *mut LeanObject,
    mut v_a_183_: *mut LeanObject,
    mut v_a_184_: *mut LeanObject,
    mut v_a_185_: *mut LeanObject,
    mut v_a_186_: *mut LeanObject,
    mut v_a_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_190_: u8 = 0;
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_196_: u8 = 0;
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_201_: u8 = 0;
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_210_: u8 = 0;
    let mut v_a_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_218_: u8 = 0;
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_223_: u8 = 0;
    let mut v_a_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_227_: u8 = 0;
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_231_: u8 = 0;
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    let mut v___x_235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_234_ = l_Lean_Meta_Grind_Arith_isNatType(v_00_u03b1_177_);
                if v___x_234_ == 0 {
                    v___x_235_ = l_Lean_Meta_Grind_Arith_isIntType(v_00_u03b1_177_);
                    v___y_190_ = v___x_235_;
                    state = 1;
                    continue;
                } else {
                    v___y_190_ = v___x_234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_191_ = 1;
                if v___y_190_ == 0 {
                    lean_inc_ref(v_00_u03b1_177_);
                    v___x_192_ = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(
                        v_00_u03b1_177_,
                        v_a_178_,
                        v_a_179_,
                        v_a_180_,
                        v_a_181_,
                        v_a_182_,
                        v_a_183_,
                        v_a_184_,
                        v_a_185_,
                        v_a_186_,
                        v_a_187_,
                    );
                    if lean_obj_tag(v___x_192_) == 0 {
                        v_a_193_ = lean_ctor_get(v___x_192_, 0);
                        v_isSharedCheck_223_ = (!lean_is_exclusive(v___x_192_)) as u8;
                        if v_isSharedCheck_223_ == 0 {
                            v___x_195_ = v___x_192_;
                            v_isShared_196_ = v_isSharedCheck_223_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_193_);
                            lean_dec(v___x_192_);
                            v___x_195_ = lean_box(0);
                            v_isShared_196_ = v_isSharedCheck_223_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_00_u03b1_177_);
                        v_a_224_ = lean_ctor_get(v___x_192_, 0);
                        v_isSharedCheck_231_ = (!lean_is_exclusive(v___x_192_)) as u8;
                        if v_isSharedCheck_231_ == 0 {
                            v___x_226_ = v___x_192_;
                            v_isShared_227_ = v_isSharedCheck_231_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_224_);
                            lean_dec(v___x_192_);
                            v___x_226_ = lean_box(0);
                            v_isShared_227_ = v_isSharedCheck_231_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_00_u03b1_177_);
                    v___x_232_ = lean_box((v___x_191_) as usize);
                    v___x_233_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_233_, 0, v___x_232_);
                    return v___x_233_;
                }
            }
            2 => {
                if lean_obj_tag(v_a_193_) == 0 {
                    lean_del_object(v___x_195_);
                    v___x_197_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(
                        v_00_u03b1_177_,
                        v_a_178_,
                        v_a_179_,
                        v_a_180_,
                        v_a_181_,
                        v_a_182_,
                        v_a_183_,
                        v_a_184_,
                        v_a_185_,
                        v_a_186_,
                        v_a_187_,
                    );
                    if lean_obj_tag(v___x_197_) == 0 {
                        v_a_198_ = lean_ctor_get(v___x_197_, 0);
                        v_isSharedCheck_210_ = (!lean_is_exclusive(v___x_197_)) as u8;
                        if v_isSharedCheck_210_ == 0 {
                            v___x_200_ = v___x_197_;
                            v_isShared_201_ = v_isSharedCheck_210_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_198_);
                            lean_dec(v___x_197_);
                            v___x_200_ = lean_box(0);
                            v_isShared_201_ = v_isSharedCheck_210_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_211_ = lean_ctor_get(v___x_197_, 0);
                        v_isSharedCheck_218_ = (!lean_is_exclusive(v___x_197_)) as u8;
                        if v_isSharedCheck_218_ == 0 {
                            v___x_213_ = v___x_197_;
                            v_isShared_214_ = v_isSharedCheck_218_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_211_);
                            lean_dec(v___x_197_);
                            v___x_213_ = lean_box(0);
                            v_isShared_214_ = v_isSharedCheck_218_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_a_193_, 1);
                    lean_dec_ref(v_00_u03b1_177_);
                    v___x_219_ = lean_box((v___x_191_) as usize);
                    if v_isShared_196_ == 0 {
                        lean_ctor_set(v___x_195_, 0, v___x_219_);
                        v___x_221_ = v___x_195_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
                        v___x_221_ = v_reuseFailAlloc_222_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_198_) == 0 {
                    v___x_202_ = lean_box((v___y_190_) as usize);
                    if v_isShared_201_ == 0 {
                        lean_ctor_set(v___x_200_, 0, v___x_202_);
                        v___x_204_ = v___x_200_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
                        v___x_204_ = v_reuseFailAlloc_205_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_198_, 1);
                    v___x_206_ = lean_box((v___x_191_) as usize);
                    if v_isShared_201_ == 0 {
                        lean_ctor_set(v___x_200_, 0, v___x_206_);
                        v___x_208_ = v___x_200_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
                        v___x_208_ = v_reuseFailAlloc_209_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_204_;
            }
            5 => {
                return v___x_208_;
            }
            6 => {
                if v_isShared_214_ == 0 {
                    v___x_216_ = v___x_213_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
                    v___x_216_ = v_reuseFailAlloc_217_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_216_;
            }
            8 => {
                return v___x_221_;
            }
            9 => {
                if v_isShared_227_ == 0 {
                    v___x_229_ = v___x_226_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
                    v___x_229_ = v_reuseFailAlloc_230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isSupportedType___boxed(
    mut v_00_u03b1_236_: *mut LeanObject,
    mut v_a_237_: *mut LeanObject,
    mut v_a_238_: *mut LeanObject,
    mut v_a_239_: *mut LeanObject,
    mut v_a_240_: *mut LeanObject,
    mut v_a_241_: *mut LeanObject,
    mut v_a_242_: *mut LeanObject,
    mut v_a_243_: *mut LeanObject,
    mut v_a_244_: *mut LeanObject,
    mut v_a_245_: *mut LeanObject,
    mut v_a_246_: *mut LeanObject,
    mut v_a_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_248_: *mut LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Lean_Meta_Grind_Arith_isSupportedType(
        v_00_u03b1_236_,
        v_a_237_,
        v_a_238_,
        v_a_239_,
        v_a_240_,
        v_a_241_,
        v_a_242_,
        v_a_243_,
        v_a_244_,
        v_a_245_,
        v_a_246_,
    );
    lean_dec(v_a_246_);
    lean_dec_ref(v_a_245_);
    lean_dec(v_a_244_);
    lean_dec_ref(v_a_243_);
    lean_dec(v_a_242_);
    lean_dec_ref(v_a_241_);
    lean_dec(v_a_240_);
    lean_dec_ref(v_a_239_);
    lean_dec(v_a_238_);
    lean_dec(v_a_237_);
    return v_res_248_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isRelevantPred(
    mut v_e_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_a_284_: *mut LeanObject,
    mut v_a_285_: *mut LeanObject,
    mut v_a_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_289_: u8 = 0;
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: u8 = 0;
    let mut v_arg_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: u8 = 0;
    let mut v___x_298_: u8 = 0;
    let mut v_arg_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: u8 = 0;
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: u8 = 0;
    let mut v___x_321_: u8 = 0;
    let mut v_arg_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: u8 = 0;
    let mut v_arg_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: u8 = 0;
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: u8 = 0;
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_292_ = l_Lean_Expr_cleanupAnnotations(v_e_276_);
                v___x_293_ = l_Lean_Expr_isApp(v___x_292_);
                if v___x_293_ == 0 {
                    lean_dec_ref(v___x_292_);
                    state = 1;
                    continue;
                } else {
                    v_arg_294_ = lean_ctor_get(v___x_292_, 1);
                    lean_inc_ref(v_arg_294_);
                    v___x_295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
                    v___x_296_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1;
                    v___x_297_ = l_Lean_Expr_isConstOf(v___x_295_, v___x_296_);
                    if v___x_297_ == 0 {
                        v___x_298_ = l_Lean_Expr_isApp(v___x_295_);
                        if v___x_298_ == 0 {
                            lean_dec_ref(v___x_295_);
                            lean_dec_ref(v_arg_294_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_299_ = lean_ctor_get(v___x_295_, 1);
                            lean_inc_ref(v_arg_299_);
                            v___x_316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_295_);
                            v___x_317_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3;
                            v___x_318_ = l_Lean_Expr_isConstOf(v___x_316_, v___x_317_);
                            if v___x_318_ == 0 {
                                v___x_319_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5;
                                v___x_320_ = l_Lean_Expr_isConstOf(v___x_316_, v___x_319_);
                                if v___x_320_ == 0 {
                                    lean_dec_ref(v_arg_299_);
                                    lean_dec_ref(v_arg_294_);
                                    v___x_321_ = l_Lean_Expr_isApp(v___x_316_);
                                    if v___x_321_ == 0 {
                                        lean_dec_ref(v___x_316_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_322_ = lean_ctor_get(v___x_316_, 1);
                                        lean_inc_ref(v_arg_322_);
                                        v___x_323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_316_);
                                        v___x_324_ =
                                            l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7;
                                        v___x_325_ = l_Lean_Expr_isConstOf(v___x_323_, v___x_324_);
                                        if v___x_325_ == 0 {
                                            lean_dec_ref(v_arg_322_);
                                            v___x_326_ = l_Lean_Expr_isApp(v___x_323_);
                                            if v___x_326_ == 0 {
                                                lean_dec_ref(v___x_323_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_arg_327_ = lean_ctor_get(v___x_323_, 1);
                                                lean_inc_ref(v_arg_327_);
                                                v___x_328_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_323_);
                                                v___x_329_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10;
                                                v___x_330_ =
                                                    l_Lean_Expr_isConstOf(v___x_328_, v___x_329_);
                                                if v___x_330_ == 0 {
                                                    v___x_331_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__13;
                                                    v___x_332_ = l_Lean_Expr_isConstOf(
                                                        v___x_328_, v___x_331_,
                                                    );
                                                    if v___x_332_ == 0 {
                                                        v___x_333_ = l_Lean_Meta_Grind_Arith_isRelevantPred___closed__16;
                                                        v___x_334_ = l_Lean_Expr_isConstOf(
                                                            v___x_328_, v___x_333_,
                                                        );
                                                        lean_dec_ref(v___x_328_);
                                                        if v___x_334_ == 0 {
                                                            lean_dec_ref(v_arg_327_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_335_ = l_Lean_Meta_Grind_Arith_isSupportedType(v_arg_327_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
                                                            return v___x_335_;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v___x_328_);
                                                        v___x_336_ =
                                                            l_Lean_Meta_Grind_Arith_isSupportedType(
                                                                v_arg_327_, v_a_277_, v_a_278_,
                                                                v_a_279_, v_a_280_, v_a_281_,
                                                                v_a_282_, v_a_283_, v_a_284_,
                                                                v_a_285_, v_a_286_,
                                                            );
                                                        return v___x_336_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_328_);
                                                    v___x_337_ =
                                                        l_Lean_Meta_Grind_Arith_isSupportedType(
                                                            v_arg_327_, v_a_277_, v_a_278_,
                                                            v_a_279_, v_a_280_, v_a_281_, v_a_282_,
                                                            v_a_283_, v_a_284_, v_a_285_, v_a_286_,
                                                        );
                                                    return v___x_337_;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_323_);
                                            v___x_338_ = l_Lean_Meta_Grind_Arith_isSupportedType(
                                                v_arg_322_, v_a_277_, v_a_278_, v_a_279_, v_a_280_,
                                                v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_,
                                                v_a_286_,
                                            );
                                            return v___x_338_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_316_);
                                    v_q_301_ = v_arg_294_;
                                    v___y_302_ = v_a_277_;
                                    v___y_303_ = v_a_278_;
                                    v___y_304_ = v_a_279_;
                                    v___y_305_ = v_a_280_;
                                    v___y_306_ = v_a_281_;
                                    v___y_307_ = v_a_282_;
                                    v___y_308_ = v_a_283_;
                                    v___y_309_ = v_a_284_;
                                    v___y_310_ = v_a_285_;
                                    v___y_311_ = v_a_286_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_316_);
                                v_q_301_ = v_arg_294_;
                                v___y_302_ = v_a_277_;
                                v___y_303_ = v_a_278_;
                                v___y_304_ = v_a_279_;
                                v___y_305_ = v_a_280_;
                                v___y_306_ = v_a_281_;
                                v___y_307_ = v_a_282_;
                                v___y_308_ = v_a_283_;
                                v___y_309_ = v_a_284_;
                                v___y_310_ = v_a_285_;
                                v___y_311_ = v_a_286_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_295_);
                        v_e_276_ = v_arg_294_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_289_ = 0;
                v___x_290_ = lean_box((v___x_289_) as usize);
                v___x_291_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_291_, 0, v___x_290_);
                return v___x_291_;
            }
            2 => {
                v___x_312_ = l_Lean_Meta_Grind_Arith_isRelevantPred(
                    v_arg_299_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_,
                    v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_,
                );
                if lean_obj_tag(v___x_312_) == 0 {
                    v_a_313_ = lean_ctor_get(v___x_312_, 0);
                    lean_inc(v_a_313_);
                    v___x_314_ = (lean_unbox(v_a_313_) as u8);
                    lean_dec(v_a_313_);
                    if v___x_314_ == 0 {
                        lean_dec_ref_known(v___x_312_, 1);
                        v_e_276_ = v_q_301_;
                        v_a_277_ = v___y_302_;
                        v_a_278_ = v___y_303_;
                        v_a_279_ = v___y_304_;
                        v_a_280_ = v___y_305_;
                        v_a_281_ = v___y_306_;
                        v_a_282_ = v___y_307_;
                        v_a_283_ = v___y_308_;
                        v_a_284_ = v___y_309_;
                        v_a_285_ = v___y_310_;
                        v_a_286_ = v___y_311_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_q_301_);
                        return v___x_312_;
                    }
                } else {
                    lean_dec_ref(v_q_301_);
                    return v___x_312_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(
    mut v_e_340_: *mut LeanObject,
    mut v_a_341_: *mut LeanObject,
    mut v_a_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
    mut v_a_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
    mut v_a_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
    mut v_a_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_352_: *mut LeanObject = core::ptr::null_mut();
    v_res_352_ = l_Lean_Meta_Grind_Arith_isRelevantPred(
        v_e_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_,
        v_a_349_, v_a_350_,
    );
    lean_dec(v_a_350_);
    lean_dec_ref(v_a_349_);
    lean_dec(v_a_348_);
    lean_dec_ref(v_a_347_);
    lean_dec(v_a_346_);
    lean_dec_ref(v_a_345_);
    lean_dec(v_a_344_);
    lean_dec_ref(v_a_343_);
    lean_dec(v_a_342_);
    lean_dec(v_a_341_);
    return v_res_352_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(builtin);
}
