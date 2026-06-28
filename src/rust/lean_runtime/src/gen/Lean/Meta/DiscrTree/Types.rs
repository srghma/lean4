// Lean compiler output
// Module: Lean.Meta.DiscrTree.Types
// Imports: Lean.Expr
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Literal_hash, l_Lean_instBEqFVarId_beq, l_Lean_instBEqLiteral_beq,
    l_Lean_instHashableFVarId_hash, l_Lean_instReprLiteral_repr, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_box_uint64, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_DiscrTree_instInhabitedKey_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_DiscrTree_instInhabitedKey: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_instBEqKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_DiscrTree_instBEqKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instBEqKey___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 97, 114, 114, 111, 119, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 115, 116, 97, 114, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 111, 116, 104, 101, 114, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 108, 105, 116, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__9_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 102, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__12_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 99, 111, 110, 115, 116, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__15_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101,
            46, 75, 101, 121, 46, 112, 114, 111, 106, 0,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__18_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_instReprKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_instReprKey_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_instReprKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_DiscrTree_instReprKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instReprKey___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_Key_hash___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_Key_hash___closed__0: u64 = 0;
pub static l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_Key_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_instHashableKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_DiscrTree_instHashableKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_instHashableKey___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_DiscrTree_Key_ctorIdx(mut v_x_352_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_352_) {
        0 => {
            let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
            v___x_353_ = lean_unsigned_to_nat(0);
            return v___x_353_;
        }
        1 => {
            let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
            v___x_354_ = lean_unsigned_to_nat(1);
            return v___x_354_;
        }
        2 => {
            let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
            v___x_355_ = lean_unsigned_to_nat(2);
            return v___x_355_;
        }
        3 => {
            let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
            v___x_356_ = lean_unsigned_to_nat(3);
            return v___x_356_;
        }
        4 => {
            let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
            v___x_357_ = lean_unsigned_to_nat(4);
            return v___x_357_;
        }
        5 => {
            let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
            v___x_358_ = lean_unsigned_to_nat(5);
            return v___x_358_;
        }
        _ => {
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            v___x_359_ = lean_unsigned_to_nat(6);
            return v___x_359_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_ctorIdx___boxed(
    mut v_x_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_361_: *mut LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_x_360_);
    lean_dec(v_x_360_);
    return v_res_361_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(
    mut v_t_362_: *mut LeanObject,
    mut v_k_363_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_362_) {
        2 => {
            let mut v_a_364_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            v_a_364_ = lean_ctor_get(v_t_362_, 0);
            lean_inc_ref(v_a_364_);
            lean_dec_ref_known(v_t_362_, 1);
            v___x_365_ = lean_apply_1(v_k_363_, v_a_364_);
            return v___x_365_;
        }
        3 => {
            let mut v_a_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            v_a_366_ = lean_ctor_get(v_t_362_, 0);
            lean_inc(v_a_366_);
            v_a_367_ = lean_ctor_get(v_t_362_, 1);
            lean_inc(v_a_367_);
            lean_dec_ref_known(v_t_362_, 2);
            v___x_368_ = lean_apply_2(v_k_363_, v_a_366_, v_a_367_);
            return v___x_368_;
        }
        4 => {
            let mut v_a_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
            v_a_369_ = lean_ctor_get(v_t_362_, 0);
            lean_inc(v_a_369_);
            v_a_370_ = lean_ctor_get(v_t_362_, 1);
            lean_inc(v_a_370_);
            lean_dec_ref_known(v_t_362_, 2);
            v___x_371_ = lean_apply_2(v_k_363_, v_a_369_, v_a_370_);
            return v___x_371_;
        }
        6 => {
            let mut v_a_372_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_373_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_374_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
            v_a_372_ = lean_ctor_get(v_t_362_, 0);
            lean_inc(v_a_372_);
            v_a_373_ = lean_ctor_get(v_t_362_, 1);
            lean_inc(v_a_373_);
            v_a_374_ = lean_ctor_get(v_t_362_, 2);
            lean_inc(v_a_374_);
            lean_dec_ref_known(v_t_362_, 3);
            v___x_375_ = lean_apply_3(v_k_363_, v_a_372_, v_a_373_, v_a_374_);
            return v___x_375_;
        }
        _ => {
            lean_dec(v_t_362_);
            return v_k_363_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_ctorElim(
    mut v_motive_376_: *mut LeanObject,
    mut v_ctorIdx_377_: *mut LeanObject,
    mut v_t_378_: *mut LeanObject,
    mut v_h_379_: *mut LeanObject,
    mut v_k_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___x_381_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_378_, v_k_380_);
    return v___x_381_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_ctorElim___boxed(
    mut v_motive_382_: *mut LeanObject,
    mut v_ctorIdx_383_: *mut LeanObject,
    mut v_t_384_: *mut LeanObject,
    mut v_h_385_: *mut LeanObject,
    mut v_k_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Lean_Meta_DiscrTree_Key_ctorElim(
        v_motive_382_,
        v_ctorIdx_383_,
        v_t_384_,
        v_h_385_,
        v_k_386_,
    );
    lean_dec(v_ctorIdx_383_);
    return v_res_387_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_star_elim___redArg(
    mut v_t_388_: *mut LeanObject,
    mut v_star_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_388_, v_star_389_);
    return v___x_390_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_star_elim(
    mut v_motive_391_: *mut LeanObject,
    mut v_t_392_: *mut LeanObject,
    mut v_h_393_: *mut LeanObject,
    mut v_star_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_392_, v_star_394_);
    return v___x_395_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_other_elim___redArg(
    mut v_t_396_: *mut LeanObject,
    mut v_other_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_396_, v_other_397_);
    return v___x_398_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_other_elim(
    mut v_motive_399_: *mut LeanObject,
    mut v_t_400_: *mut LeanObject,
    mut v_h_401_: *mut LeanObject,
    mut v_other_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v___x_403_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_400_, v_other_402_);
    return v___x_403_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_lit_elim___redArg(
    mut v_t_404_: *mut LeanObject,
    mut v_lit_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_404_, v_lit_405_);
    return v___x_406_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_lit_elim(
    mut v_motive_407_: *mut LeanObject,
    mut v_t_408_: *mut LeanObject,
    mut v_h_409_: *mut LeanObject,
    mut v_lit_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_408_, v_lit_410_);
    return v___x_411_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_fvar_elim___redArg(
    mut v_t_412_: *mut LeanObject,
    mut v_fvar_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_412_, v_fvar_413_);
    return v___x_414_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_fvar_elim(
    mut v_motive_415_: *mut LeanObject,
    mut v_t_416_: *mut LeanObject,
    mut v_h_417_: *mut LeanObject,
    mut v_fvar_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_416_, v_fvar_418_);
    return v___x_419_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_const_elim___redArg(
    mut v_t_420_: *mut LeanObject,
    mut v_const_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_420_, v_const_421_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_const_elim(
    mut v_motive_423_: *mut LeanObject,
    mut v_t_424_: *mut LeanObject,
    mut v_h_425_: *mut LeanObject,
    mut v_const_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_424_, v_const_426_);
    return v___x_427_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_arrow_elim___redArg(
    mut v_t_428_: *mut LeanObject,
    mut v_arrow_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_428_, v_arrow_429_);
    return v___x_430_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_arrow_elim(
    mut v_motive_431_: *mut LeanObject,
    mut v_t_432_: *mut LeanObject,
    mut v_h_433_: *mut LeanObject,
    mut v_arrow_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_432_, v_arrow_434_);
    return v___x_435_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_proj_elim___redArg(
    mut v_t_436_: *mut LeanObject,
    mut v_proj_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_436_, v_proj_437_);
    return v___x_438_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_proj_elim(
    mut v_motive_439_: *mut LeanObject,
    mut v_t_440_: *mut LeanObject,
    mut v_h_441_: *mut LeanObject,
    mut v_proj_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_443_ = l_Lean_Meta_DiscrTree_Key_ctorElim___redArg(v_t_440_, v_proj_442_);
    return v___x_443_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instInhabitedKey_default() -> *mut LeanObject {
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v___x_444_ = lean_box(0);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instInhabitedKey() -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_box(0);
    return v___x_445_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instBEqKey_beq(
    mut v_x_446_: *mut LeanObject,
    mut v_x_447_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_446_) {
        0 => {
            if lean_obj_tag(v_x_447_) == 0 {
                let mut v___x_448_: u8 = 0;
                v___x_448_ = 1;
                return v___x_448_;
            } else {
                let mut v___x_449_: u8 = 0;
                v___x_449_ = 0;
                return v___x_449_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_447_) == 1 {
                let mut v___x_450_: u8 = 0;
                v___x_450_ = 1;
                return v___x_450_;
            } else {
                let mut v___x_451_: u8 = 0;
                v___x_451_ = 0;
                return v___x_451_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_447_) == 2 {
                let mut v_a_452_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_453_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_454_: u8 = 0;
                v_a_452_ = lean_ctor_get(v_x_446_, 0);
                v_a_453_ = lean_ctor_get(v_x_447_, 0);
                v___x_454_ = l_Lean_instBEqLiteral_beq(v_a_452_, v_a_453_);
                return v___x_454_;
            } else {
                let mut v___x_455_: u8 = 0;
                v___x_455_ = 0;
                return v___x_455_;
            }
        }
        3 => {
            if lean_obj_tag(v_x_447_) == 3 {
                let mut v_a_456_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_457_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_458_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_459_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_460_: u8 = 0;
                v_a_456_ = lean_ctor_get(v_x_446_, 0);
                v_a_457_ = lean_ctor_get(v_x_446_, 1);
                v_a_458_ = lean_ctor_get(v_x_447_, 0);
                v_a_459_ = lean_ctor_get(v_x_447_, 1);
                v___x_460_ = l_Lean_instBEqFVarId_beq(v_a_456_, v_a_458_);
                if v___x_460_ == 0 {
                    return v___x_460_;
                } else {
                    let mut v___x_461_: u8 = 0;
                    v___x_461_ = lean_nat_dec_eq(v_a_457_, v_a_459_);
                    return v___x_461_;
                }
            } else {
                let mut v___x_462_: u8 = 0;
                v___x_462_ = 0;
                return v___x_462_;
            }
        }
        4 => {
            if lean_obj_tag(v_x_447_) == 4 {
                let mut v_a_463_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_464_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_465_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_466_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_467_: u8 = 0;
                v_a_463_ = lean_ctor_get(v_x_446_, 0);
                v_a_464_ = lean_ctor_get(v_x_446_, 1);
                v_a_465_ = lean_ctor_get(v_x_447_, 0);
                v_a_466_ = lean_ctor_get(v_x_447_, 1);
                v___x_467_ = lean_name_eq(v_a_463_, v_a_465_);
                if v___x_467_ == 0 {
                    return v___x_467_;
                } else {
                    let mut v___x_468_: u8 = 0;
                    v___x_468_ = lean_nat_dec_eq(v_a_464_, v_a_466_);
                    return v___x_468_;
                }
            } else {
                let mut v___x_469_: u8 = 0;
                v___x_469_ = 0;
                return v___x_469_;
            }
        }
        5 => {
            if lean_obj_tag(v_x_447_) == 5 {
                let mut v___x_470_: u8 = 0;
                v___x_470_ = 1;
                return v___x_470_;
            } else {
                let mut v___x_471_: u8 = 0;
                v___x_471_ = 0;
                return v___x_471_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_447_) == 6 {
                let mut v_a_472_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_473_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_474_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_475_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_476_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_477_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_478_: u8 = 0;
                v_a_472_ = lean_ctor_get(v_x_446_, 0);
                v_a_473_ = lean_ctor_get(v_x_446_, 1);
                v_a_474_ = lean_ctor_get(v_x_446_, 2);
                v_a_475_ = lean_ctor_get(v_x_447_, 0);
                v_a_476_ = lean_ctor_get(v_x_447_, 1);
                v_a_477_ = lean_ctor_get(v_x_447_, 2);
                v___x_478_ = lean_name_eq(v_a_472_, v_a_475_);
                if v___x_478_ == 0 {
                    return v___x_478_;
                } else {
                    let mut v___x_479_: u8 = 0;
                    v___x_479_ = lean_nat_dec_eq(v_a_473_, v_a_476_);
                    if v___x_479_ == 0 {
                        return v___x_479_;
                    } else {
                        let mut v___x_480_: u8 = 0;
                        v___x_480_ = lean_nat_dec_eq(v_a_474_, v_a_477_);
                        return v___x_480_;
                    }
                }
            } else {
                let mut v___x_481_: u8 = 0;
                v___x_481_ = 0;
                return v___x_481_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(
    mut v_x_482_: *mut LeanObject,
    mut v_x_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: u8 = 0;
    let mut v_r_485_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_482_, v_x_483_);
    lean_dec(v_x_483_);
    lean_dec(v_x_482_);
    v_r_485_ = lean_box((v_res_484_) as usize);
    return v_r_485_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6() -> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = lean_unsigned_to_nat(2);
    v___x_498_ = lean_nat_to_int(v___x_497_);
    return v___x_498_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7() -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_unsigned_to_nat(1);
    v___x_500_ = lean_nat_to_int(v___x_499_);
    return v___x_500_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_instReprKey_repr(
    mut v_x_525_: *mut LeanObject,
    mut v_prec_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: u8 = 0;
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u8 = 0;
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_575_: u8 = 0;
    let mut v___y_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: u8 = 0;
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut v_a_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v___y_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_525_) {
                0 => {
                    v___x_548_ = lean_unsigned_to_nat(1024);
                    v___x_549_ = lean_nat_dec_le(v___x_548_, v_prec_526_);
                    if v___x_549_ == 0 {
                        v___x_550_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                        );
                        v___y_535_ = v___x_550_;
                        state = 2;
                        continue;
                    } else {
                        v___x_551_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                        );
                        v___y_535_ = v___x_551_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v___x_552_ = lean_unsigned_to_nat(1024);
                    v___x_553_ = lean_nat_dec_le(v___x_552_, v_prec_526_);
                    if v___x_553_ == 0 {
                        v___x_554_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                        );
                        v___y_542_ = v___x_554_;
                        state = 3;
                        continue;
                    } else {
                        v___x_555_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                        );
                        v___y_542_ = v___x_555_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_556_ = lean_ctor_get(v_x_525_, 0);
                    lean_inc_ref(v_a_556_);
                    lean_dec_ref_known(v_x_525_, 1);
                    v___x_567_ = lean_unsigned_to_nat(1024);
                    v___x_568_ = lean_nat_dec_le(v___x_567_, v_prec_526_);
                    if v___x_568_ == 0 {
                        v___x_569_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                        );
                        v___y_558_ = v___x_569_;
                        state = 4;
                        continue;
                    } else {
                        v___x_570_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                        );
                        v___y_558_ = v___x_570_;
                        state = 4;
                        continue;
                    }
                }
                3 => {
                    v_a_571_ = lean_ctor_get(v_x_525_, 0);
                    v_a_572_ = lean_ctor_get(v_x_525_, 1);
                    v_isSharedCheck_597_ = (!lean_is_exclusive(v_x_525_)) as u8;
                    if v_isSharedCheck_597_ == 0 {
                        v___x_574_ = v_x_525_;
                        v_isShared_575_ = v_isSharedCheck_597_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_572_);
                        lean_inc(v_a_571_);
                        lean_dec(v_x_525_);
                        v___x_574_ = lean_box(0);
                        v_isShared_575_ = v_isSharedCheck_597_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_a_598_ = lean_ctor_get(v_x_525_, 0);
                    v_a_599_ = lean_ctor_get(v_x_525_, 1);
                    v_isSharedCheck_624_ = (!lean_is_exclusive(v_x_525_)) as u8;
                    if v_isSharedCheck_624_ == 0 {
                        v___x_601_ = v_x_525_;
                        v_isShared_602_ = v_isSharedCheck_624_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_599_);
                        lean_inc(v_a_598_);
                        lean_dec(v_x_525_);
                        v___x_601_ = lean_box(0);
                        v_isShared_602_ = v_isSharedCheck_624_;
                        state = 8;
                        continue;
                    }
                }
                5 => {
                    v___x_625_ = lean_unsigned_to_nat(1024);
                    v___x_626_ = lean_nat_dec_le(v___x_625_, v_prec_526_);
                    if v___x_626_ == 0 {
                        v___x_627_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                        );
                        v___y_528_ = v___x_627_;
                        state = 1;
                        continue;
                    } else {
                        v___x_628_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                        );
                        v___y_528_ = v___x_628_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_a_629_ = lean_ctor_get(v_x_525_, 0);
                    lean_inc(v_a_629_);
                    v_a_630_ = lean_ctor_get(v_x_525_, 1);
                    lean_inc(v_a_630_);
                    v_a_631_ = lean_ctor_get(v_x_525_, 2);
                    lean_inc(v_a_631_);
                    lean_dec_ref_known(v_x_525_, 3);
                    v___x_651_ = lean_unsigned_to_nat(1024);
                    v___x_652_ = lean_nat_dec_le(v___x_651_, v_prec_526_);
                    if v___x_652_ == 0 {
                        v___x_653_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                        );
                        v___y_633_ = v___x_653_;
                        state = 11;
                        continue;
                    } else {
                        v___x_654_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                        );
                        v___y_633_ = v___x_654_;
                        state = 11;
                        continue;
                    }
                }
            },
            1 => {
                v___x_529_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__1;
                lean_inc(v___y_528_);
                v___x_530_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_530_, 0, v___y_528_);
                lean_ctor_set(v___x_530_, 1, v___x_529_);
                v___x_531_ = 0;
                v___x_532_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_532_, 0, v___x_530_);
                lean_ctor_set_uint8(
                    v___x_532_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_531_,
                );
                v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_526_);
                return v___x_533_;
            }
            2 => {
                v___x_536_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__3;
                lean_inc(v___y_535_);
                v___x_537_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_537_, 0, v___y_535_);
                lean_ctor_set(v___x_537_, 1, v___x_536_);
                v___x_538_ = 0;
                v___x_539_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_539_, 0, v___x_537_);
                lean_ctor_set_uint8(
                    v___x_539_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_538_,
                );
                v___x_540_ = l_Repr_addAppParen(v___x_539_, v_prec_526_);
                return v___x_540_;
            }
            3 => {
                v___x_543_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__5;
                lean_inc(v___y_542_);
                v___x_544_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_544_, 0, v___y_542_);
                lean_ctor_set(v___x_544_, 1, v___x_543_);
                v___x_545_ = 0;
                v___x_546_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_546_, 0, v___x_544_);
                lean_ctor_set_uint8(
                    v___x_546_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_545_,
                );
                v___x_547_ = l_Repr_addAppParen(v___x_546_, v_prec_526_);
                return v___x_547_;
            }
            4 => {
                v___x_559_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__10;
                v___x_560_ = lean_unsigned_to_nat(1024);
                v___x_561_ = l_Lean_instReprLiteral_repr(v_a_556_, v___x_560_);
                v___x_562_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_562_, 0, v___x_559_);
                lean_ctor_set(v___x_562_, 1, v___x_561_);
                lean_inc(v___y_558_);
                v___x_563_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_563_, 0, v___y_558_);
                lean_ctor_set(v___x_563_, 1, v___x_562_);
                v___x_564_ = 0;
                v___x_565_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_565_, 0, v___x_563_);
                lean_ctor_set_uint8(
                    v___x_565_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_564_,
                );
                v___x_566_ = l_Repr_addAppParen(v___x_565_, v_prec_526_);
                return v___x_566_;
            }
            5 => {
                v___x_593_ = lean_unsigned_to_nat(1024);
                v___x_594_ = lean_nat_dec_le(v___x_593_, v_prec_526_);
                if v___x_594_ == 0 {
                    v___x_595_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                        ),
                        _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                    );
                    v___y_577_ = v___x_595_;
                    state = 6;
                    continue;
                } else {
                    v___x_596_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                        ),
                        _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                    );
                    v___y_577_ = v___x_596_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_578_ = lean_box(1);
                v___x_579_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__13;
                v___x_580_ = lean_unsigned_to_nat(1024);
                v___x_581_ = l_Lean_Name_reprPrec(v_a_571_, v___x_580_);
                if v_isShared_575_ == 0 {
                    lean_ctor_set_tag(v___x_574_, 5);
                    lean_ctor_set(v___x_574_, 1, v___x_581_);
                    lean_ctor_set(v___x_574_, 0, v___x_579_);
                    v___x_583_ = v___x_574_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_592_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_579_);
                    lean_ctor_set(v_reuseFailAlloc_592_, 1, v___x_581_);
                    v___x_583_ = v_reuseFailAlloc_592_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_584_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_584_, 0, v___x_583_);
                lean_ctor_set(v___x_584_, 1, v___x_578_);
                v___x_585_ = l_Nat_reprFast(v_a_572_);
                v___x_586_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_586_, 0, v___x_585_);
                v___x_587_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_587_, 0, v___x_584_);
                lean_ctor_set(v___x_587_, 1, v___x_586_);
                lean_inc(v___y_577_);
                v___x_588_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_588_, 0, v___y_577_);
                lean_ctor_set(v___x_588_, 1, v___x_587_);
                v___x_589_ = 0;
                v___x_590_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_590_, 0, v___x_588_);
                lean_ctor_set_uint8(
                    v___x_590_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_589_,
                );
                v___x_591_ = l_Repr_addAppParen(v___x_590_, v_prec_526_);
                return v___x_591_;
            }
            8 => {
                v___x_620_ = lean_unsigned_to_nat(1024);
                v___x_621_ = lean_nat_dec_le(v___x_620_, v_prec_526_);
                if v___x_621_ == 0 {
                    v___x_622_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6_once
                        ),
                        _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__6,
                    );
                    v___y_604_ = v___x_622_;
                    state = 9;
                    continue;
                } else {
                    v___x_623_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7_once
                        ),
                        _init_l_Lean_Meta_DiscrTree_instReprKey_repr___closed__7,
                    );
                    v___y_604_ = v___x_623_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_605_ = lean_box(1);
                v___x_606_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__16;
                v___x_607_ = lean_unsigned_to_nat(1024);
                v___x_608_ = l_Lean_Name_reprPrec(v_a_598_, v___x_607_);
                if v_isShared_602_ == 0 {
                    lean_ctor_set_tag(v___x_601_, 5);
                    lean_ctor_set(v___x_601_, 1, v___x_608_);
                    lean_ctor_set(v___x_601_, 0, v___x_606_);
                    v___x_610_ = v___x_601_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_606_);
                    lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_619_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_611_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_611_, 0, v___x_610_);
                lean_ctor_set(v___x_611_, 1, v___x_605_);
                v___x_612_ = l_Nat_reprFast(v_a_599_);
                v___x_613_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_613_, 0, v___x_612_);
                v___x_614_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_614_, 0, v___x_611_);
                lean_ctor_set(v___x_614_, 1, v___x_613_);
                lean_inc(v___y_604_);
                v___x_615_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_615_, 0, v___y_604_);
                lean_ctor_set(v___x_615_, 1, v___x_614_);
                v___x_616_ = 0;
                v___x_617_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_617_, 0, v___x_615_);
                lean_ctor_set_uint8(
                    v___x_617_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_616_,
                );
                v___x_618_ = l_Repr_addAppParen(v___x_617_, v_prec_526_);
                return v___x_618_;
            }
            11 => {
                v___x_634_ = lean_box(1);
                v___x_635_ = l_Lean_Meta_DiscrTree_instReprKey_repr___closed__19;
                v___x_636_ = lean_unsigned_to_nat(1024);
                v___x_637_ = l_Lean_Name_reprPrec(v_a_629_, v___x_636_);
                v___x_638_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_638_, 0, v___x_635_);
                lean_ctor_set(v___x_638_, 1, v___x_637_);
                v___x_639_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_639_, 0, v___x_638_);
                lean_ctor_set(v___x_639_, 1, v___x_634_);
                v___x_640_ = l_Nat_reprFast(v_a_630_);
                v___x_641_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_641_, 0, v___x_640_);
                v___x_642_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_642_, 0, v___x_639_);
                lean_ctor_set(v___x_642_, 1, v___x_641_);
                v___x_643_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_643_, 0, v___x_642_);
                lean_ctor_set(v___x_643_, 1, v___x_634_);
                v___x_644_ = l_Nat_reprFast(v_a_631_);
                v___x_645_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_645_, 0, v___x_644_);
                v___x_646_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_646_, 0, v___x_643_);
                lean_ctor_set(v___x_646_, 1, v___x_645_);
                lean_inc(v___y_633_);
                v___x_647_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_647_, 0, v___y_633_);
                lean_ctor_set(v___x_647_, 1, v___x_646_);
                v___x_648_ = 0;
                v___x_649_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_649_, 0, v___x_647_);
                lean_ctor_set_uint8(
                    v___x_649_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_648_,
                );
                v___x_650_ = l_Repr_addAppParen(v___x_649_, v_prec_526_);
                return v___x_650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_instReprKey_repr___boxed(
    mut v_x_655_: *mut LeanObject,
    mut v_prec_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_657_: *mut LeanObject = core::ptr::null_mut();
    v_res_657_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_x_655_, v_prec_656_);
    lean_dec(v_prec_656_);
    return v_res_657_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0() -> u64 {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u64 = 0;
    v___x_660_ = lean_unsigned_to_nat(1723);
    v___x_661_ = lean_uint64_of_nat(v___x_660_);
    return v___x_661_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_hash(mut v_x_662_: *mut LeanObject) -> u64 {
    let mut v___x_663_: u64 = 0;
    let mut v___x_664_: u64 = 0;
    let mut v_a_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u64 = 0;
    let mut v___x_667_: u64 = 0;
    let mut v___x_668_: u64 = 0;
    let mut v_a_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: u64 = 0;
    let mut v___x_672_: u64 = 0;
    let mut v___x_673_: u64 = 0;
    let mut v___x_674_: u64 = 0;
    let mut v___x_675_: u64 = 0;
    let mut v_a_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u64 = 0;
    let mut v___y_680_: u64 = 0;
    let mut v___x_681_: u64 = 0;
    let mut v___x_682_: u64 = 0;
    let mut v___x_683_: u64 = 0;
    let mut v___x_684_: u64 = 0;
    let mut v_hash_685_: u64 = 0;
    let mut v___x_686_: u64 = 0;
    let mut v_a_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u64 = 0;
    let mut v___y_692_: u64 = 0;
    let mut v___x_693_: u64 = 0;
    let mut v___x_694_: u64 = 0;
    let mut v___x_695_: u64 = 0;
    let mut v___x_696_: u64 = 0;
    let mut v_hash_697_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_662_) {
                0 => {
                    v___x_663_ = 7883u64;
                    return v___x_663_;
                }
                1 => {
                    v___x_664_ = 2411u64;
                    return v___x_664_;
                }
                2 => {
                    v_a_665_ = lean_ctor_get(v_x_662_, 0);
                    v___x_666_ = 1879u64;
                    v___x_667_ = l_Lean_Literal_hash(v_a_665_);
                    v___x_668_ = lean_uint64_mix_hash(v___x_666_, v___x_667_);
                    return v___x_668_;
                }
                3 => {
                    v_a_669_ = lean_ctor_get(v_x_662_, 0);
                    v_a_670_ = lean_ctor_get(v_x_662_, 1);
                    v___x_671_ = 3541u64;
                    v___x_672_ = l_Lean_instHashableFVarId_hash(v_a_669_);
                    v___x_673_ = lean_uint64_of_nat(v_a_670_);
                    v___x_674_ = lean_uint64_mix_hash(v___x_672_, v___x_673_);
                    v___x_675_ = lean_uint64_mix_hash(v___x_671_, v___x_674_);
                    return v___x_675_;
                }
                4 => {
                    v_a_676_ = lean_ctor_get(v_x_662_, 0);
                    v_a_677_ = lean_ctor_get(v_x_662_, 1);
                    v___x_678_ = 5237u64;
                    if lean_obj_tag(v_a_676_) == 0 {
                        v___x_684_ = lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_Key_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_Key_hash___closed__0_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0,
                        );
                        v___y_680_ = v___x_684_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_685_ = lean_ctor_get_uint64(
                            v_a_676_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_680_ = v_hash_685_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v___x_686_ = 17u64;
                    return v___x_686_;
                }
                _ => {
                    v_a_687_ = lean_ctor_get(v_x_662_, 0);
                    v_a_688_ = lean_ctor_get(v_x_662_, 1);
                    v_a_689_ = lean_ctor_get(v_x_662_, 2);
                    v___x_690_ = lean_uint64_of_nat(v_a_689_);
                    if lean_obj_tag(v_a_687_) == 0 {
                        v___x_696_ = lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_Key_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_DiscrTree_Key_hash___closed__0_once
                            ),
                            _init_l_Lean_Meta_DiscrTree_Key_hash___closed__0,
                        );
                        v___y_692_ = v___x_696_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_697_ = lean_ctor_get_uint64(
                            v_a_687_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_692_ = v_hash_697_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_681_ = lean_uint64_of_nat(v_a_677_);
                v___x_682_ = lean_uint64_mix_hash(v___y_680_, v___x_681_);
                v___x_683_ = lean_uint64_mix_hash(v___x_678_, v___x_682_);
                return v___x_683_;
            }
            2 => {
                v___x_693_ = lean_uint64_of_nat(v_a_688_);
                v___x_694_ = lean_uint64_mix_hash(v___y_692_, v___x_693_);
                v___x_695_ = lean_uint64_mix_hash(v___x_690_, v___x_694_);
                return v___x_695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_hash___boxed(
    mut v_x_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_699_: u64 = 0;
    let mut v_r_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_698_);
    lean_dec(v_x_698_);
    v_r_700_ = lean_box_uint64(v_res_699_);
    return v_r_700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_DiscrTree_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_DiscrTree_instInhabitedKey_default =
        _init_l_Lean_Meta_DiscrTree_instInhabitedKey_default();
    lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedKey_default);
    l_Lean_Meta_DiscrTree_instInhabitedKey = _init_l_Lean_Meta_DiscrTree_instInhabitedKey();
    lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedKey);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_DiscrTree_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_DiscrTree_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_DiscrTree_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_DiscrTree_Types(builtin);
}
