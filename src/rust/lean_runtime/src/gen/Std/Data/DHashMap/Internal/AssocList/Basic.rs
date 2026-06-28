// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Basic
// Imports: Init.NotationExtra
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value: LeanClosureObject<
    0,
> = LeanClosureObject {
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
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value:
    LeanStringObject<43> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116,
        101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105,
        99, 0,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value:
    LeanStringObject<41> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 67, 97, 115, 116, 33,
        0,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value:
    LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32,
        105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value: LeanStringObject<
    37,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value:
    LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97,
        108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 75, 101, 121, 33, 0,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(
    mut v_x_1014_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1014_) == 0 {
        let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
        v___x_1015_ = lean_unsigned_to_nat(0);
        return v___x_1015_;
    } else {
        let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
        v___x_1016_ = lean_unsigned_to_nat(1);
        return v___x_1016_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg___boxed(
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1017_);
    lean_dec(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx(
    mut v_00_u03b1_1019_: *mut LeanObject,
    mut v_00_u03b2_1020_: *mut LeanObject,
    mut v_x_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1022_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___boxed(
    mut v_00_u03b1_1023_: *mut LeanObject,
    mut v_00_u03b2_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1026_: *mut LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Std_DHashMap_Internal_AssocList_ctorIdx(v_00_u03b1_1023_, v_00_u03b2_1024_, v_x_1025_);
    lean_dec(v_x_1025_);
    return v_res_1026_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(
    mut v_t_1027_: *mut LeanObject,
    mut v_k_1028_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1027_) == 0 {
        return v_k_1028_;
    } else {
        let mut v_key_1029_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1030_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
        v_key_1029_ = lean_ctor_get(v_t_1027_, 0);
        lean_inc(v_key_1029_);
        v_value_1030_ = lean_ctor_get(v_t_1027_, 1);
        lean_inc(v_value_1030_);
        v_tail_1031_ = lean_ctor_get(v_t_1027_, 2);
        lean_inc(v_tail_1031_);
        lean_dec_ref_known(v_t_1027_, 3);
        v___x_1032_ = lean_apply_3(v_k_1028_, v_key_1029_, v_value_1030_, v_tail_1031_);
        return v___x_1032_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_00_u03b2_1034_: *mut LeanObject,
    mut v_motive_1035_: *mut LeanObject,
    mut v_ctorIdx_1036_: *mut LeanObject,
    mut v_t_1037_: *mut LeanObject,
    mut v_h_1038_: *mut LeanObject,
    mut v_k_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1037_, v_k_1039_);
    return v___x_1040_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___boxed(
    mut v_00_u03b1_1041_: *mut LeanObject,
    mut v_00_u03b2_1042_: *mut LeanObject,
    mut v_motive_1043_: *mut LeanObject,
    mut v_ctorIdx_1044_: *mut LeanObject,
    mut v_t_1045_: *mut LeanObject,
    mut v_h_1046_: *mut LeanObject,
    mut v_k_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1048_: *mut LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_DHashMap_Internal_AssocList_ctorElim(
        v_00_u03b1_1041_,
        v_00_u03b2_1042_,
        v_motive_1043_,
        v_ctorIdx_1044_,
        v_t_1045_,
        v_h_1046_,
        v_k_1047_,
    );
    lean_dec(v_ctorIdx_1044_);
    return v_res_1048_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim___redArg(
    mut v_t_1049_: *mut LeanObject,
    mut v_nil_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1049_, v_nil_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim(
    mut v_00_u03b1_1052_: *mut LeanObject,
    mut v_00_u03b2_1053_: *mut LeanObject,
    mut v_motive_1054_: *mut LeanObject,
    mut v_t_1055_: *mut LeanObject,
    mut v_h_1056_: *mut LeanObject,
    mut v_nil_1057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1055_, v_nil_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim___redArg(
    mut v_t_1059_: *mut LeanObject,
    mut v_cons_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1059_, v_cons_1060_);
    return v___x_1061_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim(
    mut v_00_u03b1_1062_: *mut LeanObject,
    mut v_00_u03b2_1063_: *mut LeanObject,
    mut v_motive_1064_: *mut LeanObject,
    mut v_t_1065_: *mut LeanObject,
    mut v_h_1066_: *mut LeanObject,
    mut v_cons_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1065_, v_cons_1067_);
    return v___x_1068_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList_default(
    mut v_00_u03b1_1069_: *mut LeanObject,
    mut v_00_u03b2_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = lean_box(0);
    return v___x_1071_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList(
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___x_1074_ = lean_box(0);
    return v___x_1074_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
    mut v_inst_1075_: *mut LeanObject,
    mut v_f_1076_: *mut LeanObject,
    mut v_x_1077_: *mut LeanObject,
    mut v_x_1078_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1078_) == 0 {
        let mut v_toApplicative_1079_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1079_ = lean_ctor_get(v_inst_1075_, 0);
        lean_inc_ref(v_toApplicative_1079_);
        lean_dec(v_f_1076_);
        lean_dec_ref(v_inst_1075_);
        v_toPure_1080_ = lean_ctor_get(v_toApplicative_1079_, 1);
        lean_inc(v_toPure_1080_);
        lean_dec_ref(v_toApplicative_1079_);
        v___x_1081_ = lean_apply_2(v_toPure_1080_, lean_box(0), v_x_1077_);
        return v___x_1081_;
    } else {
        let mut v_toBind_1082_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_1083_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1084_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1082_ = lean_ctor_get(v_inst_1075_, 1);
        lean_inc(v_toBind_1082_);
        v_key_1083_ = lean_ctor_get(v_x_1078_, 0);
        lean_inc(v_key_1083_);
        v_value_1084_ = lean_ctor_get(v_x_1078_, 1);
        lean_inc(v_value_1084_);
        v_tail_1085_ = lean_ctor_get(v_x_1078_, 2);
        lean_inc(v_tail_1085_);
        lean_dec_ref_known(v_x_1078_, 3);
        lean_inc(v_f_1076_);
        v___f_1086_ = lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1086_, 0, v_inst_1075_);
        lean_closure_set(v___f_1086_, 1, v_f_1076_);
        lean_closure_set(v___f_1086_, 2, v_tail_1085_);
        v___x_1087_ = lean_apply_3(v_f_1076_, v_x_1077_, v_key_1083_, v_value_1084_);
        v___x_1088_ = lean_apply_4(
            v_toBind_1082_,
            lean_box(0),
            lean_box(0),
            v___x_1087_,
            v___f_1086_,
        );
        return v___x_1088_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0(
    mut v_inst_1089_: *mut LeanObject,
    mut v_f_1090_: *mut LeanObject,
    mut v_tail_1091_: *mut LeanObject,
    mut v_d_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    v___x_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1089_,
        v_f_1090_,
        v_d_1092_,
        v_tail_1091_,
    );
    return v___x_1093_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM(
    mut v_00_u03b1_1094_: *mut LeanObject,
    mut v_00_u03b2_1095_: *mut LeanObject,
    mut v_00_u03b4_1096_: *mut LeanObject,
    mut v_m_1097_: *mut LeanObject,
    mut v_inst_1098_: *mut LeanObject,
    mut v_f_1099_: *mut LeanObject,
    mut v_x_1100_: *mut LeanObject,
    mut v_x_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1102_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1098_,
        v_f_1099_,
        v_x_1100_,
        v_x_1101_,
    );
    return v___x_1102_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0(
    mut v_f_1103_: *mut LeanObject,
    mut v_x1_1104_: *mut LeanObject,
    mut v_x2_1105_: *mut LeanObject,
    mut v_x3_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = lean_apply_3(v_f_1103_, v_x1_1104_, v_x2_1105_, v_x3_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg(
    mut v_f_1127_: *mut LeanObject,
    mut v_init_1128_: *mut LeanObject,
    mut v_as_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___f_1130_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1130_, 0, v_f_1127_);
    v___x_1131_ = l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9;
    v___x_1132_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1131_,
        v___f_1130_,
        v_init_1128_,
        v_as_1129_,
    );
    return v___x_1132_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl(
    mut v_00_u03b1_1133_: *mut LeanObject,
    mut v_00_u03b2_1134_: *mut LeanObject,
    mut v_00_u03b4_1135_: *mut LeanObject,
    mut v_f_1136_: *mut LeanObject,
    mut v_init_1137_: *mut LeanObject,
    mut v_as_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    v___f_1139_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1139_, 0, v_f_1136_);
    v___x_1140_ = l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9;
    v___x_1141_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1140_,
        v___f_1139_,
        v_init_1137_,
        v_as_1138_,
    );
    return v___x_1141_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___redArg___lam__0(
    mut v_f_1142_: *mut LeanObject,
    mut v_key_1143_: *mut LeanObject,
    mut v_value_1144_: *mut LeanObject,
    mut v_d_1145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1146_ = lean_apply_3(v_f_1142_, v_key_1143_, v_value_1144_, v_d_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
    mut v_inst_1147_: *mut LeanObject,
    mut v_f_1148_: *mut LeanObject,
    mut v_x_1149_: *mut LeanObject,
    mut v_x_1150_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1150_) == 0 {
        let mut v_toApplicative_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1151_ = lean_ctor_get(v_inst_1147_, 0);
        lean_inc_ref(v_toApplicative_1151_);
        lean_dec(v_f_1148_);
        lean_dec_ref(v_inst_1147_);
        v_toPure_1152_ = lean_ctor_get(v_toApplicative_1151_, 1);
        lean_inc(v_toPure_1152_);
        lean_dec_ref(v_toApplicative_1151_);
        v___x_1153_ = lean_apply_2(v_toPure_1152_, lean_box(0), v_x_1149_);
        return v___x_1153_;
    } else {
        let mut v_toBind_1154_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_1155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1156_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1154_ = lean_ctor_get(v_inst_1147_, 1);
        lean_inc(v_toBind_1154_);
        v_key_1155_ = lean_ctor_get(v_x_1150_, 0);
        lean_inc(v_key_1155_);
        v_value_1156_ = lean_ctor_get(v_x_1150_, 1);
        lean_inc(v_value_1156_);
        v_tail_1157_ = lean_ctor_get(v_x_1150_, 2);
        lean_inc(v_tail_1157_);
        lean_dec_ref_known(v_x_1150_, 3);
        lean_inc(v_f_1148_);
        v___f_1158_ = lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1158_, 0, v_f_1148_);
        lean_closure_set(v___f_1158_, 1, v_key_1155_);
        lean_closure_set(v___f_1158_, 2, v_value_1156_);
        v___x_1159_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
            v_inst_1147_,
            v_f_1148_,
            v_x_1149_,
            v_tail_1157_,
        );
        v___x_1160_ = lean_apply_4(
            v_toBind_1154_,
            lean_box(0),
            lean_box(0),
            v___x_1159_,
            v___f_1158_,
        );
        return v___x_1160_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM(
    mut v_00_u03b1_1161_: *mut LeanObject,
    mut v_00_u03b2_1162_: *mut LeanObject,
    mut v_00_u03b4_1163_: *mut LeanObject,
    mut v_m_1164_: *mut LeanObject,
    mut v_inst_1165_: *mut LeanObject,
    mut v_f_1166_: *mut LeanObject,
    mut v_x_1167_: *mut LeanObject,
    mut v_x_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v_inst_1165_,
        v_f_1166_,
        v_x_1167_,
        v_x_1168_,
    );
    return v___x_1169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldr___redArg(
    mut v_f_1170_: *mut LeanObject,
    mut v_init_1171_: *mut LeanObject,
    mut v_as_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___f_1173_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1173_, 0, v_f_1170_);
    v___x_1174_ = l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9;
    v___x_1175_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1174_,
        v___f_1173_,
        v_init_1171_,
        v_as_1172_,
    );
    return v___x_1175_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldr(
    mut v_00_u03b1_1176_: *mut LeanObject,
    mut v_00_u03b2_1177_: *mut LeanObject,
    mut v_00_u03b4_1178_: *mut LeanObject,
    mut v_f_1179_: *mut LeanObject,
    mut v_init_1180_: *mut LeanObject,
    mut v_as_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___f_1182_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1182_, 0, v_f_1179_);
    v___x_1183_ = l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9;
    v___x_1184_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1183_,
        v___f_1182_,
        v_init_1180_,
        v_as_1181_,
    );
    return v___x_1184_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0(
    mut v_f_1185_: *mut LeanObject,
    mut v_x_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    v___x_1189_ = lean_apply_2(v_f_1185_, v___y_1187_, v___y_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM___redArg(
    mut v_inst_1190_: *mut LeanObject,
    mut v_f_1191_: *mut LeanObject,
    mut v_as_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    v___f_1193_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1193_, 0, v_f_1191_);
    v___x_1194_ = lean_box(0);
    v___x_1195_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1190_,
        v___f_1193_,
        v___x_1194_,
        v_as_1192_,
    );
    return v___x_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM(
    mut v_00_u03b1_1196_: *mut LeanObject,
    mut v_00_u03b2_1197_: *mut LeanObject,
    mut v_m_1198_: *mut LeanObject,
    mut v_inst_1199_: *mut LeanObject,
    mut v_f_1200_: *mut LeanObject,
    mut v_as_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    v___f_1202_ = lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1202_, 0, v_f_1200_);
    v___x_1203_ = lean_box(0);
    v___x_1204_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1199_,
        v___f_1202_,
        v___x_1203_,
        v_as_1201_,
    );
    return v___x_1204_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(
    mut v_inst_1205_: *mut LeanObject,
    mut v_f_1206_: *mut LeanObject,
    mut v_a_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_1207_) == 0 {
        let mut v_toApplicative_1209_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1209_ = lean_ctor_get(v_inst_1205_, 0);
        lean_inc_ref(v_toApplicative_1209_);
        lean_dec(v_f_1206_);
        lean_dec_ref(v_inst_1205_);
        v_toPure_1210_ = lean_ctor_get(v_toApplicative_1209_, 1);
        lean_inc(v_toPure_1210_);
        lean_dec_ref(v_toApplicative_1209_);
        v___x_1211_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1211_, 0, v_a_1208_);
        v___x_1212_ = lean_apply_2(v_toPure_1210_, lean_box(0), v___x_1211_);
        return v___x_1212_;
    } else {
        let mut v_toApplicative_1213_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_1214_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1215_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1213_ = lean_ctor_get(v_inst_1205_, 0);
        v_toBind_1214_ = lean_ctor_get(v_inst_1205_, 1);
        lean_inc(v_toBind_1214_);
        v_toPure_1215_ = lean_ctor_get(v_toApplicative_1213_, 1);
        lean_inc(v_toPure_1215_);
        v_key_1216_ = lean_ctor_get(v_a_1207_, 0);
        lean_inc(v_key_1216_);
        v_value_1217_ = lean_ctor_get(v_a_1207_, 1);
        lean_inc(v_value_1217_);
        v_tail_1218_ = lean_ctor_get(v_a_1207_, 2);
        lean_inc(v_tail_1218_);
        lean_dec_ref_known(v_a_1207_, 3);
        lean_inc(v_f_1206_);
        v___f_1219_ = lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0 as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___f_1219_, 0, v_toPure_1215_);
        lean_closure_set(v___f_1219_, 1, v_inst_1205_);
        lean_closure_set(v___f_1219_, 2, v_f_1206_);
        lean_closure_set(v___f_1219_, 3, v_tail_1218_);
        v___x_1220_ = lean_apply_3(v_f_1206_, v_key_1216_, v_value_1217_, v_a_1208_);
        v___x_1221_ = lean_apply_4(
            v_toBind_1214_,
            lean_box(0),
            lean_box(0),
            v___x_1220_,
            v___f_1219_,
        );
        return v___x_1221_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0(
    mut v_toPure_1222_: *mut LeanObject,
    mut v_inst_1223_: *mut LeanObject,
    mut v_f_1224_: *mut LeanObject,
    mut v_tail_1225_: *mut LeanObject,
    mut v_____do__lift_1226_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1226_) == 0 {
        let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_1225_);
        lean_dec(v_f_1224_);
        lean_dec_ref(v_inst_1223_);
        v___x_1227_ = lean_apply_2(v_toPure_1222_, lean_box(0), v_____do__lift_1226_);
        return v___x_1227_;
    } else {
        let mut v_a_1228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1222_);
        v_a_1228_ = lean_ctor_get(v_____do__lift_1226_, 0);
        lean_inc(v_a_1228_);
        lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1229_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1223_, v_f_1224_, v_tail_1225_, v_a_1228_);
        return v___x_1229_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(
    mut v_00_u03b1_1230_: *mut LeanObject,
    mut v_00_u03b2_1231_: *mut LeanObject,
    mut v_00_u03b4_1232_: *mut LeanObject,
    mut v_m_1233_: *mut LeanObject,
    mut v_inst_1234_: *mut LeanObject,
    mut v_f_1235_: *mut LeanObject,
    mut v_a_1236_: *mut LeanObject,
    mut v_a_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1238_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1234_, v_f_1235_, v_a_1236_, v_a_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep___redArg(
    mut v_inst_1239_: *mut LeanObject,
    mut v_as_1240_: *mut LeanObject,
    mut v_init_1241_: *mut LeanObject,
    mut v_f_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    v___x_1243_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1239_, v_f_1242_, v_as_1240_, v_init_1241_);
    return v___x_1243_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep(
    mut v_00_u03b1_1244_: *mut LeanObject,
    mut v_00_u03b2_1245_: *mut LeanObject,
    mut v_00_u03b4_1246_: *mut LeanObject,
    mut v_m_1247_: *mut LeanObject,
    mut v_inst_1248_: *mut LeanObject,
    mut v_as_1249_: *mut LeanObject,
    mut v_init_1250_: *mut LeanObject,
    mut v_f_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1248_, v_f_1251_, v_as_1249_, v_init_1250_);
    return v___x_1252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg(
    mut v_x_1253_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1253_) == 0 {
        let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
        v___x_1254_ = lean_box(0);
        return v___x_1254_;
    } else {
        let mut v_key_1255_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1256_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
        v_key_1255_ = lean_ctor_get(v_x_1253_, 0);
        v_value_1256_ = lean_ctor_get(v_x_1253_, 1);
        v_tail_1257_ = lean_ctor_get(v_x_1253_, 2);
        lean_inc(v_value_1256_);
        lean_inc(v_key_1255_);
        v___x_1258_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1258_, 0, v_key_1255_);
        lean_ctor_set(v___x_1258_, 1, v_value_1256_);
        v___x_1259_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_tail_1257_);
        v___x_1260_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1260_, 0, v___x_1258_);
        lean_ctor_set(v___x_1260_, 1, v___x_1259_);
        return v___x_1260_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg___boxed(
    mut v_x_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v_res_1262_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1261_);
    lean_dec(v_x_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList(
    mut v_00_u03b1_1263_: *mut LeanObject,
    mut v_00_u03b2_1264_: *mut LeanObject,
    mut v_x_1265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___boxed(
    mut v_00_u03b1_1267_: *mut LeanObject,
    mut v_00_u03b2_1268_: *mut LeanObject,
    mut v_x_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ =
        l_Std_DHashMap_Internal_AssocList_toList(v_00_u03b1_1267_, v_00_u03b2_1268_, v_x_1269_);
    lean_dec(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(
    mut v_x_1271_: *mut LeanObject,
    mut v_x_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tail_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1272_) == 0 {
                    return v_x_1271_;
                } else {
                    v_tail_1273_ = lean_ctor_get(v_x_1272_, 2);
                    v___x_1274_ = lean_unsigned_to_nat(1);
                    v___x_1275_ = lean_nat_add(v_x_1271_, v___x_1274_);
                    lean_dec(v_x_1271_);
                    v_x_1271_ = v___x_1275_;
                    v_x_1272_ = v_tail_1273_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg___boxed(
    mut v_x_1277_: *mut LeanObject,
    mut v_x_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1279_: *mut LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1277_, v_x_1278_);
    lean_dec(v_x_1278_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg(
    mut v_l_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = lean_unsigned_to_nat(0);
    v___x_1282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v___x_1281_, v_l_1280_);
    return v___x_1282_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg___boxed(
    mut v_l_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1284_: *mut LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1283_);
    lean_dec(v_l_1283_);
    return v_res_1284_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length(
    mut v_00_u03b1_1285_: *mut LeanObject,
    mut v_00_u03b2_1286_: *mut LeanObject,
    mut v_l_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___boxed(
    mut v_00_u03b1_1289_: *mut LeanObject,
    mut v_00_u03b2_1290_: *mut LeanObject,
    mut v_l_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_res_1292_ =
        l_Std_DHashMap_Internal_AssocList_length(v_00_u03b1_1289_, v_00_u03b2_1290_, v_l_1291_);
    lean_dec(v_l_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(
    mut v_00_u03b1_1293_: *mut LeanObject,
    mut v_00_u03b2_1294_: *mut LeanObject,
    mut v_x_1295_: *mut LeanObject,
    mut v_x_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1295_, v_x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___boxed(
    mut v_00_u03b1_1298_: *mut LeanObject,
    mut v_00_u03b2_1299_: *mut LeanObject,
    mut v_x_1300_: *mut LeanObject,
    mut v_x_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(v_00_u03b1_1298_, v_00_u03b2_1299_, v_x_1300_, v_x_1301_);
    lean_dec(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
    mut v_inst_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_x_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1305_) == 0 {
                    lean_dec(v_a_1304_);
                    lean_dec_ref(v_inst_1303_);
                    v___x_1306_ = lean_box(0);
                    return v___x_1306_;
                } else {
                    v_key_1307_ = lean_ctor_get(v_x_1305_, 0);
                    lean_inc(v_key_1307_);
                    v_value_1308_ = lean_ctor_get(v_x_1305_, 1);
                    lean_inc(v_value_1308_);
                    v_tail_1309_ = lean_ctor_get(v_x_1305_, 2);
                    lean_inc(v_tail_1309_);
                    lean_dec_ref_known(v_x_1305_, 3);
                    lean_inc_ref(v_inst_1303_);
                    lean_inc(v_a_1304_);
                    v___x_1310_ = lean_apply_2(v_inst_1303_, v_key_1307_, v_a_1304_);
                    v___x_1311_ = (lean_unbox(v___x_1310_) as u8);
                    if v___x_1311_ == 0 {
                        lean_dec(v_value_1308_);
                        v_x_1305_ = v_tail_1309_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1309_);
                        lean_dec(v_a_1304_);
                        lean_dec_ref(v_inst_1303_);
                        v___x_1313_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1313_, 0, v_value_1308_);
                        return v___x_1313_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f(
    mut v_00_u03b1_1314_: *mut LeanObject,
    mut v_00_u03b2_1315_: *mut LeanObject,
    mut v_inst_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_x_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1316_, v_a_1317_, v_x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
    mut v_inst_1320_: *mut LeanObject,
    mut v_a_1321_: *mut LeanObject,
    mut v_x_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1322_) == 0 {
                    lean_dec(v_a_1321_);
                    lean_dec_ref(v_inst_1320_);
                    v___x_1323_ = lean_box(0);
                    return v___x_1323_;
                } else {
                    v_key_1324_ = lean_ctor_get(v_x_1322_, 0);
                    lean_inc(v_key_1324_);
                    v_value_1325_ = lean_ctor_get(v_x_1322_, 1);
                    lean_inc(v_value_1325_);
                    v_tail_1326_ = lean_ctor_get(v_x_1322_, 2);
                    lean_inc(v_tail_1326_);
                    lean_dec_ref_known(v_x_1322_, 3);
                    lean_inc_ref(v_inst_1320_);
                    lean_inc(v_a_1321_);
                    v___x_1327_ = lean_apply_2(v_inst_1320_, v_key_1324_, v_a_1321_);
                    v___x_1328_ = (lean_unbox(v___x_1327_) as u8);
                    if v___x_1328_ == 0 {
                        lean_dec(v_value_1325_);
                        v_x_1322_ = v_tail_1326_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1326_);
                        lean_dec(v_a_1321_);
                        lean_dec_ref(v_inst_1320_);
                        v___x_1330_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1330_, 0, v_value_1325_);
                        return v___x_1330_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f(
    mut v_00_u03b1_1331_: *mut LeanObject,
    mut v_00_u03b2_1332_: *mut LeanObject,
    mut v_inst_1333_: *mut LeanObject,
    mut v_inst_1334_: *mut LeanObject,
    mut v_a_1335_: *mut LeanObject,
    mut v_x_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ =
        l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_1333_, v_a_1335_, v_x_1336_);
    return v___x_1337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
    mut v_inst_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_x_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1340_) == 0 {
                    lean_dec(v_a_1339_);
                    lean_dec_ref(v_inst_1338_);
                    v___x_1341_ = lean_box(0);
                    return v___x_1341_;
                } else {
                    v_key_1342_ = lean_ctor_get(v_x_1340_, 0);
                    lean_inc_n(v_key_1342_, 2);
                    v_value_1343_ = lean_ctor_get(v_x_1340_, 1);
                    lean_inc(v_value_1343_);
                    v_tail_1344_ = lean_ctor_get(v_x_1340_, 2);
                    lean_inc(v_tail_1344_);
                    lean_dec_ref_known(v_x_1340_, 3);
                    lean_inc_ref(v_inst_1338_);
                    lean_inc(v_a_1339_);
                    v___x_1345_ = lean_apply_2(v_inst_1338_, v_key_1342_, v_a_1339_);
                    v___x_1346_ = (lean_unbox(v___x_1345_) as u8);
                    if v___x_1346_ == 0 {
                        lean_dec(v_value_1343_);
                        lean_dec(v_key_1342_);
                        v_x_1340_ = v_tail_1344_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1344_);
                        lean_dec(v_a_1339_);
                        lean_dec_ref(v_inst_1338_);
                        v___x_1348_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1348_, 0, v_key_1342_);
                        lean_ctor_set(v___x_1348_, 1, v_value_1343_);
                        v___x_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                        return v___x_1349_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f(
    mut v_00_u03b1_1350_: *mut LeanObject,
    mut v_00_u03b2_1351_: *mut LeanObject,
    mut v_inst_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
    mut v_x_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ =
        l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_1352_, v_a_1353_, v_x_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg(
    mut v_inst_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_x_1358_: *mut LeanObject,
) -> u8 {
    let mut v___x_1359_: u8 = 0;
    let mut v_key_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1358_) == 0 {
                    lean_dec(v_a_1357_);
                    lean_dec_ref(v_inst_1356_);
                    v___x_1359_ = 0;
                    return v___x_1359_;
                } else {
                    v_key_1360_ = lean_ctor_get(v_x_1358_, 0);
                    lean_inc(v_key_1360_);
                    v_tail_1361_ = lean_ctor_get(v_x_1358_, 2);
                    lean_inc(v_tail_1361_);
                    lean_dec_ref_known(v_x_1358_, 3);
                    lean_inc_ref(v_inst_1356_);
                    lean_inc(v_a_1357_);
                    v___x_1362_ = lean_apply_2(v_inst_1356_, v_key_1360_, v_a_1357_);
                    v___x_1363_ = (lean_unbox(v___x_1362_) as u8);
                    if v___x_1363_ == 0 {
                        v_x_1358_ = v_tail_1361_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1361_);
                        lean_dec(v_a_1357_);
                        lean_dec_ref(v_inst_1356_);
                        v___x_1365_ = (lean_unbox(v___x_1362_) as u8);
                        return v___x_1365_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg___boxed(
    mut v_inst_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
    mut v_x_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1369_: u8 = 0;
    let mut v_r_1370_: *mut LeanObject = core::ptr::null_mut();
    v_res_1369_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1366_, v_a_1367_, v_x_1368_);
    v_r_1370_ = lean_box((v_res_1369_) as usize);
    return v_r_1370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains(
    mut v_00_u03b1_1371_: *mut LeanObject,
    mut v_00_u03b2_1372_: *mut LeanObject,
    mut v_inst_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
    mut v_x_1375_: *mut LeanObject,
) -> u8 {
    let mut v___x_1376_: u8 = 0;
    v___x_1376_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1373_, v_a_1374_, v_x_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___boxed(
    mut v_00_u03b1_1377_: *mut LeanObject,
    mut v_00_u03b2_1378_: *mut LeanObject,
    mut v_inst_1379_: *mut LeanObject,
    mut v_a_1380_: *mut LeanObject,
    mut v_x_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Std_DHashMap_Internal_AssocList_contains(
        v_00_u03b1_1377_,
        v_00_u03b2_1378_,
        v_inst_1379_,
        v_a_1380_,
        v_x_1381_,
    );
    v_r_1383_ = lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_1384_: *mut LeanObject,
    mut v_h__1_1385_: *mut LeanObject,
    mut v_h__2_1386_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1384_) == 0 {
        let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1386_);
        v___x_1387_ = lean_box(0);
        v___x_1388_ = lean_apply_1(v_h__1_1385_, v___x_1387_);
        return v___x_1388_;
    } else {
        let mut v_key_1389_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1390_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1385_);
        v_key_1389_ = lean_ctor_get(v_x_1384_, 0);
        lean_inc(v_key_1389_);
        v_value_1390_ = lean_ctor_get(v_x_1384_, 1);
        lean_inc(v_value_1390_);
        v_tail_1391_ = lean_ctor_get(v_x_1384_, 2);
        lean_inc(v_tail_1391_);
        lean_dec_ref_known(v_x_1384_, 3);
        v___x_1392_ = lean_apply_3(v_h__2_1386_, v_key_1389_, v_value_1390_, v_tail_1391_);
        return v___x_1392_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_1393_: *mut LeanObject,
    mut v_00_u03b2_1394_: *mut LeanObject,
    mut v_motive_1395_: *mut LeanObject,
    mut v_x_1396_: *mut LeanObject,
    mut v_h__1_1397_: *mut LeanObject,
    mut v_h__2_1398_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1396_) == 0 {
        let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1398_);
        v___x_1399_ = lean_box(0);
        v___x_1400_ = lean_apply_1(v_h__1_1397_, v___x_1399_);
        return v___x_1400_;
    } else {
        let mut v_key_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1397_);
        v_key_1401_ = lean_ctor_get(v_x_1396_, 0);
        lean_inc(v_key_1401_);
        v_value_1402_ = lean_ctor_get(v_x_1396_, 1);
        lean_inc(v_value_1402_);
        v_tail_1403_ = lean_ctor_get(v_x_1396_, 2);
        lean_inc(v_tail_1403_);
        lean_dec_ref_known(v_x_1396_, 3);
        v___x_1404_ = lean_apply_3(v_h__2_1398_, v_key_1401_, v_value_1402_, v_tail_1403_);
        return v___x_1404_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___redArg(
    mut v_inst_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_x_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1408_ = lean_ctor_get(v_x_1407_, 0);
                lean_inc(v_key_1408_);
                v_value_1409_ = lean_ctor_get(v_x_1407_, 1);
                lean_inc(v_value_1409_);
                v_tail_1410_ = lean_ctor_get(v_x_1407_, 2);
                lean_inc(v_tail_1410_);
                lean_dec(v_x_1407_);
                lean_inc_ref(v_inst_1405_);
                lean_inc(v_a_1406_);
                v___x_1411_ = lean_apply_2(v_inst_1405_, v_key_1408_, v_a_1406_);
                v___x_1412_ = (lean_unbox(v___x_1411_) as u8);
                if v___x_1412_ == 0 {
                    lean_dec(v_value_1409_);
                    v_x_1407_ = v_tail_1410_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_1410_);
                    lean_dec(v_a_1406_);
                    lean_dec_ref(v_inst_1405_);
                    return v_value_1409_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get(
    mut v_00_u03b1_1414_: *mut LeanObject,
    mut v_00_u03b2_1415_: *mut LeanObject,
    mut v_inst_1416_: *mut LeanObject,
    mut v_a_1417_: *mut LeanObject,
    mut v_x_1418_: *mut LeanObject,
    mut v_x_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1416_, v_a_1417_, v_x_1418_);
    return v___x_1420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast___redArg(
    mut v_inst_1421_: *mut LeanObject,
    mut v_a_1422_: *mut LeanObject,
    mut v_x_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1424_ = lean_ctor_get(v_x_1423_, 0);
                lean_inc(v_key_1424_);
                v_value_1425_ = lean_ctor_get(v_x_1423_, 1);
                lean_inc(v_value_1425_);
                v_tail_1426_ = lean_ctor_get(v_x_1423_, 2);
                lean_inc(v_tail_1426_);
                lean_dec(v_x_1423_);
                lean_inc_ref(v_inst_1421_);
                lean_inc(v_a_1422_);
                v___x_1427_ = lean_apply_2(v_inst_1421_, v_key_1424_, v_a_1422_);
                v___x_1428_ = (lean_unbox(v___x_1427_) as u8);
                if v___x_1428_ == 0 {
                    lean_dec(v_value_1425_);
                    v_x_1423_ = v_tail_1426_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_1426_);
                    lean_dec(v_a_1422_);
                    lean_dec_ref(v_inst_1421_);
                    return v_value_1425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast(
    mut v_00_u03b1_1430_: *mut LeanObject,
    mut v_00_u03b2_1431_: *mut LeanObject,
    mut v_inst_1432_: *mut LeanObject,
    mut v_inst_1433_: *mut LeanObject,
    mut v_a_1434_: *mut LeanObject,
    mut v_x_1435_: *mut LeanObject,
    mut v_x_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1432_, v_a_1434_, v_x_1435_);
    return v___x_1437_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry___redArg(
    mut v_inst_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_x_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1441_ = lean_ctor_get(v_x_1440_, 0);
                lean_inc_n(v_key_1441_, 2);
                v_value_1442_ = lean_ctor_get(v_x_1440_, 1);
                lean_inc(v_value_1442_);
                v_tail_1443_ = lean_ctor_get(v_x_1440_, 2);
                lean_inc(v_tail_1443_);
                lean_dec(v_x_1440_);
                lean_inc_ref(v_inst_1438_);
                lean_inc(v_a_1439_);
                v___x_1444_ = lean_apply_2(v_inst_1438_, v_key_1441_, v_a_1439_);
                v___x_1445_ = (lean_unbox(v___x_1444_) as u8);
                if v___x_1445_ == 0 {
                    lean_dec(v_value_1442_);
                    lean_dec(v_key_1441_);
                    v_x_1440_ = v_tail_1443_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_1443_);
                    lean_dec(v_a_1439_);
                    lean_dec_ref(v_inst_1438_);
                    v___x_1447_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1447_, 0, v_key_1441_);
                    lean_ctor_set(v___x_1447_, 1, v_value_1442_);
                    return v___x_1447_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry(
    mut v_00_u03b1_1448_: *mut LeanObject,
    mut v_00_u03b2_1449_: *mut LeanObject,
    mut v_inst_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
    mut v_x_1452_: *mut LeanObject,
    mut v_x_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1450_, v_a_1451_, v_x_1452_);
    return v___x_1454_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
    mut v_inst_1455_: *mut LeanObject,
    mut v_a_1456_: *mut LeanObject,
    mut v_fallback_1457_: *mut LeanObject,
    mut v_x_1458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1458_) == 0 {
                    lean_dec(v_a_1456_);
                    lean_dec_ref(v_inst_1455_);
                    lean_inc_ref(v_fallback_1457_);
                    return v_fallback_1457_;
                } else {
                    v_key_1459_ = lean_ctor_get(v_x_1458_, 0);
                    lean_inc_n(v_key_1459_, 2);
                    v_value_1460_ = lean_ctor_get(v_x_1458_, 1);
                    lean_inc(v_value_1460_);
                    v_tail_1461_ = lean_ctor_get(v_x_1458_, 2);
                    lean_inc(v_tail_1461_);
                    lean_dec_ref_known(v_x_1458_, 3);
                    lean_inc_ref(v_inst_1455_);
                    lean_inc(v_a_1456_);
                    v___x_1462_ = lean_apply_2(v_inst_1455_, v_key_1459_, v_a_1456_);
                    v___x_1463_ = (lean_unbox(v___x_1462_) as u8);
                    if v___x_1463_ == 0 {
                        lean_dec(v_value_1460_);
                        lean_dec(v_key_1459_);
                        v_x_1458_ = v_tail_1461_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1461_);
                        lean_dec(v_a_1456_);
                        lean_dec_ref(v_inst_1455_);
                        v___x_1465_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1465_, 0, v_key_1459_);
                        lean_ctor_set(v___x_1465_, 1, v_value_1460_);
                        return v___x_1465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg___boxed(
    mut v_inst_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v_fallback_1468_: *mut LeanObject,
    mut v_x_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1470_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1466_,
        v_a_1467_,
        v_fallback_1468_,
        v_x_1469_,
    );
    lean_dec_ref(v_fallback_1468_);
    return v_res_1470_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD(
    mut v_00_u03b1_1471_: *mut LeanObject,
    mut v_00_u03b2_1472_: *mut LeanObject,
    mut v_inst_1473_: *mut LeanObject,
    mut v_a_1474_: *mut LeanObject,
    mut v_fallback_1475_: *mut LeanObject,
    mut v_x_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1473_,
        v_a_1474_,
        v_fallback_1475_,
        v_x_1476_,
    );
    return v___x_1477_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___boxed(
    mut v_00_u03b1_1478_: *mut LeanObject,
    mut v_00_u03b2_1479_: *mut LeanObject,
    mut v_inst_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
    mut v_fallback_1482_: *mut LeanObject,
    mut v_x_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1484_: *mut LeanObject = core::ptr::null_mut();
    v_res_1484_ = l_Std_DHashMap_Internal_AssocList_getEntryD(
        v_00_u03b1_1478_,
        v_00_u03b2_1479_,
        v_inst_1480_,
        v_a_1481_,
        v_fallback_1482_,
        v_x_1483_,
    );
    lean_dec_ref(v_fallback_1482_);
    return v_res_1484_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
    mut v_inst_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_inst_1487_: *mut LeanObject,
    mut v_x_1488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1488_) == 0 {
                    lean_dec(v_a_1486_);
                    lean_dec_ref(v_inst_1485_);
                    lean_inc_ref(v_inst_1487_);
                    return v_inst_1487_;
                } else {
                    v_key_1489_ = lean_ctor_get(v_x_1488_, 0);
                    lean_inc_n(v_key_1489_, 2);
                    v_value_1490_ = lean_ctor_get(v_x_1488_, 1);
                    lean_inc(v_value_1490_);
                    v_tail_1491_ = lean_ctor_get(v_x_1488_, 2);
                    lean_inc(v_tail_1491_);
                    lean_dec_ref_known(v_x_1488_, 3);
                    lean_inc_ref(v_inst_1485_);
                    lean_inc(v_a_1486_);
                    v___x_1492_ = lean_apply_2(v_inst_1485_, v_key_1489_, v_a_1486_);
                    v___x_1493_ = (lean_unbox(v___x_1492_) as u8);
                    if v___x_1493_ == 0 {
                        lean_dec(v_value_1490_);
                        lean_dec(v_key_1489_);
                        v_x_1488_ = v_tail_1491_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1491_);
                        lean_dec(v_a_1486_);
                        lean_dec_ref(v_inst_1485_);
                        v___x_1495_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1495_, 0, v_key_1489_);
                        lean_ctor_set(v___x_1495_, 1, v_value_1490_);
                        return v___x_1495_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg___boxed(
    mut v_inst_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_inst_1498_: *mut LeanObject,
    mut v_x_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1500_: *mut LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1496_,
        v_a_1497_,
        v_inst_1498_,
        v_x_1499_,
    );
    lean_dec_ref(v_inst_1498_);
    return v_res_1500_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21(
    mut v_00_u03b1_1501_: *mut LeanObject,
    mut v_00_u03b2_1502_: *mut LeanObject,
    mut v_inst_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
    mut v_inst_1505_: *mut LeanObject,
    mut v_x_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    v___x_1507_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1503_,
        v_a_1504_,
        v_inst_1505_,
        v_x_1506_,
    );
    return v___x_1507_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___boxed(
    mut v_00_u03b1_1508_: *mut LeanObject,
    mut v_00_u03b2_1509_: *mut LeanObject,
    mut v_inst_1510_: *mut LeanObject,
    mut v_a_1511_: *mut LeanObject,
    mut v_inst_1512_: *mut LeanObject,
    mut v_x_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1514_: *mut LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21(
        v_00_u03b1_1508_,
        v_00_u03b2_1509_,
        v_inst_1510_,
        v_a_1511_,
        v_inst_1512_,
        v_x_1513_,
    );
    lean_dec_ref(v_inst_1512_);
    return v_res_1514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey___redArg(
    mut v_inst_1515_: *mut LeanObject,
    mut v_a_1516_: *mut LeanObject,
    mut v_x_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1518_ = lean_ctor_get(v_x_1517_, 0);
                lean_inc_n(v_key_1518_, 2);
                v_tail_1519_ = lean_ctor_get(v_x_1517_, 2);
                lean_inc(v_tail_1519_);
                lean_dec(v_x_1517_);
                lean_inc_ref(v_inst_1515_);
                lean_inc(v_a_1516_);
                v___x_1520_ = lean_apply_2(v_inst_1515_, v_key_1518_, v_a_1516_);
                v___x_1521_ = (lean_unbox(v___x_1520_) as u8);
                if v___x_1521_ == 0 {
                    lean_dec(v_key_1518_);
                    v_x_1517_ = v_tail_1519_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_1519_);
                    lean_dec(v_a_1516_);
                    lean_dec_ref(v_inst_1515_);
                    return v_key_1518_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey(
    mut v_00_u03b1_1523_: *mut LeanObject,
    mut v_00_u03b2_1524_: *mut LeanObject,
    mut v_inst_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_x_1527_: *mut LeanObject,
    mut v_x_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    v___x_1529_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_1525_, v_a_1526_, v_x_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1534_ = lean_unsigned_to_nat(11);
    v___x_1535_ = lean_unsigned_to_nat(153);
    v___x_1536_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1;
    v___x_1537_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0;
    v___x_1538_ = l_mkPanicMessageWithDecl(
        v___x_1537_,
        v___x_1536_,
        v___x_1535_,
        v___x_1534_,
        v___x_1533_,
    );
    return v___x_1538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
    mut v_inst_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_inst_1541_: *mut LeanObject,
    mut v_x_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1542_) == 0 {
                    lean_dec(v_a_1540_);
                    lean_dec_ref(v_inst_1539_);
                    v___x_1543_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3_once
                        ),
                        _init_l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3,
                    );
                    v___x_1544_ = l_panic___redArg(v_inst_1541_, v___x_1543_);
                    return v___x_1544_;
                } else {
                    v_key_1545_ = lean_ctor_get(v_x_1542_, 0);
                    lean_inc(v_key_1545_);
                    v_value_1546_ = lean_ctor_get(v_x_1542_, 1);
                    lean_inc(v_value_1546_);
                    v_tail_1547_ = lean_ctor_get(v_x_1542_, 2);
                    lean_inc(v_tail_1547_);
                    lean_dec_ref_known(v_x_1542_, 3);
                    lean_inc_ref(v_inst_1539_);
                    lean_inc(v_a_1540_);
                    v___x_1548_ = lean_apply_2(v_inst_1539_, v_key_1545_, v_a_1540_);
                    v___x_1549_ = (lean_unbox(v___x_1548_) as u8);
                    if v___x_1549_ == 0 {
                        lean_dec(v_value_1546_);
                        v_x_1542_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1547_);
                        lean_dec(v_a_1540_);
                        lean_dec_ref(v_inst_1539_);
                        return v_value_1546_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___boxed(
    mut v_inst_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_inst_1553_: *mut LeanObject,
    mut v_x_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1551_,
        v_a_1552_,
        v_inst_1553_,
        v_x_1554_,
    );
    lean_dec(v_inst_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21(
    mut v_00_u03b1_1556_: *mut LeanObject,
    mut v_00_u03b2_1557_: *mut LeanObject,
    mut v_inst_1558_: *mut LeanObject,
    mut v_inst_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_inst_1561_: *mut LeanObject,
    mut v_x_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1558_,
        v_a_1560_,
        v_inst_1561_,
        v_x_1562_,
    );
    return v___x_1563_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___boxed(
    mut v_00_u03b1_1564_: *mut LeanObject,
    mut v_00_u03b2_1565_: *mut LeanObject,
    mut v_inst_1566_: *mut LeanObject,
    mut v_inst_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
    mut v_inst_1569_: *mut LeanObject,
    mut v_x_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1571_: *mut LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_getCast_x21(
        v_00_u03b1_1564_,
        v_00_u03b2_1565_,
        v_inst_1566_,
        v_inst_1567_,
        v_a_1568_,
        v_inst_1569_,
        v_x_1570_,
    );
    lean_dec(v_inst_1569_);
    return v_res_1571_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(
    mut v_inst_1572_: *mut LeanObject,
    mut v_a_1573_: *mut LeanObject,
    mut v_x_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1574_) == 0 {
                    lean_dec(v_a_1573_);
                    lean_dec_ref(v_inst_1572_);
                    v___x_1575_ = lean_box(0);
                    return v___x_1575_;
                } else {
                    v_key_1576_ = lean_ctor_get(v_x_1574_, 0);
                    lean_inc_n(v_key_1576_, 2);
                    v_tail_1577_ = lean_ctor_get(v_x_1574_, 2);
                    lean_inc(v_tail_1577_);
                    lean_dec_ref_known(v_x_1574_, 3);
                    lean_inc_ref(v_inst_1572_);
                    lean_inc(v_a_1573_);
                    v___x_1578_ = lean_apply_2(v_inst_1572_, v_key_1576_, v_a_1573_);
                    v___x_1579_ = (lean_unbox(v___x_1578_) as u8);
                    if v___x_1579_ == 0 {
                        lean_dec(v_key_1576_);
                        v_x_1574_ = v_tail_1577_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1577_);
                        lean_dec(v_a_1573_);
                        lean_dec_ref(v_inst_1572_);
                        v___x_1581_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1581_, 0, v_key_1576_);
                        return v___x_1581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f(
    mut v_00_u03b1_1582_: *mut LeanObject,
    mut v_00_u03b2_1583_: *mut LeanObject,
    mut v_inst_1584_: *mut LeanObject,
    mut v_a_1585_: *mut LeanObject,
    mut v_x_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_1584_, v_a_1585_, v_x_1586_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1590_ = lean_unsigned_to_nat(11);
    v___x_1591_ = lean_unsigned_to_nat(163);
    v___x_1592_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0;
    v___x_1593_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0;
    v___x_1594_ = l_mkPanicMessageWithDecl(
        v___x_1593_,
        v___x_1592_,
        v___x_1591_,
        v___x_1590_,
        v___x_1589_,
    );
    return v___x_1594_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
    mut v_inst_1595_: *mut LeanObject,
    mut v_inst_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
    mut v_x_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1598_) == 0 {
                    lean_dec(v_a_1597_);
                    lean_dec_ref(v_inst_1595_);
                    v___x_1599_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1,
                    );
                    v___x_1600_ = l_panic___redArg(v_inst_1596_, v___x_1599_);
                    return v___x_1600_;
                } else {
                    v_key_1601_ = lean_ctor_get(v_x_1598_, 0);
                    lean_inc(v_key_1601_);
                    v_value_1602_ = lean_ctor_get(v_x_1598_, 1);
                    lean_inc(v_value_1602_);
                    v_tail_1603_ = lean_ctor_get(v_x_1598_, 2);
                    lean_inc(v_tail_1603_);
                    lean_dec_ref_known(v_x_1598_, 3);
                    lean_inc_ref(v_inst_1595_);
                    lean_inc(v_a_1597_);
                    v___x_1604_ = lean_apply_2(v_inst_1595_, v_key_1601_, v_a_1597_);
                    v___x_1605_ = (lean_unbox(v___x_1604_) as u8);
                    if v___x_1605_ == 0 {
                        lean_dec(v_value_1602_);
                        v_x_1598_ = v_tail_1603_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1603_);
                        lean_dec(v_a_1597_);
                        lean_dec_ref(v_inst_1595_);
                        return v_value_1602_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___redArg___boxed(
    mut v_inst_1607_: *mut LeanObject,
    mut v_inst_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
    mut v_x_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1611_: *mut LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1607_,
        v_inst_1608_,
        v_a_1609_,
        v_x_1610_,
    );
    lean_dec(v_inst_1608_);
    return v_res_1611_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21(
    mut v_00_u03b1_1612_: *mut LeanObject,
    mut v_00_u03b2_1613_: *mut LeanObject,
    mut v_inst_1614_: *mut LeanObject,
    mut v_inst_1615_: *mut LeanObject,
    mut v_a_1616_: *mut LeanObject,
    mut v_x_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1614_,
        v_inst_1615_,
        v_a_1616_,
        v_x_1617_,
    );
    return v___x_1618_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___boxed(
    mut v_00_u03b1_1619_: *mut LeanObject,
    mut v_00_u03b2_1620_: *mut LeanObject,
    mut v_inst_1621_: *mut LeanObject,
    mut v_inst_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_x_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1625_: *mut LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Std_DHashMap_Internal_AssocList_get_x21(
        v_00_u03b1_1619_,
        v_00_u03b2_1620_,
        v_inst_1621_,
        v_inst_1622_,
        v_a_1623_,
        v_x_1624_,
    );
    lean_dec(v_inst_1622_);
    return v_res_1625_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1628_ = lean_unsigned_to_nat(11);
    v___x_1629_ = lean_unsigned_to_nat(168);
    v___x_1630_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0;
    v___x_1631_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0;
    v___x_1632_ = l_mkPanicMessageWithDecl(
        v___x_1631_,
        v___x_1630_,
        v___x_1629_,
        v___x_1628_,
        v___x_1627_,
    );
    return v___x_1632_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
    mut v_inst_1633_: *mut LeanObject,
    mut v_inst_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_x_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1636_) == 0 {
                    lean_dec(v_a_1635_);
                    lean_dec_ref(v_inst_1633_);
                    v___x_1637_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1_once
                        ),
                        _init_l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1,
                    );
                    v___x_1638_ = l_panic___redArg(v_inst_1634_, v___x_1637_);
                    return v___x_1638_;
                } else {
                    v_key_1639_ = lean_ctor_get(v_x_1636_, 0);
                    lean_inc_n(v_key_1639_, 2);
                    v_tail_1640_ = lean_ctor_get(v_x_1636_, 2);
                    lean_inc(v_tail_1640_);
                    lean_dec_ref_known(v_x_1636_, 3);
                    lean_inc_ref(v_inst_1633_);
                    lean_inc(v_a_1635_);
                    v___x_1641_ = lean_apply_2(v_inst_1633_, v_key_1639_, v_a_1635_);
                    v___x_1642_ = (lean_unbox(v___x_1641_) as u8);
                    if v___x_1642_ == 0 {
                        lean_dec(v_key_1639_);
                        v_x_1636_ = v_tail_1640_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1640_);
                        lean_dec(v_a_1635_);
                        lean_dec_ref(v_inst_1633_);
                        return v_key_1639_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___boxed(
    mut v_inst_1644_: *mut LeanObject,
    mut v_inst_1645_: *mut LeanObject,
    mut v_a_1646_: *mut LeanObject,
    mut v_x_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1644_,
        v_inst_1645_,
        v_a_1646_,
        v_x_1647_,
    );
    lean_dec(v_inst_1645_);
    return v_res_1648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21(
    mut v_00_u03b1_1649_: *mut LeanObject,
    mut v_00_u03b2_1650_: *mut LeanObject,
    mut v_inst_1651_: *mut LeanObject,
    mut v_inst_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_x_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1651_,
        v_inst_1652_,
        v_a_1653_,
        v_x_1654_,
    );
    return v___x_1655_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___boxed(
    mut v_00_u03b1_1656_: *mut LeanObject,
    mut v_00_u03b2_1657_: *mut LeanObject,
    mut v_inst_1658_: *mut LeanObject,
    mut v_inst_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_x_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1662_: *mut LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_DHashMap_Internal_AssocList_getKey_x21(
        v_00_u03b1_1656_,
        v_00_u03b2_1657_,
        v_inst_1658_,
        v_inst_1659_,
        v_a_1660_,
        v_x_1661_,
    );
    lean_dec(v_inst_1659_);
    return v_res_1662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
    mut v_inst_1663_: *mut LeanObject,
    mut v_a_1664_: *mut LeanObject,
    mut v_fallback_1665_: *mut LeanObject,
    mut v_x_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1666_) == 0 {
                    lean_dec(v_a_1664_);
                    lean_dec_ref(v_inst_1663_);
                    lean_inc(v_fallback_1665_);
                    return v_fallback_1665_;
                } else {
                    v_key_1667_ = lean_ctor_get(v_x_1666_, 0);
                    lean_inc(v_key_1667_);
                    v_value_1668_ = lean_ctor_get(v_x_1666_, 1);
                    lean_inc(v_value_1668_);
                    v_tail_1669_ = lean_ctor_get(v_x_1666_, 2);
                    lean_inc(v_tail_1669_);
                    lean_dec_ref_known(v_x_1666_, 3);
                    lean_inc_ref(v_inst_1663_);
                    lean_inc(v_a_1664_);
                    v___x_1670_ = lean_apply_2(v_inst_1663_, v_key_1667_, v_a_1664_);
                    v___x_1671_ = (lean_unbox(v___x_1670_) as u8);
                    if v___x_1671_ == 0 {
                        lean_dec(v_value_1668_);
                        v_x_1666_ = v_tail_1669_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1669_);
                        lean_dec(v_a_1664_);
                        lean_dec_ref(v_inst_1663_);
                        return v_value_1668_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg___boxed(
    mut v_inst_1673_: *mut LeanObject,
    mut v_a_1674_: *mut LeanObject,
    mut v_fallback_1675_: *mut LeanObject,
    mut v_x_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1677_: *mut LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1673_,
        v_a_1674_,
        v_fallback_1675_,
        v_x_1676_,
    );
    lean_dec(v_fallback_1675_);
    return v_res_1677_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD(
    mut v_00_u03b1_1678_: *mut LeanObject,
    mut v_00_u03b2_1679_: *mut LeanObject,
    mut v_inst_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
    mut v_fallback_1683_: *mut LeanObject,
    mut v_x_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1680_,
        v_a_1682_,
        v_fallback_1683_,
        v_x_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___boxed(
    mut v_00_u03b1_1686_: *mut LeanObject,
    mut v_00_u03b2_1687_: *mut LeanObject,
    mut v_inst_1688_: *mut LeanObject,
    mut v_inst_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v_fallback_1691_: *mut LeanObject,
    mut v_x_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Std_DHashMap_Internal_AssocList_getCastD(
        v_00_u03b1_1686_,
        v_00_u03b2_1687_,
        v_inst_1688_,
        v_inst_1689_,
        v_a_1690_,
        v_fallback_1691_,
        v_x_1692_,
    );
    lean_dec(v_fallback_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg(
    mut v_inst_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_fallback_1696_: *mut LeanObject,
    mut v_x_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1697_) == 0 {
                    lean_dec(v_a_1695_);
                    lean_dec_ref(v_inst_1694_);
                    lean_inc(v_fallback_1696_);
                    return v_fallback_1696_;
                } else {
                    v_key_1698_ = lean_ctor_get(v_x_1697_, 0);
                    lean_inc(v_key_1698_);
                    v_value_1699_ = lean_ctor_get(v_x_1697_, 1);
                    lean_inc(v_value_1699_);
                    v_tail_1700_ = lean_ctor_get(v_x_1697_, 2);
                    lean_inc(v_tail_1700_);
                    lean_dec_ref_known(v_x_1697_, 3);
                    lean_inc_ref(v_inst_1694_);
                    lean_inc(v_a_1695_);
                    v___x_1701_ = lean_apply_2(v_inst_1694_, v_key_1698_, v_a_1695_);
                    v___x_1702_ = (lean_unbox(v___x_1701_) as u8);
                    if v___x_1702_ == 0 {
                        lean_dec(v_value_1699_);
                        v_x_1697_ = v_tail_1700_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1700_);
                        lean_dec(v_a_1695_);
                        lean_dec_ref(v_inst_1694_);
                        return v_value_1699_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg___boxed(
    mut v_inst_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
    mut v_fallback_1706_: *mut LeanObject,
    mut v_x_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1708_: *mut LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1704_,
        v_a_1705_,
        v_fallback_1706_,
        v_x_1707_,
    );
    lean_dec(v_fallback_1706_);
    return v_res_1708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD(
    mut v_00_u03b1_1709_: *mut LeanObject,
    mut v_00_u03b2_1710_: *mut LeanObject,
    mut v_inst_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_fallback_1713_: *mut LeanObject,
    mut v_x_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1711_,
        v_a_1712_,
        v_fallback_1713_,
        v_x_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___boxed(
    mut v_00_u03b1_1716_: *mut LeanObject,
    mut v_00_u03b2_1717_: *mut LeanObject,
    mut v_inst_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
    mut v_fallback_1720_: *mut LeanObject,
    mut v_x_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1722_: *mut LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Std_DHashMap_Internal_AssocList_getD(
        v_00_u03b1_1716_,
        v_00_u03b2_1717_,
        v_inst_1718_,
        v_a_1719_,
        v_fallback_1720_,
        v_x_1721_,
    );
    lean_dec(v_fallback_1720_);
    return v_res_1722_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
    mut v_inst_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
    mut v_fallback_1725_: *mut LeanObject,
    mut v_x_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1726_) == 0 {
                    lean_dec(v_a_1724_);
                    lean_dec_ref(v_inst_1723_);
                    lean_inc(v_fallback_1725_);
                    return v_fallback_1725_;
                } else {
                    v_key_1727_ = lean_ctor_get(v_x_1726_, 0);
                    lean_inc_n(v_key_1727_, 2);
                    v_tail_1728_ = lean_ctor_get(v_x_1726_, 2);
                    lean_inc(v_tail_1728_);
                    lean_dec_ref_known(v_x_1726_, 3);
                    lean_inc_ref(v_inst_1723_);
                    lean_inc(v_a_1724_);
                    v___x_1729_ = lean_apply_2(v_inst_1723_, v_key_1727_, v_a_1724_);
                    v___x_1730_ = (lean_unbox(v___x_1729_) as u8);
                    if v___x_1730_ == 0 {
                        lean_dec(v_key_1727_);
                        v_x_1726_ = v_tail_1728_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1728_);
                        lean_dec(v_a_1724_);
                        lean_dec_ref(v_inst_1723_);
                        return v_key_1727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg___boxed(
    mut v_inst_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
    mut v_fallback_1734_: *mut LeanObject,
    mut v_x_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1732_,
        v_a_1733_,
        v_fallback_1734_,
        v_x_1735_,
    );
    lean_dec(v_fallback_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD(
    mut v_00_u03b1_1737_: *mut LeanObject,
    mut v_00_u03b2_1738_: *mut LeanObject,
    mut v_inst_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_fallback_1741_: *mut LeanObject,
    mut v_x_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1739_,
        v_a_1740_,
        v_fallback_1741_,
        v_x_1742_,
    );
    return v___x_1743_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___boxed(
    mut v_00_u03b1_1744_: *mut LeanObject,
    mut v_00_u03b2_1745_: *mut LeanObject,
    mut v_inst_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_fallback_1748_: *mut LeanObject,
    mut v_x_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Std_DHashMap_Internal_AssocList_getKeyD(
        v_00_u03b1_1744_,
        v_00_u03b2_1745_,
        v_inst_1746_,
        v_a_1747_,
        v_fallback_1748_,
        v_x_1749_,
    );
    lean_dec(v_fallback_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___redArg(
    mut v_inst_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_b_1753_: *mut LeanObject,
    mut v_x_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1754_) == 0 {
                    lean_dec(v_b_1753_);
                    lean_dec(v_a_1752_);
                    lean_dec_ref(v_inst_1751_);
                    return v_x_1754_;
                } else {
                    v_key_1755_ = lean_ctor_get(v_x_1754_, 0);
                    v_value_1756_ = lean_ctor_get(v_x_1754_, 1);
                    v_tail_1757_ = lean_ctor_get(v_x_1754_, 2);
                    v_isSharedCheck_1770_ = (!lean_is_exclusive(v_x_1754_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1759_ = v_x_1754_;
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1757_);
                        lean_inc(v_value_1756_);
                        lean_inc(v_key_1755_);
                        lean_dec(v_x_1754_);
                        v___x_1759_ = lean_box(0);
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1751_);
                lean_inc(v_a_1752_);
                lean_inc(v_key_1755_);
                v___x_1761_ = lean_apply_2(v_inst_1751_, v_key_1755_, v_a_1752_);
                v___x_1762_ = (lean_unbox(v___x_1761_) as u8);
                if v___x_1762_ == 0 {
                    v___x_1763_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_1751_,
                        v_a_1752_,
                        v_b_1753_,
                        v_tail_1757_,
                    );
                    if v_isShared_1760_ == 0 {
                        lean_ctor_set(v___x_1759_, 2, v___x_1763_);
                        v___x_1765_ = v___x_1759_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_key_1755_);
                        lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_value_1756_);
                        lean_ctor_set(v_reuseFailAlloc_1766_, 2, v___x_1763_);
                        v___x_1765_ = v_reuseFailAlloc_1766_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_1756_);
                    lean_dec(v_key_1755_);
                    lean_dec_ref(v_inst_1751_);
                    if v_isShared_1760_ == 0 {
                        lean_ctor_set(v___x_1759_, 1, v_b_1753_);
                        lean_ctor_set(v___x_1759_, 0, v_a_1752_);
                        v___x_1768_ = v___x_1759_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1752_);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_b_1753_);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_tail_1757_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1765_;
            }
            3 => {
                return v___x_1768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace(
    mut v_00_u03b1_1771_: *mut LeanObject,
    mut v_00_u03b2_1772_: *mut LeanObject,
    mut v_inst_1773_: *mut LeanObject,
    mut v_a_1774_: *mut LeanObject,
    mut v_b_1775_: *mut LeanObject,
    mut v_x_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
        v_inst_1773_,
        v_a_1774_,
        v_b_1775_,
        v_x_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___redArg(
    mut v_inst_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_x_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1780_) == 0 {
                    lean_dec(v_a_1779_);
                    lean_dec_ref(v_inst_1778_);
                    return v_x_1780_;
                } else {
                    v_key_1781_ = lean_ctor_get(v_x_1780_, 0);
                    v_value_1782_ = lean_ctor_get(v_x_1780_, 1);
                    v_tail_1783_ = lean_ctor_get(v_x_1780_, 2);
                    v_isSharedCheck_1793_ = (!lean_is_exclusive(v_x_1780_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1785_ = v_x_1780_;
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1783_);
                        lean_inc(v_value_1782_);
                        lean_inc(v_key_1781_);
                        lean_dec(v_x_1780_);
                        v___x_1785_ = lean_box(0);
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1778_);
                lean_inc(v_a_1779_);
                lean_inc(v_key_1781_);
                v___x_1787_ = lean_apply_2(v_inst_1778_, v_key_1781_, v_a_1779_);
                v___x_1788_ = (lean_unbox(v___x_1787_) as u8);
                if v___x_1788_ == 0 {
                    v___x_1789_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(
                        v_inst_1778_,
                        v_a_1779_,
                        v_tail_1783_,
                    );
                    if v_isShared_1786_ == 0 {
                        lean_ctor_set(v___x_1785_, 2, v___x_1789_);
                        v___x_1791_ = v___x_1785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_key_1781_);
                        lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_value_1782_);
                        lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1789_);
                        v___x_1791_ = v_reuseFailAlloc_1792_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1785_);
                    lean_dec(v_value_1782_);
                    lean_dec(v_key_1781_);
                    lean_dec(v_a_1779_);
                    lean_dec_ref(v_inst_1778_);
                    return v_tail_1783_;
                }
            }
            2 => {
                return v___x_1791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase(
    mut v_00_u03b1_1794_: *mut LeanObject,
    mut v_00_u03b2_1795_: *mut LeanObject,
    mut v_inst_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
    mut v_x_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    v___x_1799_ =
        l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_1796_, v_a_1797_, v_x_1798_);
    return v___x_1799_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_modify___redArg(
    mut v_inst_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
    mut v_f_1802_: *mut LeanObject,
    mut v_x_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1803_) == 0 {
                    lean_dec(v_f_1802_);
                    lean_dec(v_a_1801_);
                    lean_dec_ref(v_inst_1800_);
                    return v_x_1803_;
                } else {
                    v_key_1804_ = lean_ctor_get(v_x_1803_, 0);
                    v_value_1805_ = lean_ctor_get(v_x_1803_, 1);
                    v_tail_1806_ = lean_ctor_get(v_x_1803_, 2);
                    v_isSharedCheck_1820_ = (!lean_is_exclusive(v_x_1803_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1808_ = v_x_1803_;
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1806_);
                        lean_inc(v_value_1805_);
                        lean_inc(v_key_1804_);
                        lean_dec(v_x_1803_);
                        v___x_1808_ = lean_box(0);
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1800_);
                lean_inc(v_a_1801_);
                lean_inc(v_key_1804_);
                v___x_1810_ = lean_apply_2(v_inst_1800_, v_key_1804_, v_a_1801_);
                v___x_1811_ = (lean_unbox(v___x_1810_) as u8);
                if v___x_1811_ == 0 {
                    v___x_1812_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
                        v_inst_1800_,
                        v_a_1801_,
                        v_f_1802_,
                        v_tail_1806_,
                    );
                    if v_isShared_1809_ == 0 {
                        lean_ctor_set(v___x_1808_, 2, v___x_1812_);
                        v___x_1814_ = v___x_1808_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_key_1804_);
                        lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_value_1805_);
                        lean_ctor_set(v_reuseFailAlloc_1815_, 2, v___x_1812_);
                        v___x_1814_ = v_reuseFailAlloc_1815_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_1804_);
                    lean_dec_ref(v_inst_1800_);
                    v_b_1816_ = lean_apply_1(v_f_1802_, v_value_1805_);
                    if v_isShared_1809_ == 0 {
                        lean_ctor_set(v___x_1808_, 1, v_b_1816_);
                        lean_ctor_set(v___x_1808_, 0, v_a_1801_);
                        v___x_1818_ = v___x_1808_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1801_);
                        lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_b_1816_);
                        lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_tail_1806_);
                        v___x_1818_ = v_reuseFailAlloc_1819_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1814_;
            }
            3 => {
                return v___x_1818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_modify(
    mut v_00_u03b1_1821_: *mut LeanObject,
    mut v_00_u03b2_1822_: *mut LeanObject,
    mut v_inst_1823_: *mut LeanObject,
    mut v_inst_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_f_1826_: *mut LeanObject,
    mut v_x_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
        v_inst_1823_,
        v_a_1825_,
        v_f_1826_,
        v_x_1827_,
    );
    return v___x_1828_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_alter___redArg(
    mut v_inst_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_f_1831_: *mut LeanObject,
    mut v_x_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v_tail_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1832_) == 0 {
                    lean_dec_ref(v_inst_1829_);
                    v___x_1833_ = lean_box(0);
                    v___x_1834_ = lean_apply_1(v_f_1831_, v___x_1833_);
                    if lean_obj_tag(v___x_1834_) == 0 {
                        lean_dec(v_a_1830_);
                        return v_x_1832_;
                    } else {
                        v_val_1835_ = lean_ctor_get(v___x_1834_, 0);
                        lean_inc(v_val_1835_);
                        lean_dec_ref_known(v___x_1834_, 1);
                        v___x_1836_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_1836_, 0, v_a_1830_);
                        lean_ctor_set(v___x_1836_, 1, v_val_1835_);
                        lean_ctor_set(v___x_1836_, 2, v_x_1832_);
                        return v___x_1836_;
                    }
                } else {
                    v_key_1837_ = lean_ctor_get(v_x_1832_, 0);
                    v_value_1838_ = lean_ctor_get(v_x_1832_, 1);
                    v_tail_1839_ = lean_ctor_get(v_x_1832_, 2);
                    v_isSharedCheck_1855_ = (!lean_is_exclusive(v_x_1832_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1841_ = v_x_1832_;
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1839_);
                        lean_inc(v_value_1838_);
                        lean_inc(v_key_1837_);
                        lean_dec(v_x_1832_);
                        v___x_1841_ = lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1829_);
                lean_inc(v_a_1830_);
                lean_inc(v_key_1837_);
                v___x_1843_ = lean_apply_2(v_inst_1829_, v_key_1837_, v_a_1830_);
                v___x_1844_ = (lean_unbox(v___x_1843_) as u8);
                if v___x_1844_ == 0 {
                    v_tail_1845_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
                        v_inst_1829_,
                        v_a_1830_,
                        v_f_1831_,
                        v_tail_1839_,
                    );
                    if v_isShared_1842_ == 0 {
                        lean_ctor_set(v___x_1841_, 2, v_tail_1845_);
                        v___x_1847_ = v___x_1841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_key_1837_);
                        lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_value_1838_);
                        lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_tail_1845_);
                        v___x_1847_ = v_reuseFailAlloc_1848_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_1837_);
                    lean_dec_ref(v_inst_1829_);
                    v___x_1849_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1849_, 0, v_value_1838_);
                    v___x_1850_ = lean_apply_1(v_f_1831_, v___x_1849_);
                    if lean_obj_tag(v___x_1850_) == 0 {
                        lean_del_object(v___x_1841_);
                        lean_dec(v_a_1830_);
                        return v_tail_1839_;
                    } else {
                        v_val_1851_ = lean_ctor_get(v___x_1850_, 0);
                        lean_inc(v_val_1851_);
                        lean_dec_ref_known(v___x_1850_, 1);
                        if v_isShared_1842_ == 0 {
                            lean_ctor_set(v___x_1841_, 1, v_val_1851_);
                            lean_ctor_set(v___x_1841_, 0, v_a_1830_);
                            v___x_1853_ = v___x_1841_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1830_);
                            lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_val_1851_);
                            lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_tail_1839_);
                            v___x_1853_ = v_reuseFailAlloc_1854_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1847_;
            }
            3 => {
                return v___x_1853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_alter(
    mut v_00_u03b1_1856_: *mut LeanObject,
    mut v_00_u03b2_1857_: *mut LeanObject,
    mut v_inst_1858_: *mut LeanObject,
    mut v_inst_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_f_1861_: *mut LeanObject,
    mut v_x_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
        v_inst_1858_,
        v_a_1860_,
        v_f_1861_,
        v_x_1862_,
    );
    return v___x_1863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
    mut v_inst_1864_: *mut LeanObject,
    mut v_a_1865_: *mut LeanObject,
    mut v_f_1866_: *mut LeanObject,
    mut v_x_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1867_) == 0 {
                    lean_dec(v_f_1866_);
                    lean_dec(v_a_1865_);
                    lean_dec_ref(v_inst_1864_);
                    return v_x_1867_;
                } else {
                    v_key_1868_ = lean_ctor_get(v_x_1867_, 0);
                    v_value_1869_ = lean_ctor_get(v_x_1867_, 1);
                    v_tail_1870_ = lean_ctor_get(v_x_1867_, 2);
                    v_isSharedCheck_1884_ = (!lean_is_exclusive(v_x_1867_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1872_ = v_x_1867_;
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1870_);
                        lean_inc(v_value_1869_);
                        lean_inc(v_key_1868_);
                        lean_dec(v_x_1867_);
                        v___x_1872_ = lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1864_);
                lean_inc(v_a_1865_);
                lean_inc(v_key_1868_);
                v___x_1874_ = lean_apply_2(v_inst_1864_, v_key_1868_, v_a_1865_);
                v___x_1875_ = (lean_unbox(v___x_1874_) as u8);
                if v___x_1875_ == 0 {
                    v___x_1876_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
                        v_inst_1864_,
                        v_a_1865_,
                        v_f_1866_,
                        v_tail_1870_,
                    );
                    if v_isShared_1873_ == 0 {
                        lean_ctor_set(v___x_1872_, 2, v___x_1876_);
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_key_1868_);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_value_1869_);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 2, v___x_1876_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_1868_);
                    lean_dec_ref(v_inst_1864_);
                    v___x_1880_ = lean_apply_1(v_f_1866_, v_value_1869_);
                    if v_isShared_1873_ == 0 {
                        lean_ctor_set(v___x_1872_, 1, v___x_1880_);
                        lean_ctor_set(v___x_1872_, 0, v_a_1865_);
                        v___x_1882_ = v___x_1872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1865_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
                        lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_tail_1870_);
                        v___x_1882_ = v_reuseFailAlloc_1883_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1878_;
            }
            3 => {
                return v___x_1882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify(
    mut v_00_u03b1_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_00_u03b2_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_f_1889_: *mut LeanObject,
    mut v_x_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
        v_inst_1886_,
        v_a_1888_,
        v_f_1889_,
        v_x_1890_,
    );
    return v___x_1891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
    mut v_inst_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_f_1894_: *mut LeanObject,
    mut v_x_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_tail_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1895_) == 0 {
                    lean_dec_ref(v_inst_1892_);
                    v___x_1896_ = lean_box(0);
                    v___x_1897_ = lean_apply_1(v_f_1894_, v___x_1896_);
                    if lean_obj_tag(v___x_1897_) == 0 {
                        lean_dec(v_a_1893_);
                        return v_x_1895_;
                    } else {
                        v_val_1898_ = lean_ctor_get(v___x_1897_, 0);
                        lean_inc(v_val_1898_);
                        lean_dec_ref_known(v___x_1897_, 1);
                        v___x_1899_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_1899_, 0, v_a_1893_);
                        lean_ctor_set(v___x_1899_, 1, v_val_1898_);
                        lean_ctor_set(v___x_1899_, 2, v_x_1895_);
                        return v___x_1899_;
                    }
                } else {
                    v_key_1900_ = lean_ctor_get(v_x_1895_, 0);
                    v_value_1901_ = lean_ctor_get(v_x_1895_, 1);
                    v_tail_1902_ = lean_ctor_get(v_x_1895_, 2);
                    v_isSharedCheck_1918_ = (!lean_is_exclusive(v_x_1895_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1904_ = v_x_1895_;
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1902_);
                        lean_inc(v_value_1901_);
                        lean_inc(v_key_1900_);
                        lean_dec(v_x_1895_);
                        v___x_1904_ = lean_box(0);
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1892_);
                lean_inc(v_a_1893_);
                lean_inc(v_key_1900_);
                v___x_1906_ = lean_apply_2(v_inst_1892_, v_key_1900_, v_a_1893_);
                v___x_1907_ = (lean_unbox(v___x_1906_) as u8);
                if v___x_1907_ == 0 {
                    v_tail_1908_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
                        v_inst_1892_,
                        v_a_1893_,
                        v_f_1894_,
                        v_tail_1902_,
                    );
                    if v_isShared_1905_ == 0 {
                        lean_ctor_set(v___x_1904_, 2, v_tail_1908_);
                        v___x_1910_ = v___x_1904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_key_1900_);
                        lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_value_1901_);
                        lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_tail_1908_);
                        v___x_1910_ = v_reuseFailAlloc_1911_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_key_1900_);
                    lean_dec_ref(v_inst_1892_);
                    v___x_1912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1912_, 0, v_value_1901_);
                    v___x_1913_ = lean_apply_1(v_f_1894_, v___x_1912_);
                    if lean_obj_tag(v___x_1913_) == 0 {
                        lean_del_object(v___x_1904_);
                        lean_dec(v_a_1893_);
                        return v_tail_1902_;
                    } else {
                        v_val_1914_ = lean_ctor_get(v___x_1913_, 0);
                        lean_inc(v_val_1914_);
                        lean_dec_ref_known(v___x_1913_, 1);
                        if v_isShared_1905_ == 0 {
                            lean_ctor_set(v___x_1904_, 1, v_val_1914_);
                            lean_ctor_set(v___x_1904_, 0, v_a_1893_);
                            v___x_1916_ = v___x_1904_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1893_);
                            lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_val_1914_);
                            lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_tail_1902_);
                            v___x_1916_ = v_reuseFailAlloc_1917_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1910_;
            }
            3 => {
                return v___x_1916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter(
    mut v_00_u03b1_1919_: *mut LeanObject,
    mut v_inst_1920_: *mut LeanObject,
    mut v_00_u03b2_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
    mut v_f_1923_: *mut LeanObject,
    mut v_x_1924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
        v_inst_1920_,
        v_a_1922_,
        v_f_1923_,
        v_x_1924_,
    );
    return v___x_1925_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(
    mut v_f_1926_: *mut LeanObject,
    mut v_acc_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1928_) == 0 {
                    lean_dec_ref(v_f_1926_);
                    return v_acc_1927_;
                } else {
                    v_key_1929_ = lean_ctor_get(v_a_1928_, 0);
                    v_value_1930_ = lean_ctor_get(v_a_1928_, 1);
                    v_tail_1931_ = lean_ctor_get(v_a_1928_, 2);
                    v_isSharedCheck_1942_ = (!lean_is_exclusive(v_a_1928_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1933_ = v_a_1928_;
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1931_);
                        lean_inc(v_value_1930_);
                        lean_inc(v_key_1929_);
                        lean_dec(v_a_1928_);
                        v___x_1933_ = lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_1926_);
                lean_inc(v_key_1929_);
                v___x_1935_ = lean_apply_2(v_f_1926_, v_key_1929_, v_value_1930_);
                if lean_obj_tag(v___x_1935_) == 0 {
                    lean_del_object(v___x_1933_);
                    lean_dec(v_key_1929_);
                    v_a_1928_ = v_tail_1931_;
                    state = 0;
                    continue;
                } else {
                    v_val_1937_ = lean_ctor_get(v___x_1935_, 0);
                    lean_inc(v_val_1937_);
                    lean_dec_ref_known(v___x_1935_, 1);
                    if v_isShared_1934_ == 0 {
                        lean_ctor_set(v___x_1933_, 2, v_acc_1927_);
                        lean_ctor_set(v___x_1933_, 1, v_val_1937_);
                        v___x_1939_ = v___x_1933_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_key_1929_);
                        lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_val_1937_);
                        lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_acc_1927_);
                        v___x_1939_ = v_reuseFailAlloc_1941_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_acc_1927_ = v___x_1939_;
                v_a_1928_ = v_tail_1931_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go(
    mut v_00_u03b1_1943_: *mut LeanObject,
    mut v_00_u03b2_1944_: *mut LeanObject,
    mut v_00_u03b3_1945_: *mut LeanObject,
    mut v_f_1946_: *mut LeanObject,
    mut v_acc_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1949_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1946_, v_acc_1947_, v_a_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap___redArg(
    mut v_f_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = lean_box(0);
    v___x_1953_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1950_, v___x_1952_, v_a_1951_);
    return v___x_1953_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap(
    mut v_00_u03b1_1954_: *mut LeanObject,
    mut v_00_u03b2_1955_: *mut LeanObject,
    mut v_00_u03b3_1956_: *mut LeanObject,
    mut v_f_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    v___x_1959_ = lean_box(0);
    v___x_1960_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1957_, v___x_1959_, v_a_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(
    mut v_f_1961_: *mut LeanObject,
    mut v_acc_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1963_) == 0 {
                    lean_dec(v_f_1961_);
                    return v_acc_1962_;
                } else {
                    v_key_1964_ = lean_ctor_get(v_a_1963_, 0);
                    v_value_1965_ = lean_ctor_get(v_a_1963_, 1);
                    v_tail_1966_ = lean_ctor_get(v_a_1963_, 2);
                    v_isSharedCheck_1975_ = (!lean_is_exclusive(v_a_1963_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1968_ = v_a_1963_;
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1966_);
                        lean_inc(v_value_1965_);
                        lean_inc(v_key_1964_);
                        lean_dec(v_a_1963_);
                        v___x_1968_ = lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_f_1961_);
                lean_inc(v_key_1964_);
                v___x_1970_ = lean_apply_2(v_f_1961_, v_key_1964_, v_value_1965_);
                if v_isShared_1969_ == 0 {
                    lean_ctor_set(v___x_1968_, 2, v_acc_1962_);
                    lean_ctor_set(v___x_1968_, 1, v___x_1970_);
                    v___x_1972_ = v___x_1968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_key_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1970_);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_acc_1962_);
                    v___x_1972_ = v_reuseFailAlloc_1974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_acc_1962_ = v___x_1972_;
                v_a_1963_ = v_tail_1966_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go(
    mut v_00_u03b1_1976_: *mut LeanObject,
    mut v_00_u03b2_1977_: *mut LeanObject,
    mut v_00_u03b3_1978_: *mut LeanObject,
    mut v_f_1979_: *mut LeanObject,
    mut v_acc_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    v___x_1982_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1979_, v_acc_1980_, v_a_1981_);
    return v___x_1982_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map___redArg(
    mut v_f_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    v___x_1985_ = lean_box(0);
    v___x_1986_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1983_, v___x_1985_, v_a_1984_);
    return v___x_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map(
    mut v_00_u03b1_1987_: *mut LeanObject,
    mut v_00_u03b2_1988_: *mut LeanObject,
    mut v_00_u03b3_1989_: *mut LeanObject,
    mut v_f_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1992_ = lean_box(0);
    v___x_1993_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1990_, v___x_1992_, v_a_1991_);
    return v___x_1993_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(
    mut v_f_1994_: *mut LeanObject,
    mut v_acc_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1996_) == 0 {
                    lean_dec_ref(v_f_1994_);
                    return v_acc_1995_;
                } else {
                    v_key_1997_ = lean_ctor_get(v_a_1996_, 0);
                    v_value_1998_ = lean_ctor_get(v_a_1996_, 1);
                    v_tail_1999_ = lean_ctor_get(v_a_1996_, 2);
                    v_isSharedCheck_2010_ = (!lean_is_exclusive(v_a_1996_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2001_ = v_a_1996_;
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1999_);
                        lean_inc(v_value_1998_);
                        lean_inc(v_key_1997_);
                        lean_dec(v_a_1996_);
                        v___x_2001_ = lean_box(0);
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_1994_);
                lean_inc(v_value_1998_);
                lean_inc(v_key_1997_);
                v___x_2003_ = lean_apply_2(v_f_1994_, v_key_1997_, v_value_1998_);
                v___x_2004_ = (lean_unbox(v___x_2003_) as u8);
                if v___x_2004_ == 0 {
                    lean_del_object(v___x_2001_);
                    lean_dec(v_value_1998_);
                    lean_dec(v_key_1997_);
                    v_a_1996_ = v_tail_1999_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2002_ == 0 {
                        lean_ctor_set(v___x_2001_, 2, v_acc_1995_);
                        v___x_2007_ = v___x_2001_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_key_1997_);
                        lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_value_1998_);
                        lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_acc_1995_);
                        v___x_2007_ = v_reuseFailAlloc_2009_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_acc_1995_ = v___x_2007_;
                v_a_1996_ = v_tail_1999_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go(
    mut v_00_u03b1_2011_: *mut LeanObject,
    mut v_00_u03b2_2012_: *mut LeanObject,
    mut v_f_2013_: *mut LeanObject,
    mut v_acc_2014_: *mut LeanObject,
    mut v_a_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2013_, v_acc_2014_, v_a_2015_);
    return v___x_2016_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter___redArg(
    mut v_f_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    v___x_2019_ = lean_box(0);
    v___x_2020_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2017_, v___x_2019_, v_a_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter(
    mut v_00_u03b1_2021_: *mut LeanObject,
    mut v_00_u03b2_2022_: *mut LeanObject,
    mut v_f_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    v___x_2025_ = lean_box(0);
    v___x_2026_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2023_, v___x_2025_, v_a_2024_);
    return v___x_2026_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
}
