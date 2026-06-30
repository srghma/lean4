// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Basic
// Imports: Init.NotationExtra
use crate::ffi::lean_nat_add;
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
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(
    mut v_x_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1014_) == 0 {
        let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1015_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1015_;
    } else {
        let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1016_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1016_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg___boxed(
    mut v_x_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1017_);
    leanh::lean_dec(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx(
    mut v_00_u03b1_1019_: *mut leanh::LeanObject,
    mut v_00_u03b2_1020_: *mut leanh::LeanObject,
    mut v_x_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1022_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___boxed(
    mut v_00_u03b1_1023_: *mut leanh::LeanObject,
    mut v_00_u03b2_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Std_DHashMap_Internal_AssocList_ctorIdx(v_00_u03b1_1023_, v_00_u03b2_1024_, v_x_1025_);
    leanh::lean_dec(v_x_1025_);
    return v_res_1026_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(
    mut v_t_1027_: *mut leanh::LeanObject,
    mut v_k_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1027_) == 0 {
        return v_k_1028_;
    } else {
        let mut v_key_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_1029_ = leanh::lean_ctor_get(v_t_1027_, 0);
        leanh::lean_inc(v_key_1029_);
        v_value_1030_ = leanh::lean_ctor_get(v_t_1027_, 1);
        leanh::lean_inc(v_value_1030_);
        v_tail_1031_ = leanh::lean_ctor_get(v_t_1027_, 2);
        leanh::lean_inc(v_tail_1031_);
        leanh::lean_dec_ref_known(v_t_1027_, 3);
        v___x_1032_ =
            leanh::lean_apply_3(v_k_1028_, v_key_1029_, v_value_1030_, v_tail_1031_);
        return v___x_1032_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim(
    mut v_00_u03b1_1033_: *mut leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut leanh::LeanObject,
    mut v_motive_1035_: *mut leanh::LeanObject,
    mut v_ctorIdx_1036_: *mut leanh::LeanObject,
    mut v_t_1037_: *mut leanh::LeanObject,
    mut v_h_1038_: *mut leanh::LeanObject,
    mut v_k_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1037_, v_k_1039_);
    return v___x_1040_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___boxed(
    mut v_00_u03b1_1041_: *mut leanh::LeanObject,
    mut v_00_u03b2_1042_: *mut leanh::LeanObject,
    mut v_motive_1043_: *mut leanh::LeanObject,
    mut v_ctorIdx_1044_: *mut leanh::LeanObject,
    mut v_t_1045_: *mut leanh::LeanObject,
    mut v_h_1046_: *mut leanh::LeanObject,
    mut v_k_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_DHashMap_Internal_AssocList_ctorElim(
        v_00_u03b1_1041_,
        v_00_u03b2_1042_,
        v_motive_1043_,
        v_ctorIdx_1044_,
        v_t_1045_,
        v_h_1046_,
        v_k_1047_,
    );
    leanh::lean_dec(v_ctorIdx_1044_);
    return v_res_1048_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim___redArg(
    mut v_t_1049_: *mut leanh::LeanObject,
    mut v_nil_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1049_, v_nil_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim(
    mut v_00_u03b1_1052_: *mut leanh::LeanObject,
    mut v_00_u03b2_1053_: *mut leanh::LeanObject,
    mut v_motive_1054_: *mut leanh::LeanObject,
    mut v_t_1055_: *mut leanh::LeanObject,
    mut v_h_1056_: *mut leanh::LeanObject,
    mut v_nil_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1055_, v_nil_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim___redArg(
    mut v_t_1059_: *mut leanh::LeanObject,
    mut v_cons_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1059_, v_cons_1060_);
    return v___x_1061_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim(
    mut v_00_u03b1_1062_: *mut leanh::LeanObject,
    mut v_00_u03b2_1063_: *mut leanh::LeanObject,
    mut v_motive_1064_: *mut leanh::LeanObject,
    mut v_t_1065_: *mut leanh::LeanObject,
    mut v_h_1066_: *mut leanh::LeanObject,
    mut v_cons_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1065_, v_cons_1067_);
    return v___x_1068_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList_default(
    mut v_00_u03b1_1069_: *mut leanh::LeanObject,
    mut v_00_u03b2_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = leanh::lean_box(0);
    return v___x_1071_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList(
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_box(0);
    return v___x_1074_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
    mut v_inst_1075_: *mut leanh::LeanObject,
    mut v_f_1076_: *mut leanh::LeanObject,
    mut v_x_1077_: *mut leanh::LeanObject,
    mut v_x_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1078_) == 0 {
        let mut v_toApplicative_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1079_ = leanh::lean_ctor_get(v_inst_1075_, 0);
        leanh::lean_inc_ref(v_toApplicative_1079_);
        leanh::lean_dec(v_f_1076_);
        leanh::lean_dec_ref(v_inst_1075_);
        v_toPure_1080_ = leanh::lean_ctor_get(v_toApplicative_1079_, 1);
        leanh::lean_inc(v_toPure_1080_);
        leanh::lean_dec_ref(v_toApplicative_1079_);
        v___x_1081_ =
            leanh::lean_apply_2(v_toPure_1080_, leanh::lean_box(0), v_x_1077_);
        return v___x_1081_;
    } else {
        let mut v_toBind_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1082_ = leanh::lean_ctor_get(v_inst_1075_, 1);
        leanh::lean_inc(v_toBind_1082_);
        v_key_1083_ = leanh::lean_ctor_get(v_x_1078_, 0);
        leanh::lean_inc(v_key_1083_);
        v_value_1084_ = leanh::lean_ctor_get(v_x_1078_, 1);
        leanh::lean_inc(v_value_1084_);
        v_tail_1085_ = leanh::lean_ctor_get(v_x_1078_, 2);
        leanh::lean_inc(v_tail_1085_);
        leanh::lean_dec_ref_known(v_x_1078_, 3);
        leanh::lean_inc(v_f_1076_);
        v___f_1086_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1086_, 0, v_inst_1075_);
        leanh::lean_closure_set(v___f_1086_, 1, v_f_1076_);
        leanh::lean_closure_set(v___f_1086_, 2, v_tail_1085_);
        v___x_1087_ = leanh::lean_apply_3(v_f_1076_, v_x_1077_, v_key_1083_, v_value_1084_);
        v___x_1088_ = leanh::lean_apply_4(
            v_toBind_1082_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1087_,
            v___f_1086_,
        );
        return v___x_1088_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0(
    mut v_inst_1089_: *mut leanh::LeanObject,
    mut v_f_1090_: *mut leanh::LeanObject,
    mut v_tail_1091_: *mut leanh::LeanObject,
    mut v_d_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1089_,
        v_f_1090_,
        v_d_1092_,
        v_tail_1091_,
    );
    return v___x_1093_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM(
    mut v_00_u03b1_1094_: *mut leanh::LeanObject,
    mut v_00_u03b2_1095_: *mut leanh::LeanObject,
    mut v_00_u03b4_1096_: *mut leanh::LeanObject,
    mut v_m_1097_: *mut leanh::LeanObject,
    mut v_inst_1098_: *mut leanh::LeanObject,
    mut v_f_1099_: *mut leanh::LeanObject,
    mut v_x_1100_: *mut leanh::LeanObject,
    mut v_x_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1098_,
        v_f_1099_,
        v_x_1100_,
        v_x_1101_,
    );
    return v___x_1102_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0(
    mut v_f_1103_: *mut leanh::LeanObject,
    mut v_x1_1104_: *mut leanh::LeanObject,
    mut v_x2_1105_: *mut leanh::LeanObject,
    mut v_x3_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = leanh::lean_apply_3(v_f_1103_, v_x1_1104_, v_x2_1105_, v_x3_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg(
    mut v_f_1127_: *mut leanh::LeanObject,
    mut v_init_1128_: *mut leanh::LeanObject,
    mut v_as_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1130_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1130_, 0, v_f_1127_);
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
    mut v_00_u03b1_1133_: *mut leanh::LeanObject,
    mut v_00_u03b2_1134_: *mut leanh::LeanObject,
    mut v_00_u03b4_1135_: *mut leanh::LeanObject,
    mut v_f_1136_: *mut leanh::LeanObject,
    mut v_init_1137_: *mut leanh::LeanObject,
    mut v_as_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1139_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1139_, 0, v_f_1136_);
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
    mut v_f_1142_: *mut leanh::LeanObject,
    mut v_key_1143_: *mut leanh::LeanObject,
    mut v_value_1144_: *mut leanh::LeanObject,
    mut v_d_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = leanh::lean_apply_3(v_f_1142_, v_key_1143_, v_value_1144_, v_d_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
    mut v_inst_1147_: *mut leanh::LeanObject,
    mut v_f_1148_: *mut leanh::LeanObject,
    mut v_x_1149_: *mut leanh::LeanObject,
    mut v_x_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1150_) == 0 {
        let mut v_toApplicative_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1151_ = leanh::lean_ctor_get(v_inst_1147_, 0);
        leanh::lean_inc_ref(v_toApplicative_1151_);
        leanh::lean_dec(v_f_1148_);
        leanh::lean_dec_ref(v_inst_1147_);
        v_toPure_1152_ = leanh::lean_ctor_get(v_toApplicative_1151_, 1);
        leanh::lean_inc(v_toPure_1152_);
        leanh::lean_dec_ref(v_toApplicative_1151_);
        v___x_1153_ =
            leanh::lean_apply_2(v_toPure_1152_, leanh::lean_box(0), v_x_1149_);
        return v___x_1153_;
    } else {
        let mut v_toBind_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1154_ = leanh::lean_ctor_get(v_inst_1147_, 1);
        leanh::lean_inc(v_toBind_1154_);
        v_key_1155_ = leanh::lean_ctor_get(v_x_1150_, 0);
        leanh::lean_inc(v_key_1155_);
        v_value_1156_ = leanh::lean_ctor_get(v_x_1150_, 1);
        leanh::lean_inc(v_value_1156_);
        v_tail_1157_ = leanh::lean_ctor_get(v_x_1150_, 2);
        leanh::lean_inc(v_tail_1157_);
        leanh::lean_dec_ref_known(v_x_1150_, 3);
        leanh::lean_inc(v_f_1148_);
        v___f_1158_ = leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1158_, 0, v_f_1148_);
        leanh::lean_closure_set(v___f_1158_, 1, v_key_1155_);
        leanh::lean_closure_set(v___f_1158_, 2, v_value_1156_);
        v___x_1159_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
            v_inst_1147_,
            v_f_1148_,
            v_x_1149_,
            v_tail_1157_,
        );
        v___x_1160_ = leanh::lean_apply_4(
            v_toBind_1154_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1159_,
            v___f_1158_,
        );
        return v___x_1160_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM(
    mut v_00_u03b1_1161_: *mut leanh::LeanObject,
    mut v_00_u03b2_1162_: *mut leanh::LeanObject,
    mut v_00_u03b4_1163_: *mut leanh::LeanObject,
    mut v_m_1164_: *mut leanh::LeanObject,
    mut v_inst_1165_: *mut leanh::LeanObject,
    mut v_f_1166_: *mut leanh::LeanObject,
    mut v_x_1167_: *mut leanh::LeanObject,
    mut v_x_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v_inst_1165_,
        v_f_1166_,
        v_x_1167_,
        v_x_1168_,
    );
    return v___x_1169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldr___redArg(
    mut v_f_1170_: *mut leanh::LeanObject,
    mut v_init_1171_: *mut leanh::LeanObject,
    mut v_as_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1173_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1173_, 0, v_f_1170_);
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
    mut v_00_u03b1_1176_: *mut leanh::LeanObject,
    mut v_00_u03b2_1177_: *mut leanh::LeanObject,
    mut v_00_u03b4_1178_: *mut leanh::LeanObject,
    mut v_f_1179_: *mut leanh::LeanObject,
    mut v_init_1180_: *mut leanh::LeanObject,
    mut v_as_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1182_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1182_, 0, v_f_1179_);
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
    mut v_f_1185_: *mut leanh::LeanObject,
    mut v_x_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = leanh::lean_apply_2(v_f_1185_, v___y_1187_, v___y_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM___redArg(
    mut v_inst_1190_: *mut leanh::LeanObject,
    mut v_f_1191_: *mut leanh::LeanObject,
    mut v_as_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1193_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1193_, 0, v_f_1191_);
    v___x_1194_ = leanh::lean_box(0);
    v___x_1195_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1190_,
        v___f_1193_,
        v___x_1194_,
        v_as_1192_,
    );
    return v___x_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM(
    mut v_00_u03b1_1196_: *mut leanh::LeanObject,
    mut v_00_u03b2_1197_: *mut leanh::LeanObject,
    mut v_m_1198_: *mut leanh::LeanObject,
    mut v_inst_1199_: *mut leanh::LeanObject,
    mut v_f_1200_: *mut leanh::LeanObject,
    mut v_as_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1202_ = leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1202_, 0, v_f_1200_);
    v___x_1203_ = leanh::lean_box(0);
    v___x_1204_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1199_,
        v___f_1202_,
        v___x_1203_,
        v_as_1201_,
    );
    return v___x_1204_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(
    mut v_inst_1205_: *mut leanh::LeanObject,
    mut v_f_1206_: *mut leanh::LeanObject,
    mut v_a_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_1207_) == 0 {
        let mut v_toApplicative_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1209_ = leanh::lean_ctor_get(v_inst_1205_, 0);
        leanh::lean_inc_ref(v_toApplicative_1209_);
        leanh::lean_dec(v_f_1206_);
        leanh::lean_dec_ref(v_inst_1205_);
        v_toPure_1210_ = leanh::lean_ctor_get(v_toApplicative_1209_, 1);
        leanh::lean_inc(v_toPure_1210_);
        leanh::lean_dec_ref(v_toApplicative_1209_);
        v___x_1211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1211_, 0, v_a_1208_);
        v___x_1212_ =
            leanh::lean_apply_2(v_toPure_1210_, leanh::lean_box(0), v___x_1211_);
        return v___x_1212_;
    } else {
        let mut v_toApplicative_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1213_ = leanh::lean_ctor_get(v_inst_1205_, 0);
        v_toBind_1214_ = leanh::lean_ctor_get(v_inst_1205_, 1);
        leanh::lean_inc(v_toBind_1214_);
        v_toPure_1215_ = leanh::lean_ctor_get(v_toApplicative_1213_, 1);
        leanh::lean_inc(v_toPure_1215_);
        v_key_1216_ = leanh::lean_ctor_get(v_a_1207_, 0);
        leanh::lean_inc(v_key_1216_);
        v_value_1217_ = leanh::lean_ctor_get(v_a_1207_, 1);
        leanh::lean_inc(v_value_1217_);
        v_tail_1218_ = leanh::lean_ctor_get(v_a_1207_, 2);
        leanh::lean_inc(v_tail_1218_);
        leanh::lean_dec_ref_known(v_a_1207_, 3);
        leanh::lean_inc(v_f_1206_);
        v___f_1219_ = leanh::lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0 as *mut core::ffi::c_void, 5, 4);
        leanh::lean_closure_set(v___f_1219_, 0, v_toPure_1215_);
        leanh::lean_closure_set(v___f_1219_, 1, v_inst_1205_);
        leanh::lean_closure_set(v___f_1219_, 2, v_f_1206_);
        leanh::lean_closure_set(v___f_1219_, 3, v_tail_1218_);
        v___x_1220_ = leanh::lean_apply_3(v_f_1206_, v_key_1216_, v_value_1217_, v_a_1208_);
        v___x_1221_ = leanh::lean_apply_4(
            v_toBind_1214_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1220_,
            v___f_1219_,
        );
        return v___x_1221_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0(
    mut v_toPure_1222_: *mut leanh::LeanObject,
    mut v_inst_1223_: *mut leanh::LeanObject,
    mut v_f_1224_: *mut leanh::LeanObject,
    mut v_tail_1225_: *mut leanh::LeanObject,
    mut v_____do__lift_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1226_) == 0 {
        let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_tail_1225_);
        leanh::lean_dec(v_f_1224_);
        leanh::lean_dec_ref(v_inst_1223_);
        v___x_1227_ = leanh::lean_apply_2(
            v_toPure_1222_,
            leanh::lean_box(0),
            v_____do__lift_1226_,
        );
        return v___x_1227_;
    } else {
        let mut v_a_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1222_);
        v_a_1228_ = leanh::lean_ctor_get(v_____do__lift_1226_, 0);
        leanh::lean_inc(v_a_1228_);
        leanh::lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1229_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1223_, v_f_1224_, v_tail_1225_, v_a_1228_);
        return v___x_1229_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(
    mut v_00_u03b1_1230_: *mut leanh::LeanObject,
    mut v_00_u03b2_1231_: *mut leanh::LeanObject,
    mut v_00_u03b4_1232_: *mut leanh::LeanObject,
    mut v_m_1233_: *mut leanh::LeanObject,
    mut v_inst_1234_: *mut leanh::LeanObject,
    mut v_f_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1234_, v_f_1235_, v_a_1236_, v_a_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep___redArg(
    mut v_inst_1239_: *mut leanh::LeanObject,
    mut v_as_1240_: *mut leanh::LeanObject,
    mut v_init_1241_: *mut leanh::LeanObject,
    mut v_f_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1239_, v_f_1242_, v_as_1240_, v_init_1241_);
    return v___x_1243_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep(
    mut v_00_u03b1_1244_: *mut leanh::LeanObject,
    mut v_00_u03b2_1245_: *mut leanh::LeanObject,
    mut v_00_u03b4_1246_: *mut leanh::LeanObject,
    mut v_m_1247_: *mut leanh::LeanObject,
    mut v_inst_1248_: *mut leanh::LeanObject,
    mut v_as_1249_: *mut leanh::LeanObject,
    mut v_init_1250_: *mut leanh::LeanObject,
    mut v_f_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1248_, v_f_1251_, v_as_1249_, v_init_1250_);
    return v___x_1252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg(
    mut v_x_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1253_) == 0 {
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1254_ = leanh::lean_box(0);
        return v___x_1254_;
    } else {
        let mut v_key_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_1255_ = leanh::lean_ctor_get(v_x_1253_, 0);
        v_value_1256_ = leanh::lean_ctor_get(v_x_1253_, 1);
        v_tail_1257_ = leanh::lean_ctor_get(v_x_1253_, 2);
        leanh::lean_inc(v_value_1256_);
        leanh::lean_inc(v_key_1255_);
        v___x_1258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1258_, 0, v_key_1255_);
        leanh::lean_ctor_set(v___x_1258_, 1, v_value_1256_);
        v___x_1259_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_tail_1257_);
        v___x_1260_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1260_, 0, v___x_1258_);
        leanh::lean_ctor_set(v___x_1260_, 1, v___x_1259_);
        return v___x_1260_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg___boxed(
    mut v_x_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1261_);
    leanh::lean_dec(v_x_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList(
    mut v_00_u03b1_1263_: *mut leanh::LeanObject,
    mut v_00_u03b2_1264_: *mut leanh::LeanObject,
    mut v_x_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___boxed(
    mut v_00_u03b1_1267_: *mut leanh::LeanObject,
    mut v_00_u03b2_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ =
        l_Std_DHashMap_Internal_AssocList_toList(v_00_u03b1_1267_, v_00_u03b2_1268_, v_x_1269_);
    leanh::lean_dec(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v_x_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1272_) == 0 {
                    return v_x_1271_;
                } else {
                    v_tail_1273_ = leanh::lean_ctor_get(v_x_1272_, 2);
                    v___x_1274_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1275_ = lean_nat_add(v_x_1271_, v___x_1274_);
                    leanh::lean_dec(v_x_1271_);
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
    mut v_x_1277_: *mut leanh::LeanObject,
    mut v_x_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1277_, v_x_1278_);
    leanh::lean_dec(v_x_1278_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg(
    mut v_l_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = leanh::lean_unsigned_to_nat(0);
    v___x_1282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v___x_1281_, v_l_1280_);
    return v___x_1282_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg___boxed(
    mut v_l_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1283_);
    leanh::lean_dec(v_l_1283_);
    return v_res_1284_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length(
    mut v_00_u03b1_1285_: *mut leanh::LeanObject,
    mut v_00_u03b2_1286_: *mut leanh::LeanObject,
    mut v_l_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___boxed(
    mut v_00_u03b1_1289_: *mut leanh::LeanObject,
    mut v_00_u03b2_1290_: *mut leanh::LeanObject,
    mut v_l_1291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ =
        l_Std_DHashMap_Internal_AssocList_length(v_00_u03b1_1289_, v_00_u03b2_1290_, v_l_1291_);
    leanh::lean_dec(v_l_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(
    mut v_00_u03b1_1293_: *mut leanh::LeanObject,
    mut v_00_u03b2_1294_: *mut leanh::LeanObject,
    mut v_x_1295_: *mut leanh::LeanObject,
    mut v_x_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1295_, v_x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___boxed(
    mut v_00_u03b1_1298_: *mut leanh::LeanObject,
    mut v_00_u03b2_1299_: *mut leanh::LeanObject,
    mut v_x_1300_: *mut leanh::LeanObject,
    mut v_x_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(v_00_u03b1_1298_, v_00_u03b2_1299_, v_x_1300_, v_x_1301_);
    leanh::lean_dec(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
    mut v_inst_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
    mut v_x_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1305_) == 0 {
                    leanh::lean_dec(v_a_1304_);
                    leanh::lean_dec_ref(v_inst_1303_);
                    v___x_1306_ = leanh::lean_box(0);
                    return v___x_1306_;
                } else {
                    v_key_1307_ = leanh::lean_ctor_get(v_x_1305_, 0);
                    leanh::lean_inc(v_key_1307_);
                    v_value_1308_ = leanh::lean_ctor_get(v_x_1305_, 1);
                    leanh::lean_inc(v_value_1308_);
                    v_tail_1309_ = leanh::lean_ctor_get(v_x_1305_, 2);
                    leanh::lean_inc(v_tail_1309_);
                    leanh::lean_dec_ref_known(v_x_1305_, 3);
                    leanh::lean_inc_ref(v_inst_1303_);
                    leanh::lean_inc(v_a_1304_);
                    v___x_1310_ = leanh::lean_apply_2(v_inst_1303_, v_key_1307_, v_a_1304_);
                    v___x_1311_ = (leanh::lean_unbox(v___x_1310_) as u8);
                    if v___x_1311_ == 0 {
                        leanh::lean_dec(v_value_1308_);
                        v_x_1305_ = v_tail_1309_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1309_);
                        leanh::lean_dec(v_a_1304_);
                        leanh::lean_dec_ref(v_inst_1303_);
                        v___x_1313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1313_, 0, v_value_1308_);
                        return v___x_1313_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f(
    mut v_00_u03b1_1314_: *mut leanh::LeanObject,
    mut v_00_u03b2_1315_: *mut leanh::LeanObject,
    mut v_inst_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
    mut v_x_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1316_, v_a_1317_, v_x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
    mut v_inst_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_x_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1322_) == 0 {
                    leanh::lean_dec(v_a_1321_);
                    leanh::lean_dec_ref(v_inst_1320_);
                    v___x_1323_ = leanh::lean_box(0);
                    return v___x_1323_;
                } else {
                    v_key_1324_ = leanh::lean_ctor_get(v_x_1322_, 0);
                    leanh::lean_inc(v_key_1324_);
                    v_value_1325_ = leanh::lean_ctor_get(v_x_1322_, 1);
                    leanh::lean_inc(v_value_1325_);
                    v_tail_1326_ = leanh::lean_ctor_get(v_x_1322_, 2);
                    leanh::lean_inc(v_tail_1326_);
                    leanh::lean_dec_ref_known(v_x_1322_, 3);
                    leanh::lean_inc_ref(v_inst_1320_);
                    leanh::lean_inc(v_a_1321_);
                    v___x_1327_ = leanh::lean_apply_2(v_inst_1320_, v_key_1324_, v_a_1321_);
                    v___x_1328_ = (leanh::lean_unbox(v___x_1327_) as u8);
                    if v___x_1328_ == 0 {
                        leanh::lean_dec(v_value_1325_);
                        v_x_1322_ = v_tail_1326_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1326_);
                        leanh::lean_dec(v_a_1321_);
                        leanh::lean_dec_ref(v_inst_1320_);
                        v___x_1330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1330_, 0, v_value_1325_);
                        return v___x_1330_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f(
    mut v_00_u03b1_1331_: *mut leanh::LeanObject,
    mut v_00_u03b2_1332_: *mut leanh::LeanObject,
    mut v_inst_1333_: *mut leanh::LeanObject,
    mut v_inst_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_x_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ =
        l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_1333_, v_a_1335_, v_x_1336_);
    return v___x_1337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
    mut v_inst_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1340_) == 0 {
                    leanh::lean_dec(v_a_1339_);
                    leanh::lean_dec_ref(v_inst_1338_);
                    v___x_1341_ = leanh::lean_box(0);
                    return v___x_1341_;
                } else {
                    v_key_1342_ = leanh::lean_ctor_get(v_x_1340_, 0);
                    leanh::lean_inc_n(v_key_1342_, 2);
                    v_value_1343_ = leanh::lean_ctor_get(v_x_1340_, 1);
                    leanh::lean_inc(v_value_1343_);
                    v_tail_1344_ = leanh::lean_ctor_get(v_x_1340_, 2);
                    leanh::lean_inc(v_tail_1344_);
                    leanh::lean_dec_ref_known(v_x_1340_, 3);
                    leanh::lean_inc_ref(v_inst_1338_);
                    leanh::lean_inc(v_a_1339_);
                    v___x_1345_ = leanh::lean_apply_2(v_inst_1338_, v_key_1342_, v_a_1339_);
                    v___x_1346_ = (leanh::lean_unbox(v___x_1345_) as u8);
                    if v___x_1346_ == 0 {
                        leanh::lean_dec(v_value_1343_);
                        leanh::lean_dec(v_key_1342_);
                        v_x_1340_ = v_tail_1344_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1344_);
                        leanh::lean_dec(v_a_1339_);
                        leanh::lean_dec_ref(v_inst_1338_);
                        v___x_1348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1348_, 0, v_key_1342_);
                        leanh::lean_ctor_set(v___x_1348_, 1, v_value_1343_);
                        v___x_1349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                        return v___x_1349_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f(
    mut v_00_u03b1_1350_: *mut leanh::LeanObject,
    mut v_00_u03b2_1351_: *mut leanh::LeanObject,
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
    mut v_x_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ =
        l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_1352_, v_a_1353_, v_x_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg(
    mut v_inst_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
    mut v_x_1358_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1359_: u8 = 0;
    let mut v_key_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1358_) == 0 {
                    leanh::lean_dec(v_a_1357_);
                    leanh::lean_dec_ref(v_inst_1356_);
                    v___x_1359_ = 0;
                    return v___x_1359_;
                } else {
                    v_key_1360_ = leanh::lean_ctor_get(v_x_1358_, 0);
                    leanh::lean_inc(v_key_1360_);
                    v_tail_1361_ = leanh::lean_ctor_get(v_x_1358_, 2);
                    leanh::lean_inc(v_tail_1361_);
                    leanh::lean_dec_ref_known(v_x_1358_, 3);
                    leanh::lean_inc_ref(v_inst_1356_);
                    leanh::lean_inc(v_a_1357_);
                    v___x_1362_ = leanh::lean_apply_2(v_inst_1356_, v_key_1360_, v_a_1357_);
                    v___x_1363_ = (leanh::lean_unbox(v___x_1362_) as u8);
                    if v___x_1363_ == 0 {
                        v_x_1358_ = v_tail_1361_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1361_);
                        leanh::lean_dec(v_a_1357_);
                        leanh::lean_dec_ref(v_inst_1356_);
                        v___x_1365_ = (leanh::lean_unbox(v___x_1362_) as u8);
                        return v___x_1365_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg___boxed(
    mut v_inst_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_x_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1369_: u8 = 0;
    let mut v_r_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1366_, v_a_1367_, v_x_1368_);
    v_r_1370_ = leanh::lean_box((v_res_1369_) as usize);
    return v_r_1370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains(
    mut v_00_u03b1_1371_: *mut leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut leanh::LeanObject,
    mut v_inst_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_x_1375_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1376_: u8 = 0;
    v___x_1376_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1373_, v_a_1374_, v_x_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___boxed(
    mut v_00_u03b1_1377_: *mut leanh::LeanObject,
    mut v_00_u03b2_1378_: *mut leanh::LeanObject,
    mut v_inst_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_x_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Std_DHashMap_Internal_AssocList_contains(
        v_00_u03b1_1377_,
        v_00_u03b2_1378_,
        v_inst_1379_,
        v_a_1380_,
        v_x_1381_,
    );
    v_r_1383_ = leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_1384_: *mut leanh::LeanObject,
    mut v_h__1_1385_: *mut leanh::LeanObject,
    mut v_h__2_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1384_) == 0 {
        let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1386_);
        v___x_1387_ = leanh::lean_box(0);
        v___x_1388_ = leanh::lean_apply_1(v_h__1_1385_, v___x_1387_);
        return v___x_1388_;
    } else {
        let mut v_key_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1385_);
        v_key_1389_ = leanh::lean_ctor_get(v_x_1384_, 0);
        leanh::lean_inc(v_key_1389_);
        v_value_1390_ = leanh::lean_ctor_get(v_x_1384_, 1);
        leanh::lean_inc(v_value_1390_);
        v_tail_1391_ = leanh::lean_ctor_get(v_x_1384_, 2);
        leanh::lean_inc(v_tail_1391_);
        leanh::lean_dec_ref_known(v_x_1384_, 3);
        v___x_1392_ =
            leanh::lean_apply_3(v_h__2_1386_, v_key_1389_, v_value_1390_, v_tail_1391_);
        return v___x_1392_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_1393_: *mut leanh::LeanObject,
    mut v_00_u03b2_1394_: *mut leanh::LeanObject,
    mut v_motive_1395_: *mut leanh::LeanObject,
    mut v_x_1396_: *mut leanh::LeanObject,
    mut v_h__1_1397_: *mut leanh::LeanObject,
    mut v_h__2_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1396_) == 0 {
        let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1398_);
        v___x_1399_ = leanh::lean_box(0);
        v___x_1400_ = leanh::lean_apply_1(v_h__1_1397_, v___x_1399_);
        return v___x_1400_;
    } else {
        let mut v_key_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1397_);
        v_key_1401_ = leanh::lean_ctor_get(v_x_1396_, 0);
        leanh::lean_inc(v_key_1401_);
        v_value_1402_ = leanh::lean_ctor_get(v_x_1396_, 1);
        leanh::lean_inc(v_value_1402_);
        v_tail_1403_ = leanh::lean_ctor_get(v_x_1396_, 2);
        leanh::lean_inc(v_tail_1403_);
        leanh::lean_dec_ref_known(v_x_1396_, 3);
        v___x_1404_ =
            leanh::lean_apply_3(v_h__2_1398_, v_key_1401_, v_value_1402_, v_tail_1403_);
        return v___x_1404_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___redArg(
    mut v_inst_1405_: *mut leanh::LeanObject,
    mut v_a_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1408_ = leanh::lean_ctor_get(v_x_1407_, 0);
                leanh::lean_inc(v_key_1408_);
                v_value_1409_ = leanh::lean_ctor_get(v_x_1407_, 1);
                leanh::lean_inc(v_value_1409_);
                v_tail_1410_ = leanh::lean_ctor_get(v_x_1407_, 2);
                leanh::lean_inc(v_tail_1410_);
                leanh::lean_dec(v_x_1407_);
                leanh::lean_inc_ref(v_inst_1405_);
                leanh::lean_inc(v_a_1406_);
                v___x_1411_ = leanh::lean_apply_2(v_inst_1405_, v_key_1408_, v_a_1406_);
                v___x_1412_ = (leanh::lean_unbox(v___x_1411_) as u8);
                if v___x_1412_ == 0 {
                    leanh::lean_dec(v_value_1409_);
                    v_x_1407_ = v_tail_1410_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_1410_);
                    leanh::lean_dec(v_a_1406_);
                    leanh::lean_dec_ref(v_inst_1405_);
                    return v_value_1409_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get(
    mut v_00_u03b1_1414_: *mut leanh::LeanObject,
    mut v_00_u03b2_1415_: *mut leanh::LeanObject,
    mut v_inst_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_x_1418_: *mut leanh::LeanObject,
    mut v_x_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1416_, v_a_1417_, v_x_1418_);
    return v___x_1420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast___redArg(
    mut v_inst_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_x_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1424_ = leanh::lean_ctor_get(v_x_1423_, 0);
                leanh::lean_inc(v_key_1424_);
                v_value_1425_ = leanh::lean_ctor_get(v_x_1423_, 1);
                leanh::lean_inc(v_value_1425_);
                v_tail_1426_ = leanh::lean_ctor_get(v_x_1423_, 2);
                leanh::lean_inc(v_tail_1426_);
                leanh::lean_dec(v_x_1423_);
                leanh::lean_inc_ref(v_inst_1421_);
                leanh::lean_inc(v_a_1422_);
                v___x_1427_ = leanh::lean_apply_2(v_inst_1421_, v_key_1424_, v_a_1422_);
                v___x_1428_ = (leanh::lean_unbox(v___x_1427_) as u8);
                if v___x_1428_ == 0 {
                    leanh::lean_dec(v_value_1425_);
                    v_x_1423_ = v_tail_1426_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_1426_);
                    leanh::lean_dec(v_a_1422_);
                    leanh::lean_dec_ref(v_inst_1421_);
                    return v_value_1425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast(
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_00_u03b2_1431_: *mut leanh::LeanObject,
    mut v_inst_1432_: *mut leanh::LeanObject,
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
    mut v_x_1435_: *mut leanh::LeanObject,
    mut v_x_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1432_, v_a_1434_, v_x_1435_);
    return v___x_1437_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry___redArg(
    mut v_inst_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_x_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1441_ = leanh::lean_ctor_get(v_x_1440_, 0);
                leanh::lean_inc_n(v_key_1441_, 2);
                v_value_1442_ = leanh::lean_ctor_get(v_x_1440_, 1);
                leanh::lean_inc(v_value_1442_);
                v_tail_1443_ = leanh::lean_ctor_get(v_x_1440_, 2);
                leanh::lean_inc(v_tail_1443_);
                leanh::lean_dec(v_x_1440_);
                leanh::lean_inc_ref(v_inst_1438_);
                leanh::lean_inc(v_a_1439_);
                v___x_1444_ = leanh::lean_apply_2(v_inst_1438_, v_key_1441_, v_a_1439_);
                v___x_1445_ = (leanh::lean_unbox(v___x_1444_) as u8);
                if v___x_1445_ == 0 {
                    leanh::lean_dec(v_value_1442_);
                    leanh::lean_dec(v_key_1441_);
                    v_x_1440_ = v_tail_1443_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_1443_);
                    leanh::lean_dec(v_a_1439_);
                    leanh::lean_dec_ref(v_inst_1438_);
                    v___x_1447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1447_, 0, v_key_1441_);
                    leanh::lean_ctor_set(v___x_1447_, 1, v_value_1442_);
                    return v___x_1447_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry(
    mut v_00_u03b1_1448_: *mut leanh::LeanObject,
    mut v_00_u03b2_1449_: *mut leanh::LeanObject,
    mut v_inst_1450_: *mut leanh::LeanObject,
    mut v_a_1451_: *mut leanh::LeanObject,
    mut v_x_1452_: *mut leanh::LeanObject,
    mut v_x_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1450_, v_a_1451_, v_x_1452_);
    return v___x_1454_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
    mut v_inst_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_fallback_1457_: *mut leanh::LeanObject,
    mut v_x_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1458_) == 0 {
                    leanh::lean_dec(v_a_1456_);
                    leanh::lean_dec_ref(v_inst_1455_);
                    leanh::lean_inc_ref(v_fallback_1457_);
                    return v_fallback_1457_;
                } else {
                    v_key_1459_ = leanh::lean_ctor_get(v_x_1458_, 0);
                    leanh::lean_inc_n(v_key_1459_, 2);
                    v_value_1460_ = leanh::lean_ctor_get(v_x_1458_, 1);
                    leanh::lean_inc(v_value_1460_);
                    v_tail_1461_ = leanh::lean_ctor_get(v_x_1458_, 2);
                    leanh::lean_inc(v_tail_1461_);
                    leanh::lean_dec_ref_known(v_x_1458_, 3);
                    leanh::lean_inc_ref(v_inst_1455_);
                    leanh::lean_inc(v_a_1456_);
                    v___x_1462_ = leanh::lean_apply_2(v_inst_1455_, v_key_1459_, v_a_1456_);
                    v___x_1463_ = (leanh::lean_unbox(v___x_1462_) as u8);
                    if v___x_1463_ == 0 {
                        leanh::lean_dec(v_value_1460_);
                        leanh::lean_dec(v_key_1459_);
                        v_x_1458_ = v_tail_1461_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1461_);
                        leanh::lean_dec(v_a_1456_);
                        leanh::lean_dec_ref(v_inst_1455_);
                        v___x_1465_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1465_, 0, v_key_1459_);
                        leanh::lean_ctor_set(v___x_1465_, 1, v_value_1460_);
                        return v___x_1465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg___boxed(
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_fallback_1468_: *mut leanh::LeanObject,
    mut v_x_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1466_,
        v_a_1467_,
        v_fallback_1468_,
        v_x_1469_,
    );
    leanh::lean_dec_ref(v_fallback_1468_);
    return v_res_1470_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD(
    mut v_00_u03b1_1471_: *mut leanh::LeanObject,
    mut v_00_u03b2_1472_: *mut leanh::LeanObject,
    mut v_inst_1473_: *mut leanh::LeanObject,
    mut v_a_1474_: *mut leanh::LeanObject,
    mut v_fallback_1475_: *mut leanh::LeanObject,
    mut v_x_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1473_,
        v_a_1474_,
        v_fallback_1475_,
        v_x_1476_,
    );
    return v___x_1477_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___boxed(
    mut v_00_u03b1_1478_: *mut leanh::LeanObject,
    mut v_00_u03b2_1479_: *mut leanh::LeanObject,
    mut v_inst_1480_: *mut leanh::LeanObject,
    mut v_a_1481_: *mut leanh::LeanObject,
    mut v_fallback_1482_: *mut leanh::LeanObject,
    mut v_x_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ = l_Std_DHashMap_Internal_AssocList_getEntryD(
        v_00_u03b1_1478_,
        v_00_u03b2_1479_,
        v_inst_1480_,
        v_a_1481_,
        v_fallback_1482_,
        v_x_1483_,
    );
    leanh::lean_dec_ref(v_fallback_1482_);
    return v_res_1484_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
    mut v_inst_1487_: *mut leanh::LeanObject,
    mut v_x_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1488_) == 0 {
                    leanh::lean_dec(v_a_1486_);
                    leanh::lean_dec_ref(v_inst_1485_);
                    leanh::lean_inc_ref(v_inst_1487_);
                    return v_inst_1487_;
                } else {
                    v_key_1489_ = leanh::lean_ctor_get(v_x_1488_, 0);
                    leanh::lean_inc_n(v_key_1489_, 2);
                    v_value_1490_ = leanh::lean_ctor_get(v_x_1488_, 1);
                    leanh::lean_inc(v_value_1490_);
                    v_tail_1491_ = leanh::lean_ctor_get(v_x_1488_, 2);
                    leanh::lean_inc(v_tail_1491_);
                    leanh::lean_dec_ref_known(v_x_1488_, 3);
                    leanh::lean_inc_ref(v_inst_1485_);
                    leanh::lean_inc(v_a_1486_);
                    v___x_1492_ = leanh::lean_apply_2(v_inst_1485_, v_key_1489_, v_a_1486_);
                    v___x_1493_ = (leanh::lean_unbox(v___x_1492_) as u8);
                    if v___x_1493_ == 0 {
                        leanh::lean_dec(v_value_1490_);
                        leanh::lean_dec(v_key_1489_);
                        v_x_1488_ = v_tail_1491_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1491_);
                        leanh::lean_dec(v_a_1486_);
                        leanh::lean_dec_ref(v_inst_1485_);
                        v___x_1495_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1495_, 0, v_key_1489_);
                        leanh::lean_ctor_set(v___x_1495_, 1, v_value_1490_);
                        return v___x_1495_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg___boxed(
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_a_1497_: *mut leanh::LeanObject,
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_x_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1496_,
        v_a_1497_,
        v_inst_1498_,
        v_x_1499_,
    );
    leanh::lean_dec_ref(v_inst_1498_);
    return v_res_1500_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21(
    mut v_00_u03b1_1501_: *mut leanh::LeanObject,
    mut v_00_u03b2_1502_: *mut leanh::LeanObject,
    mut v_inst_1503_: *mut leanh::LeanObject,
    mut v_a_1504_: *mut leanh::LeanObject,
    mut v_inst_1505_: *mut leanh::LeanObject,
    mut v_x_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1503_,
        v_a_1504_,
        v_inst_1505_,
        v_x_1506_,
    );
    return v___x_1507_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___boxed(
    mut v_00_u03b1_1508_: *mut leanh::LeanObject,
    mut v_00_u03b2_1509_: *mut leanh::LeanObject,
    mut v_inst_1510_: *mut leanh::LeanObject,
    mut v_a_1511_: *mut leanh::LeanObject,
    mut v_inst_1512_: *mut leanh::LeanObject,
    mut v_x_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21(
        v_00_u03b1_1508_,
        v_00_u03b2_1509_,
        v_inst_1510_,
        v_a_1511_,
        v_inst_1512_,
        v_x_1513_,
    );
    leanh::lean_dec_ref(v_inst_1512_);
    return v_res_1514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey___redArg(
    mut v_inst_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_x_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1518_ = leanh::lean_ctor_get(v_x_1517_, 0);
                leanh::lean_inc_n(v_key_1518_, 2);
                v_tail_1519_ = leanh::lean_ctor_get(v_x_1517_, 2);
                leanh::lean_inc(v_tail_1519_);
                leanh::lean_dec(v_x_1517_);
                leanh::lean_inc_ref(v_inst_1515_);
                leanh::lean_inc(v_a_1516_);
                v___x_1520_ = leanh::lean_apply_2(v_inst_1515_, v_key_1518_, v_a_1516_);
                v___x_1521_ = (leanh::lean_unbox(v___x_1520_) as u8);
                if v___x_1521_ == 0 {
                    leanh::lean_dec(v_key_1518_);
                    v_x_1517_ = v_tail_1519_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_1519_);
                    leanh::lean_dec(v_a_1516_);
                    leanh::lean_dec_ref(v_inst_1515_);
                    return v_key_1518_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey(
    mut v_00_u03b1_1523_: *mut leanh::LeanObject,
    mut v_00_u03b2_1524_: *mut leanh::LeanObject,
    mut v_inst_1525_: *mut leanh::LeanObject,
    mut v_a_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_1525_, v_a_1526_, v_x_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1534_ = leanh::lean_unsigned_to_nat(11);
    v___x_1535_ = leanh::lean_unsigned_to_nat(153);
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
    mut v_inst_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_inst_1541_: *mut leanh::LeanObject,
    mut v_x_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1542_) == 0 {
                    leanh::lean_dec(v_a_1540_);
                    leanh::lean_dec_ref(v_inst_1539_);
                    v___x_1543_ = leanh::lean_obj_once(
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
                    v_key_1545_ = leanh::lean_ctor_get(v_x_1542_, 0);
                    leanh::lean_inc(v_key_1545_);
                    v_value_1546_ = leanh::lean_ctor_get(v_x_1542_, 1);
                    leanh::lean_inc(v_value_1546_);
                    v_tail_1547_ = leanh::lean_ctor_get(v_x_1542_, 2);
                    leanh::lean_inc(v_tail_1547_);
                    leanh::lean_dec_ref_known(v_x_1542_, 3);
                    leanh::lean_inc_ref(v_inst_1539_);
                    leanh::lean_inc(v_a_1540_);
                    v___x_1548_ = leanh::lean_apply_2(v_inst_1539_, v_key_1545_, v_a_1540_);
                    v___x_1549_ = (leanh::lean_unbox(v___x_1548_) as u8);
                    if v___x_1549_ == 0 {
                        leanh::lean_dec(v_value_1546_);
                        v_x_1542_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1547_);
                        leanh::lean_dec(v_a_1540_);
                        leanh::lean_dec_ref(v_inst_1539_);
                        return v_value_1546_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___boxed(
    mut v_inst_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: *mut leanh::LeanObject,
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_x_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1551_,
        v_a_1552_,
        v_inst_1553_,
        v_x_1554_,
    );
    leanh::lean_dec(v_inst_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21(
    mut v_00_u03b1_1556_: *mut leanh::LeanObject,
    mut v_00_u03b2_1557_: *mut leanh::LeanObject,
    mut v_inst_1558_: *mut leanh::LeanObject,
    mut v_inst_1559_: *mut leanh::LeanObject,
    mut v_a_1560_: *mut leanh::LeanObject,
    mut v_inst_1561_: *mut leanh::LeanObject,
    mut v_x_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1558_,
        v_a_1560_,
        v_inst_1561_,
        v_x_1562_,
    );
    return v___x_1563_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___boxed(
    mut v_00_u03b1_1564_: *mut leanh::LeanObject,
    mut v_00_u03b2_1565_: *mut leanh::LeanObject,
    mut v_inst_1566_: *mut leanh::LeanObject,
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_inst_1569_: *mut leanh::LeanObject,
    mut v_x_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_getCast_x21(
        v_00_u03b1_1564_,
        v_00_u03b2_1565_,
        v_inst_1566_,
        v_inst_1567_,
        v_a_1568_,
        v_inst_1569_,
        v_x_1570_,
    );
    leanh::lean_dec(v_inst_1569_);
    return v_res_1571_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
    mut v_x_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1574_) == 0 {
                    leanh::lean_dec(v_a_1573_);
                    leanh::lean_dec_ref(v_inst_1572_);
                    v___x_1575_ = leanh::lean_box(0);
                    return v___x_1575_;
                } else {
                    v_key_1576_ = leanh::lean_ctor_get(v_x_1574_, 0);
                    leanh::lean_inc_n(v_key_1576_, 2);
                    v_tail_1577_ = leanh::lean_ctor_get(v_x_1574_, 2);
                    leanh::lean_inc(v_tail_1577_);
                    leanh::lean_dec_ref_known(v_x_1574_, 3);
                    leanh::lean_inc_ref(v_inst_1572_);
                    leanh::lean_inc(v_a_1573_);
                    v___x_1578_ = leanh::lean_apply_2(v_inst_1572_, v_key_1576_, v_a_1573_);
                    v___x_1579_ = (leanh::lean_unbox(v___x_1578_) as u8);
                    if v___x_1579_ == 0 {
                        leanh::lean_dec(v_key_1576_);
                        v_x_1574_ = v_tail_1577_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1577_);
                        leanh::lean_dec(v_a_1573_);
                        leanh::lean_dec_ref(v_inst_1572_);
                        v___x_1581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1581_, 0, v_key_1576_);
                        return v___x_1581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f(
    mut v_00_u03b1_1582_: *mut leanh::LeanObject,
    mut v_00_u03b2_1583_: *mut leanh::LeanObject,
    mut v_inst_1584_: *mut leanh::LeanObject,
    mut v_a_1585_: *mut leanh::LeanObject,
    mut v_x_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_1584_, v_a_1585_, v_x_1586_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1590_ = leanh::lean_unsigned_to_nat(11);
    v___x_1591_ = leanh::lean_unsigned_to_nat(163);
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
    mut v_inst_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
    mut v_x_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1598_) == 0 {
                    leanh::lean_dec(v_a_1597_);
                    leanh::lean_dec_ref(v_inst_1595_);
                    v___x_1599_ = leanh::lean_obj_once(
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
                    v_key_1601_ = leanh::lean_ctor_get(v_x_1598_, 0);
                    leanh::lean_inc(v_key_1601_);
                    v_value_1602_ = leanh::lean_ctor_get(v_x_1598_, 1);
                    leanh::lean_inc(v_value_1602_);
                    v_tail_1603_ = leanh::lean_ctor_get(v_x_1598_, 2);
                    leanh::lean_inc(v_tail_1603_);
                    leanh::lean_dec_ref_known(v_x_1598_, 3);
                    leanh::lean_inc_ref(v_inst_1595_);
                    leanh::lean_inc(v_a_1597_);
                    v___x_1604_ = leanh::lean_apply_2(v_inst_1595_, v_key_1601_, v_a_1597_);
                    v___x_1605_ = (leanh::lean_unbox(v___x_1604_) as u8);
                    if v___x_1605_ == 0 {
                        leanh::lean_dec(v_value_1602_);
                        v_x_1598_ = v_tail_1603_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1603_);
                        leanh::lean_dec(v_a_1597_);
                        leanh::lean_dec_ref(v_inst_1595_);
                        return v_value_1602_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___redArg___boxed(
    mut v_inst_1607_: *mut leanh::LeanObject,
    mut v_inst_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
    mut v_x_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1607_,
        v_inst_1608_,
        v_a_1609_,
        v_x_1610_,
    );
    leanh::lean_dec(v_inst_1608_);
    return v_res_1611_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21(
    mut v_00_u03b1_1612_: *mut leanh::LeanObject,
    mut v_00_u03b2_1613_: *mut leanh::LeanObject,
    mut v_inst_1614_: *mut leanh::LeanObject,
    mut v_inst_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_x_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1614_,
        v_inst_1615_,
        v_a_1616_,
        v_x_1617_,
    );
    return v___x_1618_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___boxed(
    mut v_00_u03b1_1619_: *mut leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut leanh::LeanObject,
    mut v_inst_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v_a_1623_: *mut leanh::LeanObject,
    mut v_x_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Std_DHashMap_Internal_AssocList_get_x21(
        v_00_u03b1_1619_,
        v_00_u03b2_1620_,
        v_inst_1621_,
        v_inst_1622_,
        v_a_1623_,
        v_x_1624_,
    );
    leanh::lean_dec(v_inst_1622_);
    return v_res_1625_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1628_ = leanh::lean_unsigned_to_nat(11);
    v___x_1629_ = leanh::lean_unsigned_to_nat(168);
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
    mut v_inst_1633_: *mut leanh::LeanObject,
    mut v_inst_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1636_) == 0 {
                    leanh::lean_dec(v_a_1635_);
                    leanh::lean_dec_ref(v_inst_1633_);
                    v___x_1637_ = leanh::lean_obj_once(
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
                    v_key_1639_ = leanh::lean_ctor_get(v_x_1636_, 0);
                    leanh::lean_inc_n(v_key_1639_, 2);
                    v_tail_1640_ = leanh::lean_ctor_get(v_x_1636_, 2);
                    leanh::lean_inc(v_tail_1640_);
                    leanh::lean_dec_ref_known(v_x_1636_, 3);
                    leanh::lean_inc_ref(v_inst_1633_);
                    leanh::lean_inc(v_a_1635_);
                    v___x_1641_ = leanh::lean_apply_2(v_inst_1633_, v_key_1639_, v_a_1635_);
                    v___x_1642_ = (leanh::lean_unbox(v___x_1641_) as u8);
                    if v___x_1642_ == 0 {
                        leanh::lean_dec(v_key_1639_);
                        v_x_1636_ = v_tail_1640_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1640_);
                        leanh::lean_dec(v_a_1635_);
                        leanh::lean_dec_ref(v_inst_1633_);
                        return v_key_1639_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___boxed(
    mut v_inst_1644_: *mut leanh::LeanObject,
    mut v_inst_1645_: *mut leanh::LeanObject,
    mut v_a_1646_: *mut leanh::LeanObject,
    mut v_x_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1644_,
        v_inst_1645_,
        v_a_1646_,
        v_x_1647_,
    );
    leanh::lean_dec(v_inst_1645_);
    return v_res_1648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21(
    mut v_00_u03b1_1649_: *mut leanh::LeanObject,
    mut v_00_u03b2_1650_: *mut leanh::LeanObject,
    mut v_inst_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
    mut v_x_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1651_,
        v_inst_1652_,
        v_a_1653_,
        v_x_1654_,
    );
    return v___x_1655_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___boxed(
    mut v_00_u03b1_1656_: *mut leanh::LeanObject,
    mut v_00_u03b2_1657_: *mut leanh::LeanObject,
    mut v_inst_1658_: *mut leanh::LeanObject,
    mut v_inst_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_x_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_DHashMap_Internal_AssocList_getKey_x21(
        v_00_u03b1_1656_,
        v_00_u03b2_1657_,
        v_inst_1658_,
        v_inst_1659_,
        v_a_1660_,
        v_x_1661_,
    );
    leanh::lean_dec(v_inst_1659_);
    return v_res_1662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
    mut v_inst_1663_: *mut leanh::LeanObject,
    mut v_a_1664_: *mut leanh::LeanObject,
    mut v_fallback_1665_: *mut leanh::LeanObject,
    mut v_x_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1666_) == 0 {
                    leanh::lean_dec(v_a_1664_);
                    leanh::lean_dec_ref(v_inst_1663_);
                    leanh::lean_inc(v_fallback_1665_);
                    return v_fallback_1665_;
                } else {
                    v_key_1667_ = leanh::lean_ctor_get(v_x_1666_, 0);
                    leanh::lean_inc(v_key_1667_);
                    v_value_1668_ = leanh::lean_ctor_get(v_x_1666_, 1);
                    leanh::lean_inc(v_value_1668_);
                    v_tail_1669_ = leanh::lean_ctor_get(v_x_1666_, 2);
                    leanh::lean_inc(v_tail_1669_);
                    leanh::lean_dec_ref_known(v_x_1666_, 3);
                    leanh::lean_inc_ref(v_inst_1663_);
                    leanh::lean_inc(v_a_1664_);
                    v___x_1670_ = leanh::lean_apply_2(v_inst_1663_, v_key_1667_, v_a_1664_);
                    v___x_1671_ = (leanh::lean_unbox(v___x_1670_) as u8);
                    if v___x_1671_ == 0 {
                        leanh::lean_dec(v_value_1668_);
                        v_x_1666_ = v_tail_1669_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1669_);
                        leanh::lean_dec(v_a_1664_);
                        leanh::lean_dec_ref(v_inst_1663_);
                        return v_value_1668_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg___boxed(
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_a_1674_: *mut leanh::LeanObject,
    mut v_fallback_1675_: *mut leanh::LeanObject,
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1673_,
        v_a_1674_,
        v_fallback_1675_,
        v_x_1676_,
    );
    leanh::lean_dec(v_fallback_1675_);
    return v_res_1677_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD(
    mut v_00_u03b1_1678_: *mut leanh::LeanObject,
    mut v_00_u03b2_1679_: *mut leanh::LeanObject,
    mut v_inst_1680_: *mut leanh::LeanObject,
    mut v_inst_1681_: *mut leanh::LeanObject,
    mut v_a_1682_: *mut leanh::LeanObject,
    mut v_fallback_1683_: *mut leanh::LeanObject,
    mut v_x_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1680_,
        v_a_1682_,
        v_fallback_1683_,
        v_x_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___boxed(
    mut v_00_u03b1_1686_: *mut leanh::LeanObject,
    mut v_00_u03b2_1687_: *mut leanh::LeanObject,
    mut v_inst_1688_: *mut leanh::LeanObject,
    mut v_inst_1689_: *mut leanh::LeanObject,
    mut v_a_1690_: *mut leanh::LeanObject,
    mut v_fallback_1691_: *mut leanh::LeanObject,
    mut v_x_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Std_DHashMap_Internal_AssocList_getCastD(
        v_00_u03b1_1686_,
        v_00_u03b2_1687_,
        v_inst_1688_,
        v_inst_1689_,
        v_a_1690_,
        v_fallback_1691_,
        v_x_1692_,
    );
    leanh::lean_dec(v_fallback_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg(
    mut v_inst_1694_: *mut leanh::LeanObject,
    mut v_a_1695_: *mut leanh::LeanObject,
    mut v_fallback_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1697_) == 0 {
                    leanh::lean_dec(v_a_1695_);
                    leanh::lean_dec_ref(v_inst_1694_);
                    leanh::lean_inc(v_fallback_1696_);
                    return v_fallback_1696_;
                } else {
                    v_key_1698_ = leanh::lean_ctor_get(v_x_1697_, 0);
                    leanh::lean_inc(v_key_1698_);
                    v_value_1699_ = leanh::lean_ctor_get(v_x_1697_, 1);
                    leanh::lean_inc(v_value_1699_);
                    v_tail_1700_ = leanh::lean_ctor_get(v_x_1697_, 2);
                    leanh::lean_inc(v_tail_1700_);
                    leanh::lean_dec_ref_known(v_x_1697_, 3);
                    leanh::lean_inc_ref(v_inst_1694_);
                    leanh::lean_inc(v_a_1695_);
                    v___x_1701_ = leanh::lean_apply_2(v_inst_1694_, v_key_1698_, v_a_1695_);
                    v___x_1702_ = (leanh::lean_unbox(v___x_1701_) as u8);
                    if v___x_1702_ == 0 {
                        leanh::lean_dec(v_value_1699_);
                        v_x_1697_ = v_tail_1700_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1700_);
                        leanh::lean_dec(v_a_1695_);
                        leanh::lean_dec_ref(v_inst_1694_);
                        return v_value_1699_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg___boxed(
    mut v_inst_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_fallback_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1704_,
        v_a_1705_,
        v_fallback_1706_,
        v_x_1707_,
    );
    leanh::lean_dec(v_fallback_1706_);
    return v_res_1708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD(
    mut v_00_u03b1_1709_: *mut leanh::LeanObject,
    mut v_00_u03b2_1710_: *mut leanh::LeanObject,
    mut v_inst_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_fallback_1713_: *mut leanh::LeanObject,
    mut v_x_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1711_,
        v_a_1712_,
        v_fallback_1713_,
        v_x_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___boxed(
    mut v_00_u03b1_1716_: *mut leanh::LeanObject,
    mut v_00_u03b2_1717_: *mut leanh::LeanObject,
    mut v_inst_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
    mut v_fallback_1720_: *mut leanh::LeanObject,
    mut v_x_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Std_DHashMap_Internal_AssocList_getD(
        v_00_u03b1_1716_,
        v_00_u03b2_1717_,
        v_inst_1718_,
        v_a_1719_,
        v_fallback_1720_,
        v_x_1721_,
    );
    leanh::lean_dec(v_fallback_1720_);
    return v_res_1722_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
    mut v_inst_1723_: *mut leanh::LeanObject,
    mut v_a_1724_: *mut leanh::LeanObject,
    mut v_fallback_1725_: *mut leanh::LeanObject,
    mut v_x_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1726_) == 0 {
                    leanh::lean_dec(v_a_1724_);
                    leanh::lean_dec_ref(v_inst_1723_);
                    leanh::lean_inc(v_fallback_1725_);
                    return v_fallback_1725_;
                } else {
                    v_key_1727_ = leanh::lean_ctor_get(v_x_1726_, 0);
                    leanh::lean_inc_n(v_key_1727_, 2);
                    v_tail_1728_ = leanh::lean_ctor_get(v_x_1726_, 2);
                    leanh::lean_inc(v_tail_1728_);
                    leanh::lean_dec_ref_known(v_x_1726_, 3);
                    leanh::lean_inc_ref(v_inst_1723_);
                    leanh::lean_inc(v_a_1724_);
                    v___x_1729_ = leanh::lean_apply_2(v_inst_1723_, v_key_1727_, v_a_1724_);
                    v___x_1730_ = (leanh::lean_unbox(v___x_1729_) as u8);
                    if v___x_1730_ == 0 {
                        leanh::lean_dec(v_key_1727_);
                        v_x_1726_ = v_tail_1728_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1728_);
                        leanh::lean_dec(v_a_1724_);
                        leanh::lean_dec_ref(v_inst_1723_);
                        return v_key_1727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg___boxed(
    mut v_inst_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
    mut v_fallback_1734_: *mut leanh::LeanObject,
    mut v_x_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1732_,
        v_a_1733_,
        v_fallback_1734_,
        v_x_1735_,
    );
    leanh::lean_dec(v_fallback_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD(
    mut v_00_u03b1_1737_: *mut leanh::LeanObject,
    mut v_00_u03b2_1738_: *mut leanh::LeanObject,
    mut v_inst_1739_: *mut leanh::LeanObject,
    mut v_a_1740_: *mut leanh::LeanObject,
    mut v_fallback_1741_: *mut leanh::LeanObject,
    mut v_x_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1739_,
        v_a_1740_,
        v_fallback_1741_,
        v_x_1742_,
    );
    return v___x_1743_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___boxed(
    mut v_00_u03b1_1744_: *mut leanh::LeanObject,
    mut v_00_u03b2_1745_: *mut leanh::LeanObject,
    mut v_inst_1746_: *mut leanh::LeanObject,
    mut v_a_1747_: *mut leanh::LeanObject,
    mut v_fallback_1748_: *mut leanh::LeanObject,
    mut v_x_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Std_DHashMap_Internal_AssocList_getKeyD(
        v_00_u03b1_1744_,
        v_00_u03b2_1745_,
        v_inst_1746_,
        v_a_1747_,
        v_fallback_1748_,
        v_x_1749_,
    );
    leanh::lean_dec(v_fallback_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___redArg(
    mut v_inst_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_b_1753_: *mut leanh::LeanObject,
    mut v_x_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1754_) == 0 {
                    leanh::lean_dec(v_b_1753_);
                    leanh::lean_dec(v_a_1752_);
                    leanh::lean_dec_ref(v_inst_1751_);
                    return v_x_1754_;
                } else {
                    v_key_1755_ = leanh::lean_ctor_get(v_x_1754_, 0);
                    v_value_1756_ = leanh::lean_ctor_get(v_x_1754_, 1);
                    v_tail_1757_ = leanh::lean_ctor_get(v_x_1754_, 2);
                    v_isSharedCheck_1770_ = (!leanh::lean_is_exclusive(v_x_1754_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1759_ = v_x_1754_;
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1757_);
                        leanh::lean_inc(v_value_1756_);
                        leanh::lean_inc(v_key_1755_);
                        leanh::lean_dec(v_x_1754_);
                        v___x_1759_ = leanh::lean_box(0);
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1751_);
                leanh::lean_inc(v_a_1752_);
                leanh::lean_inc(v_key_1755_);
                v___x_1761_ = leanh::lean_apply_2(v_inst_1751_, v_key_1755_, v_a_1752_);
                v___x_1762_ = (leanh::lean_unbox(v___x_1761_) as u8);
                if v___x_1762_ == 0 {
                    v___x_1763_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_1751_,
                        v_a_1752_,
                        v_b_1753_,
                        v_tail_1757_,
                    );
                    if v_isShared_1760_ == 0 {
                        leanh::lean_ctor_set(v___x_1759_, 2, v___x_1763_);
                        v___x_1765_ = v___x_1759_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_key_1755_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_value_1756_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 2, v___x_1763_);
                        v___x_1765_ = v_reuseFailAlloc_1766_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1756_);
                    leanh::lean_dec(v_key_1755_);
                    leanh::lean_dec_ref(v_inst_1751_);
                    if v_isShared_1760_ == 0 {
                        leanh::lean_ctor_set(v___x_1759_, 1, v_b_1753_);
                        leanh::lean_ctor_set(v___x_1759_, 0, v_a_1752_);
                        v___x_1768_ = v___x_1759_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1752_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_b_1753_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_tail_1757_);
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
    mut v_00_u03b1_1771_: *mut leanh::LeanObject,
    mut v_00_u03b2_1772_: *mut leanh::LeanObject,
    mut v_inst_1773_: *mut leanh::LeanObject,
    mut v_a_1774_: *mut leanh::LeanObject,
    mut v_b_1775_: *mut leanh::LeanObject,
    mut v_x_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
        v_inst_1773_,
        v_a_1774_,
        v_b_1775_,
        v_x_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___redArg(
    mut v_inst_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
    mut v_x_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1780_) == 0 {
                    leanh::lean_dec(v_a_1779_);
                    leanh::lean_dec_ref(v_inst_1778_);
                    return v_x_1780_;
                } else {
                    v_key_1781_ = leanh::lean_ctor_get(v_x_1780_, 0);
                    v_value_1782_ = leanh::lean_ctor_get(v_x_1780_, 1);
                    v_tail_1783_ = leanh::lean_ctor_get(v_x_1780_, 2);
                    v_isSharedCheck_1793_ = (!leanh::lean_is_exclusive(v_x_1780_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1785_ = v_x_1780_;
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1783_);
                        leanh::lean_inc(v_value_1782_);
                        leanh::lean_inc(v_key_1781_);
                        leanh::lean_dec(v_x_1780_);
                        v___x_1785_ = leanh::lean_box(0);
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1778_);
                leanh::lean_inc(v_a_1779_);
                leanh::lean_inc(v_key_1781_);
                v___x_1787_ = leanh::lean_apply_2(v_inst_1778_, v_key_1781_, v_a_1779_);
                v___x_1788_ = (leanh::lean_unbox(v___x_1787_) as u8);
                if v___x_1788_ == 0 {
                    v___x_1789_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(
                        v_inst_1778_,
                        v_a_1779_,
                        v_tail_1783_,
                    );
                    if v_isShared_1786_ == 0 {
                        leanh::lean_ctor_set(v___x_1785_, 2, v___x_1789_);
                        v___x_1791_ = v___x_1785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1792_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_key_1781_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_value_1782_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1789_);
                        v___x_1791_ = v_reuseFailAlloc_1792_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1785_);
                    leanh::lean_dec(v_value_1782_);
                    leanh::lean_dec(v_key_1781_);
                    leanh::lean_dec(v_a_1779_);
                    leanh::lean_dec_ref(v_inst_1778_);
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
    mut v_00_u03b1_1794_: *mut leanh::LeanObject,
    mut v_00_u03b2_1795_: *mut leanh::LeanObject,
    mut v_inst_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_x_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ =
        l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_1796_, v_a_1797_, v_x_1798_);
    return v___x_1799_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_modify___redArg(
    mut v_inst_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
    mut v_f_1802_: *mut leanh::LeanObject,
    mut v_x_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1803_) == 0 {
                    leanh::lean_dec(v_f_1802_);
                    leanh::lean_dec(v_a_1801_);
                    leanh::lean_dec_ref(v_inst_1800_);
                    return v_x_1803_;
                } else {
                    v_key_1804_ = leanh::lean_ctor_get(v_x_1803_, 0);
                    v_value_1805_ = leanh::lean_ctor_get(v_x_1803_, 1);
                    v_tail_1806_ = leanh::lean_ctor_get(v_x_1803_, 2);
                    v_isSharedCheck_1820_ = (!leanh::lean_is_exclusive(v_x_1803_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1808_ = v_x_1803_;
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1806_);
                        leanh::lean_inc(v_value_1805_);
                        leanh::lean_inc(v_key_1804_);
                        leanh::lean_dec(v_x_1803_);
                        v___x_1808_ = leanh::lean_box(0);
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1800_);
                leanh::lean_inc(v_a_1801_);
                leanh::lean_inc(v_key_1804_);
                v___x_1810_ = leanh::lean_apply_2(v_inst_1800_, v_key_1804_, v_a_1801_);
                v___x_1811_ = (leanh::lean_unbox(v___x_1810_) as u8);
                if v___x_1811_ == 0 {
                    v___x_1812_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
                        v_inst_1800_,
                        v_a_1801_,
                        v_f_1802_,
                        v_tail_1806_,
                    );
                    if v_isShared_1809_ == 0 {
                        leanh::lean_ctor_set(v___x_1808_, 2, v___x_1812_);
                        v___x_1814_ = v___x_1808_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1815_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_key_1804_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_value_1805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 2, v___x_1812_);
                        v___x_1814_ = v_reuseFailAlloc_1815_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_1804_);
                    leanh::lean_dec_ref(v_inst_1800_);
                    v_b_1816_ = leanh::lean_apply_1(v_f_1802_, v_value_1805_);
                    if v_isShared_1809_ == 0 {
                        leanh::lean_ctor_set(v___x_1808_, 1, v_b_1816_);
                        leanh::lean_ctor_set(v___x_1808_, 0, v_a_1801_);
                        v___x_1818_ = v___x_1808_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1819_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1801_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_b_1816_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_tail_1806_);
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
    mut v_00_u03b1_1821_: *mut leanh::LeanObject,
    mut v_00_u03b2_1822_: *mut leanh::LeanObject,
    mut v_inst_1823_: *mut leanh::LeanObject,
    mut v_inst_1824_: *mut leanh::LeanObject,
    mut v_a_1825_: *mut leanh::LeanObject,
    mut v_f_1826_: *mut leanh::LeanObject,
    mut v_x_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
        v_inst_1823_,
        v_a_1825_,
        v_f_1826_,
        v_x_1827_,
    );
    return v___x_1828_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_alter___redArg(
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_a_1830_: *mut leanh::LeanObject,
    mut v_f_1831_: *mut leanh::LeanObject,
    mut v_x_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v_tail_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1832_) == 0 {
                    leanh::lean_dec_ref(v_inst_1829_);
                    v___x_1833_ = leanh::lean_box(0);
                    v___x_1834_ = leanh::lean_apply_1(v_f_1831_, v___x_1833_);
                    if leanh::lean_obj_tag(v___x_1834_) == 0 {
                        leanh::lean_dec(v_a_1830_);
                        return v_x_1832_;
                    } else {
                        v_val_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                        leanh::lean_inc(v_val_1835_);
                        leanh::lean_dec_ref_known(v___x_1834_, 1);
                        v___x_1836_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1836_, 0, v_a_1830_);
                        leanh::lean_ctor_set(v___x_1836_, 1, v_val_1835_);
                        leanh::lean_ctor_set(v___x_1836_, 2, v_x_1832_);
                        return v___x_1836_;
                    }
                } else {
                    v_key_1837_ = leanh::lean_ctor_get(v_x_1832_, 0);
                    v_value_1838_ = leanh::lean_ctor_get(v_x_1832_, 1);
                    v_tail_1839_ = leanh::lean_ctor_get(v_x_1832_, 2);
                    v_isSharedCheck_1855_ = (!leanh::lean_is_exclusive(v_x_1832_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1841_ = v_x_1832_;
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1839_);
                        leanh::lean_inc(v_value_1838_);
                        leanh::lean_inc(v_key_1837_);
                        leanh::lean_dec(v_x_1832_);
                        v___x_1841_ = leanh::lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1829_);
                leanh::lean_inc(v_a_1830_);
                leanh::lean_inc(v_key_1837_);
                v___x_1843_ = leanh::lean_apply_2(v_inst_1829_, v_key_1837_, v_a_1830_);
                v___x_1844_ = (leanh::lean_unbox(v___x_1843_) as u8);
                if v___x_1844_ == 0 {
                    v_tail_1845_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
                        v_inst_1829_,
                        v_a_1830_,
                        v_f_1831_,
                        v_tail_1839_,
                    );
                    if v_isShared_1842_ == 0 {
                        leanh::lean_ctor_set(v___x_1841_, 2, v_tail_1845_);
                        v___x_1847_ = v___x_1841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1848_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_key_1837_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_value_1838_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_tail_1845_);
                        v___x_1847_ = v_reuseFailAlloc_1848_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_1837_);
                    leanh::lean_dec_ref(v_inst_1829_);
                    v___x_1849_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1849_, 0, v_value_1838_);
                    v___x_1850_ = leanh::lean_apply_1(v_f_1831_, v___x_1849_);
                    if leanh::lean_obj_tag(v___x_1850_) == 0 {
                        leanh::lean_del_object(v___x_1841_);
                        leanh::lean_dec(v_a_1830_);
                        return v_tail_1839_;
                    } else {
                        v_val_1851_ = leanh::lean_ctor_get(v___x_1850_, 0);
                        leanh::lean_inc(v_val_1851_);
                        leanh::lean_dec_ref_known(v___x_1850_, 1);
                        if v_isShared_1842_ == 0 {
                            leanh::lean_ctor_set(v___x_1841_, 1, v_val_1851_);
                            leanh::lean_ctor_set(v___x_1841_, 0, v_a_1830_);
                            v___x_1853_ = v___x_1841_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1854_ =
                                leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1830_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_val_1851_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_tail_1839_);
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
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_00_u03b2_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
    mut v_f_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
        v_inst_1858_,
        v_a_1860_,
        v_f_1861_,
        v_x_1862_,
    );
    return v___x_1863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
    mut v_inst_1864_: *mut leanh::LeanObject,
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_f_1866_: *mut leanh::LeanObject,
    mut v_x_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1867_) == 0 {
                    leanh::lean_dec(v_f_1866_);
                    leanh::lean_dec(v_a_1865_);
                    leanh::lean_dec_ref(v_inst_1864_);
                    return v_x_1867_;
                } else {
                    v_key_1868_ = leanh::lean_ctor_get(v_x_1867_, 0);
                    v_value_1869_ = leanh::lean_ctor_get(v_x_1867_, 1);
                    v_tail_1870_ = leanh::lean_ctor_get(v_x_1867_, 2);
                    v_isSharedCheck_1884_ = (!leanh::lean_is_exclusive(v_x_1867_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1872_ = v_x_1867_;
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1870_);
                        leanh::lean_inc(v_value_1869_);
                        leanh::lean_inc(v_key_1868_);
                        leanh::lean_dec(v_x_1867_);
                        v___x_1872_ = leanh::lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1864_);
                leanh::lean_inc(v_a_1865_);
                leanh::lean_inc(v_key_1868_);
                v___x_1874_ = leanh::lean_apply_2(v_inst_1864_, v_key_1868_, v_a_1865_);
                v___x_1875_ = (leanh::lean_unbox(v___x_1874_) as u8);
                if v___x_1875_ == 0 {
                    v___x_1876_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
                        v_inst_1864_,
                        v_a_1865_,
                        v_f_1866_,
                        v_tail_1870_,
                    );
                    if v_isShared_1873_ == 0 {
                        leanh::lean_ctor_set(v___x_1872_, 2, v___x_1876_);
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_key_1868_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_value_1869_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 2, v___x_1876_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_1868_);
                    leanh::lean_dec_ref(v_inst_1864_);
                    v___x_1880_ = leanh::lean_apply_1(v_f_1866_, v_value_1869_);
                    if v_isShared_1873_ == 0 {
                        leanh::lean_ctor_set(v___x_1872_, 1, v___x_1880_);
                        leanh::lean_ctor_set(v___x_1872_, 0, v_a_1865_);
                        v___x_1882_ = v___x_1872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1883_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1865_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_tail_1870_);
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
    mut v_00_u03b1_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_00_u03b2_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_f_1889_: *mut leanh::LeanObject,
    mut v_x_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
        v_inst_1886_,
        v_a_1888_,
        v_f_1889_,
        v_x_1890_,
    );
    return v___x_1891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
    mut v_inst_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_f_1894_: *mut leanh::LeanObject,
    mut v_x_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_tail_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1895_) == 0 {
                    leanh::lean_dec_ref(v_inst_1892_);
                    v___x_1896_ = leanh::lean_box(0);
                    v___x_1897_ = leanh::lean_apply_1(v_f_1894_, v___x_1896_);
                    if leanh::lean_obj_tag(v___x_1897_) == 0 {
                        leanh::lean_dec(v_a_1893_);
                        return v_x_1895_;
                    } else {
                        v_val_1898_ = leanh::lean_ctor_get(v___x_1897_, 0);
                        leanh::lean_inc(v_val_1898_);
                        leanh::lean_dec_ref_known(v___x_1897_, 1);
                        v___x_1899_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1899_, 0, v_a_1893_);
                        leanh::lean_ctor_set(v___x_1899_, 1, v_val_1898_);
                        leanh::lean_ctor_set(v___x_1899_, 2, v_x_1895_);
                        return v___x_1899_;
                    }
                } else {
                    v_key_1900_ = leanh::lean_ctor_get(v_x_1895_, 0);
                    v_value_1901_ = leanh::lean_ctor_get(v_x_1895_, 1);
                    v_tail_1902_ = leanh::lean_ctor_get(v_x_1895_, 2);
                    v_isSharedCheck_1918_ = (!leanh::lean_is_exclusive(v_x_1895_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1904_ = v_x_1895_;
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1902_);
                        leanh::lean_inc(v_value_1901_);
                        leanh::lean_inc(v_key_1900_);
                        leanh::lean_dec(v_x_1895_);
                        v___x_1904_ = leanh::lean_box(0);
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1892_);
                leanh::lean_inc(v_a_1893_);
                leanh::lean_inc(v_key_1900_);
                v___x_1906_ = leanh::lean_apply_2(v_inst_1892_, v_key_1900_, v_a_1893_);
                v___x_1907_ = (leanh::lean_unbox(v___x_1906_) as u8);
                if v___x_1907_ == 0 {
                    v_tail_1908_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
                        v_inst_1892_,
                        v_a_1893_,
                        v_f_1894_,
                        v_tail_1902_,
                    );
                    if v_isShared_1905_ == 0 {
                        leanh::lean_ctor_set(v___x_1904_, 2, v_tail_1908_);
                        v___x_1910_ = v___x_1904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1911_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_key_1900_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_value_1901_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_tail_1908_);
                        v___x_1910_ = v_reuseFailAlloc_1911_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_1900_);
                    leanh::lean_dec_ref(v_inst_1892_);
                    v___x_1912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1912_, 0, v_value_1901_);
                    v___x_1913_ = leanh::lean_apply_1(v_f_1894_, v___x_1912_);
                    if leanh::lean_obj_tag(v___x_1913_) == 0 {
                        leanh::lean_del_object(v___x_1904_);
                        leanh::lean_dec(v_a_1893_);
                        return v_tail_1902_;
                    } else {
                        v_val_1914_ = leanh::lean_ctor_get(v___x_1913_, 0);
                        leanh::lean_inc(v_val_1914_);
                        leanh::lean_dec_ref_known(v___x_1913_, 1);
                        if v_isShared_1905_ == 0 {
                            leanh::lean_ctor_set(v___x_1904_, 1, v_val_1914_);
                            leanh::lean_ctor_set(v___x_1904_, 0, v_a_1893_);
                            v___x_1916_ = v___x_1904_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1917_ =
                                leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1893_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_val_1914_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_tail_1902_);
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
    mut v_00_u03b1_1919_: *mut leanh::LeanObject,
    mut v_inst_1920_: *mut leanh::LeanObject,
    mut v_00_u03b2_1921_: *mut leanh::LeanObject,
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_f_1923_: *mut leanh::LeanObject,
    mut v_x_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
        v_inst_1920_,
        v_a_1922_,
        v_f_1923_,
        v_x_1924_,
    );
    return v___x_1925_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(
    mut v_f_1926_: *mut leanh::LeanObject,
    mut v_acc_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1928_) == 0 {
                    leanh::lean_dec_ref(v_f_1926_);
                    return v_acc_1927_;
                } else {
                    v_key_1929_ = leanh::lean_ctor_get(v_a_1928_, 0);
                    v_value_1930_ = leanh::lean_ctor_get(v_a_1928_, 1);
                    v_tail_1931_ = leanh::lean_ctor_get(v_a_1928_, 2);
                    v_isSharedCheck_1942_ = (!leanh::lean_is_exclusive(v_a_1928_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1933_ = v_a_1928_;
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1931_);
                        leanh::lean_inc(v_value_1930_);
                        leanh::lean_inc(v_key_1929_);
                        leanh::lean_dec(v_a_1928_);
                        v___x_1933_ = leanh::lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_f_1926_);
                leanh::lean_inc(v_key_1929_);
                v___x_1935_ = leanh::lean_apply_2(v_f_1926_, v_key_1929_, v_value_1930_);
                if leanh::lean_obj_tag(v___x_1935_) == 0 {
                    leanh::lean_del_object(v___x_1933_);
                    leanh::lean_dec(v_key_1929_);
                    v_a_1928_ = v_tail_1931_;
                    state = 0;
                    continue;
                } else {
                    v_val_1937_ = leanh::lean_ctor_get(v___x_1935_, 0);
                    leanh::lean_inc(v_val_1937_);
                    leanh::lean_dec_ref_known(v___x_1935_, 1);
                    if v_isShared_1934_ == 0 {
                        leanh::lean_ctor_set(v___x_1933_, 2, v_acc_1927_);
                        leanh::lean_ctor_set(v___x_1933_, 1, v_val_1937_);
                        v___x_1939_ = v___x_1933_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1941_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_key_1929_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_val_1937_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_acc_1927_);
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
    mut v_00_u03b1_1943_: *mut leanh::LeanObject,
    mut v_00_u03b2_1944_: *mut leanh::LeanObject,
    mut v_00_u03b3_1945_: *mut leanh::LeanObject,
    mut v_f_1946_: *mut leanh::LeanObject,
    mut v_acc_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1946_, v_acc_1947_, v_a_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap___redArg(
    mut v_f_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = leanh::lean_box(0);
    v___x_1953_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1950_, v___x_1952_, v_a_1951_);
    return v___x_1953_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap(
    mut v_00_u03b1_1954_: *mut leanh::LeanObject,
    mut v_00_u03b2_1955_: *mut leanh::LeanObject,
    mut v_00_u03b3_1956_: *mut leanh::LeanObject,
    mut v_f_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = leanh::lean_box(0);
    v___x_1960_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1957_, v___x_1959_, v_a_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(
    mut v_f_1961_: *mut leanh::LeanObject,
    mut v_acc_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1963_) == 0 {
                    leanh::lean_dec(v_f_1961_);
                    return v_acc_1962_;
                } else {
                    v_key_1964_ = leanh::lean_ctor_get(v_a_1963_, 0);
                    v_value_1965_ = leanh::lean_ctor_get(v_a_1963_, 1);
                    v_tail_1966_ = leanh::lean_ctor_get(v_a_1963_, 2);
                    v_isSharedCheck_1975_ = (!leanh::lean_is_exclusive(v_a_1963_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1968_ = v_a_1963_;
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1966_);
                        leanh::lean_inc(v_value_1965_);
                        leanh::lean_inc(v_key_1964_);
                        leanh::lean_dec(v_a_1963_);
                        v___x_1968_ = leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_f_1961_);
                leanh::lean_inc(v_key_1964_);
                v___x_1970_ = leanh::lean_apply_2(v_f_1961_, v_key_1964_, v_value_1965_);
                if v_isShared_1969_ == 0 {
                    leanh::lean_ctor_set(v___x_1968_, 2, v_acc_1962_);
                    leanh::lean_ctor_set(v___x_1968_, 1, v___x_1970_);
                    v___x_1972_ = v___x_1968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_key_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_acc_1962_);
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
    mut v_00_u03b1_1976_: *mut leanh::LeanObject,
    mut v_00_u03b2_1977_: *mut leanh::LeanObject,
    mut v_00_u03b3_1978_: *mut leanh::LeanObject,
    mut v_f_1979_: *mut leanh::LeanObject,
    mut v_acc_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1979_, v_acc_1980_, v_a_1981_);
    return v___x_1982_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map___redArg(
    mut v_f_1983_: *mut leanh::LeanObject,
    mut v_a_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1985_ = leanh::lean_box(0);
    v___x_1986_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1983_, v___x_1985_, v_a_1984_);
    return v___x_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map(
    mut v_00_u03b1_1987_: *mut leanh::LeanObject,
    mut v_00_u03b2_1988_: *mut leanh::LeanObject,
    mut v_00_u03b3_1989_: *mut leanh::LeanObject,
    mut v_f_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = leanh::lean_box(0);
    v___x_1993_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1990_, v___x_1992_, v_a_1991_);
    return v___x_1993_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(
    mut v_f_1994_: *mut leanh::LeanObject,
    mut v_acc_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1996_) == 0 {
                    leanh::lean_dec_ref(v_f_1994_);
                    return v_acc_1995_;
                } else {
                    v_key_1997_ = leanh::lean_ctor_get(v_a_1996_, 0);
                    v_value_1998_ = leanh::lean_ctor_get(v_a_1996_, 1);
                    v_tail_1999_ = leanh::lean_ctor_get(v_a_1996_, 2);
                    v_isSharedCheck_2010_ = (!leanh::lean_is_exclusive(v_a_1996_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2001_ = v_a_1996_;
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1999_);
                        leanh::lean_inc(v_value_1998_);
                        leanh::lean_inc(v_key_1997_);
                        leanh::lean_dec(v_a_1996_);
                        v___x_2001_ = leanh::lean_box(0);
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_f_1994_);
                leanh::lean_inc(v_value_1998_);
                leanh::lean_inc(v_key_1997_);
                v___x_2003_ = leanh::lean_apply_2(v_f_1994_, v_key_1997_, v_value_1998_);
                v___x_2004_ = (leanh::lean_unbox(v___x_2003_) as u8);
                if v___x_2004_ == 0 {
                    leanh::lean_del_object(v___x_2001_);
                    leanh::lean_dec(v_value_1998_);
                    leanh::lean_dec(v_key_1997_);
                    v_a_1996_ = v_tail_1999_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2002_ == 0 {
                        leanh::lean_ctor_set(v___x_2001_, 2, v_acc_1995_);
                        v___x_2007_ = v___x_2001_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2009_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_key_1997_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_value_1998_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_acc_1995_);
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
    mut v_00_u03b1_2011_: *mut leanh::LeanObject,
    mut v_00_u03b2_2012_: *mut leanh::LeanObject,
    mut v_f_2013_: *mut leanh::LeanObject,
    mut v_acc_2014_: *mut leanh::LeanObject,
    mut v_a_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2013_, v_acc_2014_, v_a_2015_);
    return v___x_2016_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter___redArg(
    mut v_f_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = leanh::lean_box(0);
    v___x_2020_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2017_, v___x_2019_, v_a_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter(
    mut v_00_u03b1_2021_: *mut leanh::LeanObject,
    mut v_00_u03b2_2022_: *mut leanh::LeanObject,
    mut v_f_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = leanh::lean_box(0);
    v___x_2026_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2023_, v___x_2025_, v_a_2024_);
    return v___x_2026_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
}