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
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_foldl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(
    mut v_x_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1014_) == 0 {
        let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1015_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1015_;
    } else {
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1016_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1016_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg___boxed(
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1017_);
    crate::leanh::lean_dec(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx(
    mut v_00_u03b1_1019_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1020_: *mut crate::leanh::LeanObject,
    mut v_x_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1022_ = l_Std_DHashMap_Internal_AssocList_ctorIdx___redArg(v_x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorIdx___boxed(
    mut v_00_u03b1_1023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1024_: *mut crate::leanh::LeanObject,
    mut v_x_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ =
        l_Std_DHashMap_Internal_AssocList_ctorIdx(v_00_u03b1_1023_, v_00_u03b2_1024_, v_x_1025_);
    crate::leanh::lean_dec(v_x_1025_);
    return v_res_1026_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(
    mut v_t_1027_: *mut crate::leanh::LeanObject,
    mut v_k_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1027_) == 0 {
        return v_k_1028_;
    } else {
        let mut v_key_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_1029_ = crate::leanh::lean_ctor_get(v_t_1027_, 0);
        crate::leanh::lean_inc(v_key_1029_);
        v_value_1030_ = crate::leanh::lean_ctor_get(v_t_1027_, 1);
        crate::leanh::lean_inc(v_value_1030_);
        v_tail_1031_ = crate::leanh::lean_ctor_get(v_t_1027_, 2);
        crate::leanh::lean_inc(v_tail_1031_);
        crate::leanh::lean_dec_ref_known(v_t_1027_, 3);
        v___x_1032_ =
            crate::leanh::lean_apply_3(v_k_1028_, v_key_1029_, v_value_1030_, v_tail_1031_);
        return v___x_1032_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim(
    mut v_00_u03b1_1033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut crate::leanh::LeanObject,
    mut v_motive_1035_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1036_: *mut crate::leanh::LeanObject,
    mut v_t_1037_: *mut crate::leanh::LeanObject,
    mut v_h_1038_: *mut crate::leanh::LeanObject,
    mut v_k_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1037_, v_k_1039_);
    return v___x_1040_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_ctorElim___boxed(
    mut v_00_u03b1_1041_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1042_: *mut crate::leanh::LeanObject,
    mut v_motive_1043_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1044_: *mut crate::leanh::LeanObject,
    mut v_t_1045_: *mut crate::leanh::LeanObject,
    mut v_h_1046_: *mut crate::leanh::LeanObject,
    mut v_k_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_DHashMap_Internal_AssocList_ctorElim(
        v_00_u03b1_1041_,
        v_00_u03b2_1042_,
        v_motive_1043_,
        v_ctorIdx_1044_,
        v_t_1045_,
        v_h_1046_,
        v_k_1047_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1044_);
    return v_res_1048_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim___redArg(
    mut v_t_1049_: *mut crate::leanh::LeanObject,
    mut v_nil_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1049_, v_nil_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_nil_elim(
    mut v_00_u03b1_1052_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1053_: *mut crate::leanh::LeanObject,
    mut v_motive_1054_: *mut crate::leanh::LeanObject,
    mut v_t_1055_: *mut crate::leanh::LeanObject,
    mut v_h_1056_: *mut crate::leanh::LeanObject,
    mut v_nil_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1055_, v_nil_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim___redArg(
    mut v_t_1059_: *mut crate::leanh::LeanObject,
    mut v_cons_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1059_, v_cons_1060_);
    return v___x_1061_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_cons_elim(
    mut v_00_u03b1_1062_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1063_: *mut crate::leanh::LeanObject,
    mut v_motive_1064_: *mut crate::leanh::LeanObject,
    mut v_t_1065_: *mut crate::leanh::LeanObject,
    mut v_h_1066_: *mut crate::leanh::LeanObject,
    mut v_cons_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Std_DHashMap_Internal_AssocList_ctorElim___redArg(v_t_1065_, v_cons_1067_);
    return v___x_1068_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList_default(
    mut v_00_u03b1_1069_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = crate::leanh::lean_box(0);
    return v___x_1071_;
}
pub unsafe fn l_Std_DHashMap_Internal_instInhabitedAssocList(
    mut v_a_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = crate::leanh::lean_box(0);
    return v___x_1074_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_f_1076_: *mut crate::leanh::LeanObject,
    mut v_x_1077_: *mut crate::leanh::LeanObject,
    mut v_x_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1078_) == 0 {
        let mut v_toApplicative_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1079_ = crate::leanh::lean_ctor_get(v_inst_1075_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1079_);
        crate::leanh::lean_dec(v_f_1076_);
        crate::leanh::lean_dec_ref(v_inst_1075_);
        v_toPure_1080_ = crate::leanh::lean_ctor_get(v_toApplicative_1079_, 1);
        crate::leanh::lean_inc(v_toPure_1080_);
        crate::leanh::lean_dec_ref(v_toApplicative_1079_);
        v___x_1081_ =
            crate::leanh::lean_apply_2(v_toPure_1080_, crate::leanh::lean_box(0), v_x_1077_);
        return v___x_1081_;
    } else {
        let mut v_toBind_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1082_ = crate::leanh::lean_ctor_get(v_inst_1075_, 1);
        crate::leanh::lean_inc(v_toBind_1082_);
        v_key_1083_ = crate::leanh::lean_ctor_get(v_x_1078_, 0);
        crate::leanh::lean_inc(v_key_1083_);
        v_value_1084_ = crate::leanh::lean_ctor_get(v_x_1078_, 1);
        crate::leanh::lean_inc(v_value_1084_);
        v_tail_1085_ = crate::leanh::lean_ctor_get(v_x_1078_, 2);
        crate::leanh::lean_inc(v_tail_1085_);
        crate::leanh::lean_dec_ref_known(v_x_1078_, 3);
        crate::leanh::lean_inc(v_f_1076_);
        v___f_1086_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1086_, 0, v_inst_1075_);
        crate::leanh::lean_closure_set(v___f_1086_, 1, v_f_1076_);
        crate::leanh::lean_closure_set(v___f_1086_, 2, v_tail_1085_);
        v___x_1087_ = crate::leanh::lean_apply_3(v_f_1076_, v_x_1077_, v_key_1083_, v_value_1084_);
        v___x_1088_ = crate::leanh::lean_apply_4(
            v_toBind_1082_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1087_,
            v___f_1086_,
        );
        return v___x_1088_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___redArg___lam__0(
    mut v_inst_1089_: *mut crate::leanh::LeanObject,
    mut v_f_1090_: *mut crate::leanh::LeanObject,
    mut v_tail_1091_: *mut crate::leanh::LeanObject,
    mut v_d_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1089_,
        v_f_1090_,
        v_d_1092_,
        v_tail_1091_,
    );
    return v___x_1093_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM(
    mut v_00_u03b1_1094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1095_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1096_: *mut crate::leanh::LeanObject,
    mut v_m_1097_: *mut crate::leanh::LeanObject,
    mut v_inst_1098_: *mut crate::leanh::LeanObject,
    mut v_f_1099_: *mut crate::leanh::LeanObject,
    mut v_x_1100_: *mut crate::leanh::LeanObject,
    mut v_x_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1098_,
        v_f_1099_,
        v_x_1100_,
        v_x_1101_,
    );
    return v___x_1102_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0(
    mut v_f_1103_: *mut crate::leanh::LeanObject,
    mut v_x1_1104_: *mut crate::leanh::LeanObject,
    mut v_x2_1105_: *mut crate::leanh::LeanObject,
    mut v_x3_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = crate::leanh::lean_apply_3(v_f_1103_, v_x1_1104_, v_x2_1105_, v_x3_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldl___redArg(
    mut v_f_1127_: *mut crate::leanh::LeanObject,
    mut v_init_1128_: *mut crate::leanh::LeanObject,
    mut v_as_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1130_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1130_, 0, v_f_1127_);
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
    mut v_00_u03b1_1133_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1135_: *mut crate::leanh::LeanObject,
    mut v_f_1136_: *mut crate::leanh::LeanObject,
    mut v_init_1137_: *mut crate::leanh::LeanObject,
    mut v_as_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1139_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1139_, 0, v_f_1136_);
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
    mut v_f_1142_: *mut crate::leanh::LeanObject,
    mut v_key_1143_: *mut crate::leanh::LeanObject,
    mut v_value_1144_: *mut crate::leanh::LeanObject,
    mut v_d_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = crate::leanh::lean_apply_3(v_f_1142_, v_key_1143_, v_value_1144_, v_d_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
    mut v_inst_1147_: *mut crate::leanh::LeanObject,
    mut v_f_1148_: *mut crate::leanh::LeanObject,
    mut v_x_1149_: *mut crate::leanh::LeanObject,
    mut v_x_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1150_) == 0 {
        let mut v_toApplicative_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1151_ = crate::leanh::lean_ctor_get(v_inst_1147_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1151_);
        crate::leanh::lean_dec(v_f_1148_);
        crate::leanh::lean_dec_ref(v_inst_1147_);
        v_toPure_1152_ = crate::leanh::lean_ctor_get(v_toApplicative_1151_, 1);
        crate::leanh::lean_inc(v_toPure_1152_);
        crate::leanh::lean_dec_ref(v_toApplicative_1151_);
        v___x_1153_ =
            crate::leanh::lean_apply_2(v_toPure_1152_, crate::leanh::lean_box(0), v_x_1149_);
        return v___x_1153_;
    } else {
        let mut v_toBind_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1154_ = crate::leanh::lean_ctor_get(v_inst_1147_, 1);
        crate::leanh::lean_inc(v_toBind_1154_);
        v_key_1155_ = crate::leanh::lean_ctor_get(v_x_1150_, 0);
        crate::leanh::lean_inc(v_key_1155_);
        v_value_1156_ = crate::leanh::lean_ctor_get(v_x_1150_, 1);
        crate::leanh::lean_inc(v_value_1156_);
        v_tail_1157_ = crate::leanh::lean_ctor_get(v_x_1150_, 2);
        crate::leanh::lean_inc(v_tail_1157_);
        crate::leanh::lean_dec_ref_known(v_x_1150_, 3);
        crate::leanh::lean_inc(v_f_1148_);
        v___f_1158_ = crate::leanh::lean_alloc_closure(
            l_Std_DHashMap_Internal_AssocList_foldrM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1158_, 0, v_f_1148_);
        crate::leanh::lean_closure_set(v___f_1158_, 1, v_key_1155_);
        crate::leanh::lean_closure_set(v___f_1158_, 2, v_value_1156_);
        v___x_1159_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
            v_inst_1147_,
            v_f_1148_,
            v_x_1149_,
            v_tail_1157_,
        );
        v___x_1160_ = crate::leanh::lean_apply_4(
            v_toBind_1154_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1159_,
            v___f_1158_,
        );
        return v___x_1160_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM(
    mut v_00_u03b1_1161_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1163_: *mut crate::leanh::LeanObject,
    mut v_m_1164_: *mut crate::leanh::LeanObject,
    mut v_inst_1165_: *mut crate::leanh::LeanObject,
    mut v_f_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
    mut v_x_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v_inst_1165_,
        v_f_1166_,
        v_x_1167_,
        v_x_1168_,
    );
    return v___x_1169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldr___redArg(
    mut v_f_1170_: *mut crate::leanh::LeanObject,
    mut v_init_1171_: *mut crate::leanh::LeanObject,
    mut v_as_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1173_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1173_, 0, v_f_1170_);
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
    mut v_00_u03b1_1176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1177_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1178_: *mut crate::leanh::LeanObject,
    mut v_f_1179_: *mut crate::leanh::LeanObject,
    mut v_init_1180_: *mut crate::leanh::LeanObject,
    mut v_as_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1182_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1182_, 0, v_f_1179_);
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
    mut v_f_1185_: *mut crate::leanh::LeanObject,
    mut v_x_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = crate::leanh::lean_apply_2(v_f_1185_, v___y_1187_, v___y_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM___redArg(
    mut v_inst_1190_: *mut crate::leanh::LeanObject,
    mut v_f_1191_: *mut crate::leanh::LeanObject,
    mut v_as_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1193_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1193_, 0, v_f_1191_);
    v___x_1194_ = crate::leanh::lean_box(0);
    v___x_1195_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1190_,
        v___f_1193_,
        v___x_1194_,
        v_as_1192_,
    );
    return v___x_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forM(
    mut v_00_u03b1_1196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1197_: *mut crate::leanh::LeanObject,
    mut v_m_1198_: *mut crate::leanh::LeanObject,
    mut v_inst_1199_: *mut crate::leanh::LeanObject,
    mut v_f_1200_: *mut crate::leanh::LeanObject,
    mut v_as_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1202_ = crate::leanh::lean_alloc_closure(
        l_Std_DHashMap_Internal_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1202_, 0, v_f_1200_);
    v___x_1203_ = crate::leanh::lean_box(0);
    v___x_1204_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v_inst_1199_,
        v___f_1202_,
        v___x_1203_,
        v_as_1201_,
    );
    return v___x_1204_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(
    mut v_inst_1205_: *mut crate::leanh::LeanObject,
    mut v_f_1206_: *mut crate::leanh::LeanObject,
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_1207_) == 0 {
        let mut v_toApplicative_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1209_ = crate::leanh::lean_ctor_get(v_inst_1205_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1209_);
        crate::leanh::lean_dec(v_f_1206_);
        crate::leanh::lean_dec_ref(v_inst_1205_);
        v_toPure_1210_ = crate::leanh::lean_ctor_get(v_toApplicative_1209_, 1);
        crate::leanh::lean_inc(v_toPure_1210_);
        crate::leanh::lean_dec_ref(v_toApplicative_1209_);
        v___x_1211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1211_, 0, v_a_1208_);
        v___x_1212_ =
            crate::leanh::lean_apply_2(v_toPure_1210_, crate::leanh::lean_box(0), v___x_1211_);
        return v___x_1212_;
    } else {
        let mut v_toApplicative_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1213_ = crate::leanh::lean_ctor_get(v_inst_1205_, 0);
        v_toBind_1214_ = crate::leanh::lean_ctor_get(v_inst_1205_, 1);
        crate::leanh::lean_inc(v_toBind_1214_);
        v_toPure_1215_ = crate::leanh::lean_ctor_get(v_toApplicative_1213_, 1);
        crate::leanh::lean_inc(v_toPure_1215_);
        v_key_1216_ = crate::leanh::lean_ctor_get(v_a_1207_, 0);
        crate::leanh::lean_inc(v_key_1216_);
        v_value_1217_ = crate::leanh::lean_ctor_get(v_a_1207_, 1);
        crate::leanh::lean_inc(v_value_1217_);
        v_tail_1218_ = crate::leanh::lean_ctor_get(v_a_1207_, 2);
        crate::leanh::lean_inc(v_tail_1218_);
        crate::leanh::lean_dec_ref_known(v_a_1207_, 3);
        crate::leanh::lean_inc(v_f_1206_);
        v___f_1219_ = crate::leanh::lean_alloc_closure(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_1219_, 0, v_toPure_1215_);
        crate::leanh::lean_closure_set(v___f_1219_, 1, v_inst_1205_);
        crate::leanh::lean_closure_set(v___f_1219_, 2, v_f_1206_);
        crate::leanh::lean_closure_set(v___f_1219_, 3, v_tail_1218_);
        v___x_1220_ = crate::leanh::lean_apply_3(v_f_1206_, v_key_1216_, v_value_1217_, v_a_1208_);
        v___x_1221_ = crate::leanh::lean_apply_4(
            v_toBind_1214_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1220_,
            v___f_1219_,
        );
        return v___x_1221_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg___lam__0(
    mut v_toPure_1222_: *mut crate::leanh::LeanObject,
    mut v_inst_1223_: *mut crate::leanh::LeanObject,
    mut v_f_1224_: *mut crate::leanh::LeanObject,
    mut v_tail_1225_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1226_) == 0 {
        let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_1225_);
        crate::leanh::lean_dec(v_f_1224_);
        crate::leanh::lean_dec_ref(v_inst_1223_);
        v___x_1227_ = crate::leanh::lean_apply_2(
            v_toPure_1222_,
            crate::leanh::lean_box(0),
            v_____do__lift_1226_,
        );
        return v___x_1227_;
    } else {
        let mut v_a_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1222_);
        v_a_1228_ = crate::leanh::lean_ctor_get(v_____do__lift_1226_, 0);
        crate::leanh::lean_inc(v_a_1228_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1229_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1223_, v_f_1224_, v_tail_1225_, v_a_1228_);
        return v___x_1229_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(
    mut v_00_u03b1_1230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1232_: *mut crate::leanh::LeanObject,
    mut v_m_1233_: *mut crate::leanh::LeanObject,
    mut v_inst_1234_: *mut crate::leanh::LeanObject,
    mut v_f_1235_: *mut crate::leanh::LeanObject,
    mut v_a_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1234_, v_f_1235_, v_a_1236_, v_a_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep___redArg(
    mut v_inst_1239_: *mut crate::leanh::LeanObject,
    mut v_as_1240_: *mut crate::leanh::LeanObject,
    mut v_init_1241_: *mut crate::leanh::LeanObject,
    mut v_f_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1239_, v_f_1242_, v_as_1240_, v_init_1241_);
    return v___x_1243_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_forInStep(
    mut v_00_u03b1_1244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1245_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_1246_: *mut crate::leanh::LeanObject,
    mut v_m_1247_: *mut crate::leanh::LeanObject,
    mut v_inst_1248_: *mut crate::leanh::LeanObject,
    mut v_as_1249_: *mut crate::leanh::LeanObject,
    mut v_init_1250_: *mut crate::leanh::LeanObject,
    mut v_f_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v_inst_1248_, v_f_1251_, v_as_1249_, v_init_1250_);
    return v___x_1252_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg(
    mut v_x_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1253_) == 0 {
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1254_ = crate::leanh::lean_box(0);
        return v___x_1254_;
    } else {
        let mut v_key_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_1255_ = crate::leanh::lean_ctor_get(v_x_1253_, 0);
        v_value_1256_ = crate::leanh::lean_ctor_get(v_x_1253_, 1);
        v_tail_1257_ = crate::leanh::lean_ctor_get(v_x_1253_, 2);
        crate::leanh::lean_inc(v_value_1256_);
        crate::leanh::lean_inc(v_key_1255_);
        v___x_1258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1258_, 0, v_key_1255_);
        crate::leanh::lean_ctor_set(v___x_1258_, 1, v_value_1256_);
        v___x_1259_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_tail_1257_);
        v___x_1260_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1260_, 0, v___x_1258_);
        crate::leanh::lean_ctor_set(v___x_1260_, 1, v___x_1259_);
        return v___x_1260_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___redArg___boxed(
    mut v_x_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1261_);
    crate::leanh::lean_dec(v_x_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList(
    mut v_00_u03b1_1263_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1264_: *mut crate::leanh::LeanObject,
    mut v_x_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_toList___boxed(
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ =
        l_Std_DHashMap_Internal_AssocList_toList(v_00_u03b1_1267_, v_00_u03b2_1268_, v_x_1269_);
    crate::leanh::lean_dec(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(
    mut v_x_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1272_) == 0 {
                    return v_x_1271_;
                } else {
                    v_tail_1273_ = crate::leanh::lean_ctor_get(v_x_1272_, 2);
                    v___x_1274_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1275_ = lean_nat_add(v_x_1271_, v___x_1274_);
                    crate::leanh::lean_dec(v_x_1271_);
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
    mut v_x_1277_: *mut crate::leanh::LeanObject,
    mut v_x_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1277_, v_x_1278_);
    crate::leanh::lean_dec(v_x_1278_);
    return v_res_1279_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg(
    mut v_l_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v___x_1281_, v_l_1280_);
    return v___x_1282_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___redArg___boxed(
    mut v_l_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1283_);
    crate::leanh::lean_dec(v_l_1283_);
    return v_res_1284_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length(
    mut v_00_u03b1_1285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1286_: *mut crate::leanh::LeanObject,
    mut v_l_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_l_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_length___boxed(
    mut v_00_u03b1_1289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1290_: *mut crate::leanh::LeanObject,
    mut v_l_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ =
        l_Std_DHashMap_Internal_AssocList_length(v_00_u03b1_1289_, v_00_u03b2_1290_, v_l_1291_);
    crate::leanh::lean_dec(v_l_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(
    mut v_00_u03b1_1293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1294_: *mut crate::leanh::LeanObject,
    mut v_x_1295_: *mut crate::leanh::LeanObject,
    mut v_x_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___redArg(v_x_1295_, v_x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0___boxed(
    mut v_00_u03b1_1298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v_x_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_length_spec__0(v_00_u03b1_1298_, v_00_u03b2_1299_, v_x_1300_, v_x_1301_);
    crate::leanh::lean_dec(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(
    mut v_inst_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_x_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1305_) == 0 {
                    crate::leanh::lean_dec(v_a_1304_);
                    crate::leanh::lean_dec_ref(v_inst_1303_);
                    v___x_1306_ = crate::leanh::lean_box(0);
                    return v___x_1306_;
                } else {
                    v_key_1307_ = crate::leanh::lean_ctor_get(v_x_1305_, 0);
                    crate::leanh::lean_inc(v_key_1307_);
                    v_value_1308_ = crate::leanh::lean_ctor_get(v_x_1305_, 1);
                    crate::leanh::lean_inc(v_value_1308_);
                    v_tail_1309_ = crate::leanh::lean_ctor_get(v_x_1305_, 2);
                    crate::leanh::lean_inc(v_tail_1309_);
                    crate::leanh::lean_dec_ref_known(v_x_1305_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1303_);
                    crate::leanh::lean_inc(v_a_1304_);
                    v___x_1310_ = crate::leanh::lean_apply_2(v_inst_1303_, v_key_1307_, v_a_1304_);
                    v___x_1311_ = (crate::leanh::lean_unbox(v___x_1310_) as u8);
                    if v___x_1311_ == 0 {
                        crate::leanh::lean_dec(v_value_1308_);
                        v_x_1305_ = v_tail_1309_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1309_);
                        crate::leanh::lean_dec(v_a_1304_);
                        crate::leanh::lean_dec_ref(v_inst_1303_);
                        v___x_1313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1313_, 0, v_value_1308_);
                        return v___x_1313_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f(
    mut v_00_u03b1_1314_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_x_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1316_, v_a_1317_, v_x_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(
    mut v_inst_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_x_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1322_) == 0 {
                    crate::leanh::lean_dec(v_a_1321_);
                    crate::leanh::lean_dec_ref(v_inst_1320_);
                    v___x_1323_ = crate::leanh::lean_box(0);
                    return v___x_1323_;
                } else {
                    v_key_1324_ = crate::leanh::lean_ctor_get(v_x_1322_, 0);
                    crate::leanh::lean_inc(v_key_1324_);
                    v_value_1325_ = crate::leanh::lean_ctor_get(v_x_1322_, 1);
                    crate::leanh::lean_inc(v_value_1325_);
                    v_tail_1326_ = crate::leanh::lean_ctor_get(v_x_1322_, 2);
                    crate::leanh::lean_inc(v_tail_1326_);
                    crate::leanh::lean_dec_ref_known(v_x_1322_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1320_);
                    crate::leanh::lean_inc(v_a_1321_);
                    v___x_1327_ = crate::leanh::lean_apply_2(v_inst_1320_, v_key_1324_, v_a_1321_);
                    v___x_1328_ = (crate::leanh::lean_unbox(v___x_1327_) as u8);
                    if v___x_1328_ == 0 {
                        crate::leanh::lean_dec(v_value_1325_);
                        v_x_1322_ = v_tail_1326_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1326_);
                        crate::leanh::lean_dec(v_a_1321_);
                        crate::leanh::lean_dec_ref(v_inst_1320_);
                        v___x_1330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1330_, 0, v_value_1325_);
                        return v___x_1330_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x3f(
    mut v_00_u03b1_1331_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1332_: *mut crate::leanh::LeanObject,
    mut v_inst_1333_: *mut crate::leanh::LeanObject,
    mut v_inst_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_x_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ =
        l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_1333_, v_a_1335_, v_x_1336_);
    return v___x_1337_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(
    mut v_inst_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1340_) == 0 {
                    crate::leanh::lean_dec(v_a_1339_);
                    crate::leanh::lean_dec_ref(v_inst_1338_);
                    v___x_1341_ = crate::leanh::lean_box(0);
                    return v___x_1341_;
                } else {
                    v_key_1342_ = crate::leanh::lean_ctor_get(v_x_1340_, 0);
                    crate::leanh::lean_inc_n(v_key_1342_, 2);
                    v_value_1343_ = crate::leanh::lean_ctor_get(v_x_1340_, 1);
                    crate::leanh::lean_inc(v_value_1343_);
                    v_tail_1344_ = crate::leanh::lean_ctor_get(v_x_1340_, 2);
                    crate::leanh::lean_inc(v_tail_1344_);
                    crate::leanh::lean_dec_ref_known(v_x_1340_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1338_);
                    crate::leanh::lean_inc(v_a_1339_);
                    v___x_1345_ = crate::leanh::lean_apply_2(v_inst_1338_, v_key_1342_, v_a_1339_);
                    v___x_1346_ = (crate::leanh::lean_unbox(v___x_1345_) as u8);
                    if v___x_1346_ == 0 {
                        crate::leanh::lean_dec(v_value_1343_);
                        crate::leanh::lean_dec(v_key_1342_);
                        v_x_1340_ = v_tail_1344_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1344_);
                        crate::leanh::lean_dec(v_a_1339_);
                        crate::leanh::lean_dec_ref(v_inst_1338_);
                        v___x_1348_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1348_, 0, v_key_1342_);
                        crate::leanh::lean_ctor_set(v___x_1348_, 1, v_value_1343_);
                        v___x_1349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1348_);
                        return v___x_1349_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x3f(
    mut v_00_u03b1_1350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1351_: *mut crate::leanh::LeanObject,
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_x_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ =
        l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_1352_, v_a_1353_, v_x_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg(
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_x_1358_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1359_: u8 = 0;
    let mut v_key_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1358_) == 0 {
                    crate::leanh::lean_dec(v_a_1357_);
                    crate::leanh::lean_dec_ref(v_inst_1356_);
                    v___x_1359_ = 0;
                    return v___x_1359_;
                } else {
                    v_key_1360_ = crate::leanh::lean_ctor_get(v_x_1358_, 0);
                    crate::leanh::lean_inc(v_key_1360_);
                    v_tail_1361_ = crate::leanh::lean_ctor_get(v_x_1358_, 2);
                    crate::leanh::lean_inc(v_tail_1361_);
                    crate::leanh::lean_dec_ref_known(v_x_1358_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1356_);
                    crate::leanh::lean_inc(v_a_1357_);
                    v___x_1362_ = crate::leanh::lean_apply_2(v_inst_1356_, v_key_1360_, v_a_1357_);
                    v___x_1363_ = (crate::leanh::lean_unbox(v___x_1362_) as u8);
                    if v___x_1363_ == 0 {
                        v_x_1358_ = v_tail_1361_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1361_);
                        crate::leanh::lean_dec(v_a_1357_);
                        crate::leanh::lean_dec_ref(v_inst_1356_);
                        v___x_1365_ = (crate::leanh::lean_unbox(v___x_1362_) as u8);
                        return v___x_1365_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___redArg___boxed(
    mut v_inst_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_x_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1369_: u8 = 0;
    let mut v_r_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1366_, v_a_1367_, v_x_1368_);
    v_r_1370_ = crate::leanh::lean_box((v_res_1369_) as usize);
    return v_r_1370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains(
    mut v_00_u03b1_1371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_inst_1373_: *mut crate::leanh::LeanObject,
    mut v_a_1374_: *mut crate::leanh::LeanObject,
    mut v_x_1375_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1376_: u8 = 0;
    v___x_1376_ =
        l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1373_, v_a_1374_, v_x_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___boxed(
    mut v_00_u03b1_1377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1378_: *mut crate::leanh::LeanObject,
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_x_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Std_DHashMap_Internal_AssocList_contains(
        v_00_u03b1_1377_,
        v_00_u03b2_1378_,
        v_inst_1379_,
        v_a_1380_,
        v_x_1381_,
    );
    v_r_1383_ = crate::leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(
    mut v_x_1384_: *mut crate::leanh::LeanObject,
    mut v_h__1_1385_: *mut crate::leanh::LeanObject,
    mut v_h__2_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1384_) == 0 {
        let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1386_);
        v___x_1387_ = crate::leanh::lean_box(0);
        v___x_1388_ = crate::leanh::lean_apply_1(v_h__1_1385_, v___x_1387_);
        return v___x_1388_;
    } else {
        let mut v_key_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1385_);
        v_key_1389_ = crate::leanh::lean_ctor_get(v_x_1384_, 0);
        crate::leanh::lean_inc(v_key_1389_);
        v_value_1390_ = crate::leanh::lean_ctor_get(v_x_1384_, 1);
        crate::leanh::lean_inc(v_value_1390_);
        v_tail_1391_ = crate::leanh::lean_ctor_get(v_x_1384_, 2);
        crate::leanh::lean_inc(v_tail_1391_);
        crate::leanh::lean_dec_ref_known(v_x_1384_, 3);
        v___x_1392_ =
            crate::leanh::lean_apply_3(v_h__2_1386_, v_key_1389_, v_value_1390_, v_tail_1391_);
        return v___x_1392_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(
    mut v_00_u03b1_1393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1394_: *mut crate::leanh::LeanObject,
    mut v_motive_1395_: *mut crate::leanh::LeanObject,
    mut v_x_1396_: *mut crate::leanh::LeanObject,
    mut v_h__1_1397_: *mut crate::leanh::LeanObject,
    mut v_h__2_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1396_) == 0 {
        let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1398_);
        v___x_1399_ = crate::leanh::lean_box(0);
        v___x_1400_ = crate::leanh::lean_apply_1(v_h__1_1397_, v___x_1399_);
        return v___x_1400_;
    } else {
        let mut v_key_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1397_);
        v_key_1401_ = crate::leanh::lean_ctor_get(v_x_1396_, 0);
        crate::leanh::lean_inc(v_key_1401_);
        v_value_1402_ = crate::leanh::lean_ctor_get(v_x_1396_, 1);
        crate::leanh::lean_inc(v_value_1402_);
        v_tail_1403_ = crate::leanh::lean_ctor_get(v_x_1396_, 2);
        crate::leanh::lean_inc(v_tail_1403_);
        crate::leanh::lean_dec_ref_known(v_x_1396_, 3);
        v___x_1404_ =
            crate::leanh::lean_apply_3(v_h__2_1398_, v_key_1401_, v_value_1402_, v_tail_1403_);
        return v___x_1404_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get___redArg(
    mut v_inst_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_x_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1408_ = crate::leanh::lean_ctor_get(v_x_1407_, 0);
                crate::leanh::lean_inc(v_key_1408_);
                v_value_1409_ = crate::leanh::lean_ctor_get(v_x_1407_, 1);
                crate::leanh::lean_inc(v_value_1409_);
                v_tail_1410_ = crate::leanh::lean_ctor_get(v_x_1407_, 2);
                crate::leanh::lean_inc(v_tail_1410_);
                crate::leanh::lean_dec(v_x_1407_);
                crate::leanh::lean_inc_ref(v_inst_1405_);
                crate::leanh::lean_inc(v_a_1406_);
                v___x_1411_ = crate::leanh::lean_apply_2(v_inst_1405_, v_key_1408_, v_a_1406_);
                v___x_1412_ = (crate::leanh::lean_unbox(v___x_1411_) as u8);
                if v___x_1412_ == 0 {
                    crate::leanh::lean_dec(v_value_1409_);
                    v_x_1407_ = v_tail_1410_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_1410_);
                    crate::leanh::lean_dec(v_a_1406_);
                    crate::leanh::lean_dec_ref(v_inst_1405_);
                    return v_value_1409_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get(
    mut v_00_u03b1_1414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1415_: *mut crate::leanh::LeanObject,
    mut v_inst_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
    mut v_x_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ =
        l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1416_, v_a_1417_, v_x_1418_);
    return v___x_1420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast___redArg(
    mut v_inst_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_x_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1424_ = crate::leanh::lean_ctor_get(v_x_1423_, 0);
                crate::leanh::lean_inc(v_key_1424_);
                v_value_1425_ = crate::leanh::lean_ctor_get(v_x_1423_, 1);
                crate::leanh::lean_inc(v_value_1425_);
                v_tail_1426_ = crate::leanh::lean_ctor_get(v_x_1423_, 2);
                crate::leanh::lean_inc(v_tail_1426_);
                crate::leanh::lean_dec(v_x_1423_);
                crate::leanh::lean_inc_ref(v_inst_1421_);
                crate::leanh::lean_inc(v_a_1422_);
                v___x_1427_ = crate::leanh::lean_apply_2(v_inst_1421_, v_key_1424_, v_a_1422_);
                v___x_1428_ = (crate::leanh::lean_unbox(v___x_1427_) as u8);
                if v___x_1428_ == 0 {
                    crate::leanh::lean_dec(v_value_1425_);
                    v_x_1423_ = v_tail_1426_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_1426_);
                    crate::leanh::lean_dec(v_a_1422_);
                    crate::leanh::lean_dec_ref(v_inst_1421_);
                    return v_value_1425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast(
    mut v_00_u03b1_1430_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1431_: *mut crate::leanh::LeanObject,
    mut v_inst_1432_: *mut crate::leanh::LeanObject,
    mut v_inst_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
    mut v_x_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ =
        l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1432_, v_a_1434_, v_x_1435_);
    return v___x_1437_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry___redArg(
    mut v_inst_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1441_ = crate::leanh::lean_ctor_get(v_x_1440_, 0);
                crate::leanh::lean_inc_n(v_key_1441_, 2);
                v_value_1442_ = crate::leanh::lean_ctor_get(v_x_1440_, 1);
                crate::leanh::lean_inc(v_value_1442_);
                v_tail_1443_ = crate::leanh::lean_ctor_get(v_x_1440_, 2);
                crate::leanh::lean_inc(v_tail_1443_);
                crate::leanh::lean_dec(v_x_1440_);
                crate::leanh::lean_inc_ref(v_inst_1438_);
                crate::leanh::lean_inc(v_a_1439_);
                v___x_1444_ = crate::leanh::lean_apply_2(v_inst_1438_, v_key_1441_, v_a_1439_);
                v___x_1445_ = (crate::leanh::lean_unbox(v___x_1444_) as u8);
                if v___x_1445_ == 0 {
                    crate::leanh::lean_dec(v_value_1442_);
                    crate::leanh::lean_dec(v_key_1441_);
                    v_x_1440_ = v_tail_1443_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_1443_);
                    crate::leanh::lean_dec(v_a_1439_);
                    crate::leanh::lean_dec_ref(v_inst_1438_);
                    v___x_1447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v_key_1441_);
                    crate::leanh::lean_ctor_set(v___x_1447_, 1, v_value_1442_);
                    return v___x_1447_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry(
    mut v_00_u03b1_1448_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1449_: *mut crate::leanh::LeanObject,
    mut v_inst_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_x_1452_: *mut crate::leanh::LeanObject,
    mut v_x_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ =
        l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1450_, v_a_1451_, v_x_1452_);
    return v___x_1454_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
    mut v_inst_1455_: *mut crate::leanh::LeanObject,
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_fallback_1457_: *mut crate::leanh::LeanObject,
    mut v_x_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1458_) == 0 {
                    crate::leanh::lean_dec(v_a_1456_);
                    crate::leanh::lean_dec_ref(v_inst_1455_);
                    crate::leanh::lean_inc_ref(v_fallback_1457_);
                    return v_fallback_1457_;
                } else {
                    v_key_1459_ = crate::leanh::lean_ctor_get(v_x_1458_, 0);
                    crate::leanh::lean_inc_n(v_key_1459_, 2);
                    v_value_1460_ = crate::leanh::lean_ctor_get(v_x_1458_, 1);
                    crate::leanh::lean_inc(v_value_1460_);
                    v_tail_1461_ = crate::leanh::lean_ctor_get(v_x_1458_, 2);
                    crate::leanh::lean_inc(v_tail_1461_);
                    crate::leanh::lean_dec_ref_known(v_x_1458_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1455_);
                    crate::leanh::lean_inc(v_a_1456_);
                    v___x_1462_ = crate::leanh::lean_apply_2(v_inst_1455_, v_key_1459_, v_a_1456_);
                    v___x_1463_ = (crate::leanh::lean_unbox(v___x_1462_) as u8);
                    if v___x_1463_ == 0 {
                        crate::leanh::lean_dec(v_value_1460_);
                        crate::leanh::lean_dec(v_key_1459_);
                        v_x_1458_ = v_tail_1461_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1461_);
                        crate::leanh::lean_dec(v_a_1456_);
                        crate::leanh::lean_dec_ref(v_inst_1455_);
                        v___x_1465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1465_, 0, v_key_1459_);
                        crate::leanh::lean_ctor_set(v___x_1465_, 1, v_value_1460_);
                        return v___x_1465_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___redArg___boxed(
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v_fallback_1468_: *mut crate::leanh::LeanObject,
    mut v_x_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1466_,
        v_a_1467_,
        v_fallback_1468_,
        v_x_1469_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1468_);
    return v_res_1470_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD(
    mut v_00_u03b1_1471_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1472_: *mut crate::leanh::LeanObject,
    mut v_inst_1473_: *mut crate::leanh::LeanObject,
    mut v_a_1474_: *mut crate::leanh::LeanObject,
    mut v_fallback_1475_: *mut crate::leanh::LeanObject,
    mut v_x_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(
        v_inst_1473_,
        v_a_1474_,
        v_fallback_1475_,
        v_x_1476_,
    );
    return v___x_1477_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntryD___boxed(
    mut v_00_u03b1_1478_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1479_: *mut crate::leanh::LeanObject,
    mut v_inst_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_fallback_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ = l_Std_DHashMap_Internal_AssocList_getEntryD(
        v_00_u03b1_1478_,
        v_00_u03b2_1479_,
        v_inst_1480_,
        v_a_1481_,
        v_fallback_1482_,
        v_x_1483_,
    );
    crate::leanh::lean_dec_ref(v_fallback_1482_);
    return v_res_1484_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
    mut v_inst_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
    mut v_x_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1488_) == 0 {
                    crate::leanh::lean_dec(v_a_1486_);
                    crate::leanh::lean_dec_ref(v_inst_1485_);
                    crate::leanh::lean_inc_ref(v_inst_1487_);
                    return v_inst_1487_;
                } else {
                    v_key_1489_ = crate::leanh::lean_ctor_get(v_x_1488_, 0);
                    crate::leanh::lean_inc_n(v_key_1489_, 2);
                    v_value_1490_ = crate::leanh::lean_ctor_get(v_x_1488_, 1);
                    crate::leanh::lean_inc(v_value_1490_);
                    v_tail_1491_ = crate::leanh::lean_ctor_get(v_x_1488_, 2);
                    crate::leanh::lean_inc(v_tail_1491_);
                    crate::leanh::lean_dec_ref_known(v_x_1488_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1485_);
                    crate::leanh::lean_inc(v_a_1486_);
                    v___x_1492_ = crate::leanh::lean_apply_2(v_inst_1485_, v_key_1489_, v_a_1486_);
                    v___x_1493_ = (crate::leanh::lean_unbox(v___x_1492_) as u8);
                    if v___x_1493_ == 0 {
                        crate::leanh::lean_dec(v_value_1490_);
                        crate::leanh::lean_dec(v_key_1489_);
                        v_x_1488_ = v_tail_1491_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1491_);
                        crate::leanh::lean_dec(v_a_1486_);
                        crate::leanh::lean_dec_ref(v_inst_1485_);
                        v___x_1495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1495_, 0, v_key_1489_);
                        crate::leanh::lean_ctor_set(v___x_1495_, 1, v_value_1490_);
                        return v___x_1495_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg___boxed(
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_a_1497_: *mut crate::leanh::LeanObject,
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1496_,
        v_a_1497_,
        v_inst_1498_,
        v_x_1499_,
    );
    crate::leanh::lean_dec_ref(v_inst_1498_);
    return v_res_1500_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21(
    mut v_00_u03b1_1501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1502_: *mut crate::leanh::LeanObject,
    mut v_inst_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
    mut v_inst_1505_: *mut crate::leanh::LeanObject,
    mut v_x_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(
        v_inst_1503_,
        v_a_1504_,
        v_inst_1505_,
        v_x_1506_,
    );
    return v___x_1507_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getEntry_x21___boxed(
    mut v_00_u03b1_1508_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1509_: *mut crate::leanh::LeanObject,
    mut v_inst_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_x_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21(
        v_00_u03b1_1508_,
        v_00_u03b2_1509_,
        v_inst_1510_,
        v_a_1511_,
        v_inst_1512_,
        v_x_1513_,
    );
    crate::leanh::lean_dec_ref(v_inst_1512_);
    return v_res_1514_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey___redArg(
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_x_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_key_1518_ = crate::leanh::lean_ctor_get(v_x_1517_, 0);
                crate::leanh::lean_inc_n(v_key_1518_, 2);
                v_tail_1519_ = crate::leanh::lean_ctor_get(v_x_1517_, 2);
                crate::leanh::lean_inc(v_tail_1519_);
                crate::leanh::lean_dec(v_x_1517_);
                crate::leanh::lean_inc_ref(v_inst_1515_);
                crate::leanh::lean_inc(v_a_1516_);
                v___x_1520_ = crate::leanh::lean_apply_2(v_inst_1515_, v_key_1518_, v_a_1516_);
                v___x_1521_ = (crate::leanh::lean_unbox(v___x_1520_) as u8);
                if v___x_1521_ == 0 {
                    crate::leanh::lean_dec(v_key_1518_);
                    v_x_1517_ = v_tail_1519_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_1519_);
                    crate::leanh::lean_dec(v_a_1516_);
                    crate::leanh::lean_dec_ref(v_inst_1515_);
                    return v_key_1518_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey(
    mut v_00_u03b1_1523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1524_: *mut crate::leanh::LeanObject,
    mut v_inst_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_x_1527_: *mut crate::leanh::LeanObject,
    mut v_x_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ =
        l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_1525_, v_a_1526_, v_x_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1534_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1535_ = crate::leanh::lean_unsigned_to_nat(153);
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
    mut v_inst_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_inst_1541_: *mut crate::leanh::LeanObject,
    mut v_x_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1542_) == 0 {
                    crate::leanh::lean_dec(v_a_1540_);
                    crate::leanh::lean_dec_ref(v_inst_1539_);
                    v___x_1543_ = crate::leanh::lean_obj_once(
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
                    v_key_1545_ = crate::leanh::lean_ctor_get(v_x_1542_, 0);
                    crate::leanh::lean_inc(v_key_1545_);
                    v_value_1546_ = crate::leanh::lean_ctor_get(v_x_1542_, 1);
                    crate::leanh::lean_inc(v_value_1546_);
                    v_tail_1547_ = crate::leanh::lean_ctor_get(v_x_1542_, 2);
                    crate::leanh::lean_inc(v_tail_1547_);
                    crate::leanh::lean_dec_ref_known(v_x_1542_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1539_);
                    crate::leanh::lean_inc(v_a_1540_);
                    v___x_1548_ = crate::leanh::lean_apply_2(v_inst_1539_, v_key_1545_, v_a_1540_);
                    v___x_1549_ = (crate::leanh::lean_unbox(v___x_1548_) as u8);
                    if v___x_1549_ == 0 {
                        crate::leanh::lean_dec(v_value_1546_);
                        v_x_1542_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1547_);
                        crate::leanh::lean_dec(v_a_1540_);
                        crate::leanh::lean_dec_ref(v_inst_1539_);
                        return v_value_1546_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___boxed(
    mut v_inst_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_inst_1553_: *mut crate::leanh::LeanObject,
    mut v_x_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1551_,
        v_a_1552_,
        v_inst_1553_,
        v_x_1554_,
    );
    crate::leanh::lean_dec(v_inst_1553_);
    return v_res_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21(
    mut v_00_u03b1_1556_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1557_: *mut crate::leanh::LeanObject,
    mut v_inst_1558_: *mut crate::leanh::LeanObject,
    mut v_inst_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_inst_1561_: *mut crate::leanh::LeanObject,
    mut v_x_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(
        v_inst_1558_,
        v_a_1560_,
        v_inst_1561_,
        v_x_1562_,
    );
    return v___x_1563_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCast_x21___boxed(
    mut v_00_u03b1_1564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1565_: *mut crate::leanh::LeanObject,
    mut v_inst_1566_: *mut crate::leanh::LeanObject,
    mut v_inst_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_inst_1569_: *mut crate::leanh::LeanObject,
    mut v_x_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_getCast_x21(
        v_00_u03b1_1564_,
        v_00_u03b2_1565_,
        v_inst_1566_,
        v_inst_1567_,
        v_a_1568_,
        v_inst_1569_,
        v_x_1570_,
    );
    crate::leanh::lean_dec(v_inst_1569_);
    return v_res_1571_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
    mut v_x_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1574_) == 0 {
                    crate::leanh::lean_dec(v_a_1573_);
                    crate::leanh::lean_dec_ref(v_inst_1572_);
                    v___x_1575_ = crate::leanh::lean_box(0);
                    return v___x_1575_;
                } else {
                    v_key_1576_ = crate::leanh::lean_ctor_get(v_x_1574_, 0);
                    crate::leanh::lean_inc_n(v_key_1576_, 2);
                    v_tail_1577_ = crate::leanh::lean_ctor_get(v_x_1574_, 2);
                    crate::leanh::lean_inc(v_tail_1577_);
                    crate::leanh::lean_dec_ref_known(v_x_1574_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1572_);
                    crate::leanh::lean_inc(v_a_1573_);
                    v___x_1578_ = crate::leanh::lean_apply_2(v_inst_1572_, v_key_1576_, v_a_1573_);
                    v___x_1579_ = (crate::leanh::lean_unbox(v___x_1578_) as u8);
                    if v___x_1579_ == 0 {
                        crate::leanh::lean_dec(v_key_1576_);
                        v_x_1574_ = v_tail_1577_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1577_);
                        crate::leanh::lean_dec(v_a_1573_);
                        crate::leanh::lean_dec_ref(v_inst_1572_);
                        v___x_1581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1581_, 0, v_key_1576_);
                        return v___x_1581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x3f(
    mut v_00_u03b1_1582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1583_: *mut crate::leanh::LeanObject,
    mut v_inst_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_x_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ =
        l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_1584_, v_a_1585_, v_x_1586_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1590_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1591_ = crate::leanh::lean_unsigned_to_nat(163);
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
    mut v_inst_1595_: *mut crate::leanh::LeanObject,
    mut v_inst_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1598_) == 0 {
                    crate::leanh::lean_dec(v_a_1597_);
                    crate::leanh::lean_dec_ref(v_inst_1595_);
                    v___x_1599_ = crate::leanh::lean_obj_once(
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
                    v_key_1601_ = crate::leanh::lean_ctor_get(v_x_1598_, 0);
                    crate::leanh::lean_inc(v_key_1601_);
                    v_value_1602_ = crate::leanh::lean_ctor_get(v_x_1598_, 1);
                    crate::leanh::lean_inc(v_value_1602_);
                    v_tail_1603_ = crate::leanh::lean_ctor_get(v_x_1598_, 2);
                    crate::leanh::lean_inc(v_tail_1603_);
                    crate::leanh::lean_dec_ref_known(v_x_1598_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1595_);
                    crate::leanh::lean_inc(v_a_1597_);
                    v___x_1604_ = crate::leanh::lean_apply_2(v_inst_1595_, v_key_1601_, v_a_1597_);
                    v___x_1605_ = (crate::leanh::lean_unbox(v___x_1604_) as u8);
                    if v___x_1605_ == 0 {
                        crate::leanh::lean_dec(v_value_1602_);
                        v_x_1598_ = v_tail_1603_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1603_);
                        crate::leanh::lean_dec(v_a_1597_);
                        crate::leanh::lean_dec_ref(v_inst_1595_);
                        return v_value_1602_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___redArg___boxed(
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
    mut v_inst_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
    mut v_x_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1607_,
        v_inst_1608_,
        v_a_1609_,
        v_x_1610_,
    );
    crate::leanh::lean_dec(v_inst_1608_);
    return v_res_1611_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21(
    mut v_00_u03b1_1612_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1613_: *mut crate::leanh::LeanObject,
    mut v_inst_1614_: *mut crate::leanh::LeanObject,
    mut v_inst_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(
        v_inst_1614_,
        v_inst_1615_,
        v_a_1616_,
        v_x_1617_,
    );
    return v___x_1618_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___boxed(
    mut v_00_u03b1_1619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1620_: *mut crate::leanh::LeanObject,
    mut v_inst_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_x_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Std_DHashMap_Internal_AssocList_get_x21(
        v_00_u03b1_1619_,
        v_00_u03b2_1620_,
        v_inst_1621_,
        v_inst_1622_,
        v_a_1623_,
        v_x_1624_,
    );
    crate::leanh::lean_dec(v_inst_1622_);
    return v_res_1625_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg___closed__2;
    v___x_1628_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1629_ = crate::leanh::lean_unsigned_to_nat(168);
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
    mut v_inst_1633_: *mut crate::leanh::LeanObject,
    mut v_inst_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1636_) == 0 {
                    crate::leanh::lean_dec(v_a_1635_);
                    crate::leanh::lean_dec_ref(v_inst_1633_);
                    v___x_1637_ = crate::leanh::lean_obj_once(
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
                    v_key_1639_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                    crate::leanh::lean_inc_n(v_key_1639_, 2);
                    v_tail_1640_ = crate::leanh::lean_ctor_get(v_x_1636_, 2);
                    crate::leanh::lean_inc(v_tail_1640_);
                    crate::leanh::lean_dec_ref_known(v_x_1636_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1633_);
                    crate::leanh::lean_inc(v_a_1635_);
                    v___x_1641_ = crate::leanh::lean_apply_2(v_inst_1633_, v_key_1639_, v_a_1635_);
                    v___x_1642_ = (crate::leanh::lean_unbox(v___x_1641_) as u8);
                    if v___x_1642_ == 0 {
                        crate::leanh::lean_dec(v_key_1639_);
                        v_x_1636_ = v_tail_1640_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1640_);
                        crate::leanh::lean_dec(v_a_1635_);
                        crate::leanh::lean_dec_ref(v_inst_1633_);
                        return v_key_1639_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg___boxed(
    mut v_inst_1644_: *mut crate::leanh::LeanObject,
    mut v_inst_1645_: *mut crate::leanh::LeanObject,
    mut v_a_1646_: *mut crate::leanh::LeanObject,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1644_,
        v_inst_1645_,
        v_a_1646_,
        v_x_1647_,
    );
    crate::leanh::lean_dec(v_inst_1645_);
    return v_res_1648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21(
    mut v_00_u03b1_1649_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1650_: *mut crate::leanh::LeanObject,
    mut v_inst_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_x_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(
        v_inst_1651_,
        v_inst_1652_,
        v_a_1653_,
        v_x_1654_,
    );
    return v___x_1655_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKey_x21___boxed(
    mut v_00_u03b1_1656_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1657_: *mut crate::leanh::LeanObject,
    mut v_inst_1658_: *mut crate::leanh::LeanObject,
    mut v_inst_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_x_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_DHashMap_Internal_AssocList_getKey_x21(
        v_00_u03b1_1656_,
        v_00_u03b2_1657_,
        v_inst_1658_,
        v_inst_1659_,
        v_a_1660_,
        v_x_1661_,
    );
    crate::leanh::lean_dec(v_inst_1659_);
    return v_res_1662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
    mut v_inst_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
    mut v_fallback_1665_: *mut crate::leanh::LeanObject,
    mut v_x_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1666_) == 0 {
                    crate::leanh::lean_dec(v_a_1664_);
                    crate::leanh::lean_dec_ref(v_inst_1663_);
                    crate::leanh::lean_inc(v_fallback_1665_);
                    return v_fallback_1665_;
                } else {
                    v_key_1667_ = crate::leanh::lean_ctor_get(v_x_1666_, 0);
                    crate::leanh::lean_inc(v_key_1667_);
                    v_value_1668_ = crate::leanh::lean_ctor_get(v_x_1666_, 1);
                    crate::leanh::lean_inc(v_value_1668_);
                    v_tail_1669_ = crate::leanh::lean_ctor_get(v_x_1666_, 2);
                    crate::leanh::lean_inc(v_tail_1669_);
                    crate::leanh::lean_dec_ref_known(v_x_1666_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1663_);
                    crate::leanh::lean_inc(v_a_1664_);
                    v___x_1670_ = crate::leanh::lean_apply_2(v_inst_1663_, v_key_1667_, v_a_1664_);
                    v___x_1671_ = (crate::leanh::lean_unbox(v___x_1670_) as u8);
                    if v___x_1671_ == 0 {
                        crate::leanh::lean_dec(v_value_1668_);
                        v_x_1666_ = v_tail_1669_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1669_);
                        crate::leanh::lean_dec(v_a_1664_);
                        crate::leanh::lean_dec_ref(v_inst_1663_);
                        return v_value_1668_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___redArg___boxed(
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_a_1674_: *mut crate::leanh::LeanObject,
    mut v_fallback_1675_: *mut crate::leanh::LeanObject,
    mut v_x_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1673_,
        v_a_1674_,
        v_fallback_1675_,
        v_x_1676_,
    );
    crate::leanh::lean_dec(v_fallback_1675_);
    return v_res_1677_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD(
    mut v_00_u03b1_1678_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1679_: *mut crate::leanh::LeanObject,
    mut v_inst_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
    mut v_fallback_1683_: *mut crate::leanh::LeanObject,
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(
        v_inst_1680_,
        v_a_1682_,
        v_fallback_1683_,
        v_x_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getCastD___boxed(
    mut v_00_u03b1_1686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1687_: *mut crate::leanh::LeanObject,
    mut v_inst_1688_: *mut crate::leanh::LeanObject,
    mut v_inst_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_fallback_1691_: *mut crate::leanh::LeanObject,
    mut v_x_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Std_DHashMap_Internal_AssocList_getCastD(
        v_00_u03b1_1686_,
        v_00_u03b2_1687_,
        v_inst_1688_,
        v_inst_1689_,
        v_a_1690_,
        v_fallback_1691_,
        v_x_1692_,
    );
    crate::leanh::lean_dec(v_fallback_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg(
    mut v_inst_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_fallback_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1697_) == 0 {
                    crate::leanh::lean_dec(v_a_1695_);
                    crate::leanh::lean_dec_ref(v_inst_1694_);
                    crate::leanh::lean_inc(v_fallback_1696_);
                    return v_fallback_1696_;
                } else {
                    v_key_1698_ = crate::leanh::lean_ctor_get(v_x_1697_, 0);
                    crate::leanh::lean_inc(v_key_1698_);
                    v_value_1699_ = crate::leanh::lean_ctor_get(v_x_1697_, 1);
                    crate::leanh::lean_inc(v_value_1699_);
                    v_tail_1700_ = crate::leanh::lean_ctor_get(v_x_1697_, 2);
                    crate::leanh::lean_inc(v_tail_1700_);
                    crate::leanh::lean_dec_ref_known(v_x_1697_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1694_);
                    crate::leanh::lean_inc(v_a_1695_);
                    v___x_1701_ = crate::leanh::lean_apply_2(v_inst_1694_, v_key_1698_, v_a_1695_);
                    v___x_1702_ = (crate::leanh::lean_unbox(v___x_1701_) as u8);
                    if v___x_1702_ == 0 {
                        crate::leanh::lean_dec(v_value_1699_);
                        v_x_1697_ = v_tail_1700_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1700_);
                        crate::leanh::lean_dec(v_a_1695_);
                        crate::leanh::lean_dec_ref(v_inst_1694_);
                        return v_value_1699_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___redArg___boxed(
    mut v_inst_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_fallback_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1704_,
        v_a_1705_,
        v_fallback_1706_,
        v_x_1707_,
    );
    crate::leanh::lean_dec(v_fallback_1706_);
    return v_res_1708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD(
    mut v_00_u03b1_1709_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1710_: *mut crate::leanh::LeanObject,
    mut v_inst_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_fallback_1713_: *mut crate::leanh::LeanObject,
    mut v_x_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(
        v_inst_1711_,
        v_a_1712_,
        v_fallback_1713_,
        v_x_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___boxed(
    mut v_00_u03b1_1716_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1717_: *mut crate::leanh::LeanObject,
    mut v_inst_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
    mut v_fallback_1720_: *mut crate::leanh::LeanObject,
    mut v_x_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l_Std_DHashMap_Internal_AssocList_getD(
        v_00_u03b1_1716_,
        v_00_u03b2_1717_,
        v_inst_1718_,
        v_a_1719_,
        v_fallback_1720_,
        v_x_1721_,
    );
    crate::leanh::lean_dec(v_fallback_1720_);
    return v_res_1722_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
    mut v_inst_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
    mut v_fallback_1725_: *mut crate::leanh::LeanObject,
    mut v_x_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1726_) == 0 {
                    crate::leanh::lean_dec(v_a_1724_);
                    crate::leanh::lean_dec_ref(v_inst_1723_);
                    crate::leanh::lean_inc(v_fallback_1725_);
                    return v_fallback_1725_;
                } else {
                    v_key_1727_ = crate::leanh::lean_ctor_get(v_x_1726_, 0);
                    crate::leanh::lean_inc_n(v_key_1727_, 2);
                    v_tail_1728_ = crate::leanh::lean_ctor_get(v_x_1726_, 2);
                    crate::leanh::lean_inc(v_tail_1728_);
                    crate::leanh::lean_dec_ref_known(v_x_1726_, 3);
                    crate::leanh::lean_inc_ref(v_inst_1723_);
                    crate::leanh::lean_inc(v_a_1724_);
                    v___x_1729_ = crate::leanh::lean_apply_2(v_inst_1723_, v_key_1727_, v_a_1724_);
                    v___x_1730_ = (crate::leanh::lean_unbox(v___x_1729_) as u8);
                    if v___x_1730_ == 0 {
                        crate::leanh::lean_dec(v_key_1727_);
                        v_x_1726_ = v_tail_1728_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1728_);
                        crate::leanh::lean_dec(v_a_1724_);
                        crate::leanh::lean_dec_ref(v_inst_1723_);
                        return v_key_1727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___redArg___boxed(
    mut v_inst_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
    mut v_fallback_1734_: *mut crate::leanh::LeanObject,
    mut v_x_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1732_,
        v_a_1733_,
        v_fallback_1734_,
        v_x_1735_,
    );
    crate::leanh::lean_dec(v_fallback_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD(
    mut v_00_u03b1_1737_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1738_: *mut crate::leanh::LeanObject,
    mut v_inst_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_fallback_1741_: *mut crate::leanh::LeanObject,
    mut v_x_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(
        v_inst_1739_,
        v_a_1740_,
        v_fallback_1741_,
        v_x_1742_,
    );
    return v___x_1743_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getKeyD___boxed(
    mut v_00_u03b1_1744_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1745_: *mut crate::leanh::LeanObject,
    mut v_inst_1746_: *mut crate::leanh::LeanObject,
    mut v_a_1747_: *mut crate::leanh::LeanObject,
    mut v_fallback_1748_: *mut crate::leanh::LeanObject,
    mut v_x_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Std_DHashMap_Internal_AssocList_getKeyD(
        v_00_u03b1_1744_,
        v_00_u03b2_1745_,
        v_inst_1746_,
        v_a_1747_,
        v_fallback_1748_,
        v_x_1749_,
    );
    crate::leanh::lean_dec(v_fallback_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___redArg(
    mut v_inst_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_b_1753_: *mut crate::leanh::LeanObject,
    mut v_x_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1754_) == 0 {
                    crate::leanh::lean_dec(v_b_1753_);
                    crate::leanh::lean_dec(v_a_1752_);
                    crate::leanh::lean_dec_ref(v_inst_1751_);
                    return v_x_1754_;
                } else {
                    v_key_1755_ = crate::leanh::lean_ctor_get(v_x_1754_, 0);
                    v_value_1756_ = crate::leanh::lean_ctor_get(v_x_1754_, 1);
                    v_tail_1757_ = crate::leanh::lean_ctor_get(v_x_1754_, 2);
                    v_isSharedCheck_1770_ = (!crate::leanh::lean_is_exclusive(v_x_1754_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1759_ = v_x_1754_;
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1757_);
                        crate::leanh::lean_inc(v_value_1756_);
                        crate::leanh::lean_inc(v_key_1755_);
                        crate::leanh::lean_dec(v_x_1754_);
                        v___x_1759_ = crate::leanh::lean_box(0);
                        v_isShared_1760_ = v_isSharedCheck_1770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1751_);
                crate::leanh::lean_inc(v_a_1752_);
                crate::leanh::lean_inc(v_key_1755_);
                v___x_1761_ = crate::leanh::lean_apply_2(v_inst_1751_, v_key_1755_, v_a_1752_);
                v___x_1762_ = (crate::leanh::lean_unbox(v___x_1761_) as u8);
                if v___x_1762_ == 0 {
                    v___x_1763_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
                        v_inst_1751_,
                        v_a_1752_,
                        v_b_1753_,
                        v_tail_1757_,
                    );
                    if v_isShared_1760_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1759_, 2, v___x_1763_);
                        v___x_1765_ = v___x_1759_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1766_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_key_1755_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_value_1756_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 2, v___x_1763_);
                        v___x_1765_ = v_reuseFailAlloc_1766_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1756_);
                    crate::leanh::lean_dec(v_key_1755_);
                    crate::leanh::lean_dec_ref(v_inst_1751_);
                    if v_isShared_1760_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1759_, 1, v_b_1753_);
                        crate::leanh::lean_ctor_set(v___x_1759_, 0, v_a_1752_);
                        v___x_1768_ = v___x_1759_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1752_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_b_1753_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_tail_1757_);
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
    mut v_00_u03b1_1771_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1772_: *mut crate::leanh::LeanObject,
    mut v_inst_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_b_1775_: *mut crate::leanh::LeanObject,
    mut v_x_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(
        v_inst_1773_,
        v_a_1774_,
        v_b_1775_,
        v_x_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___redArg(
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1780_) == 0 {
                    crate::leanh::lean_dec(v_a_1779_);
                    crate::leanh::lean_dec_ref(v_inst_1778_);
                    return v_x_1780_;
                } else {
                    v_key_1781_ = crate::leanh::lean_ctor_get(v_x_1780_, 0);
                    v_value_1782_ = crate::leanh::lean_ctor_get(v_x_1780_, 1);
                    v_tail_1783_ = crate::leanh::lean_ctor_get(v_x_1780_, 2);
                    v_isSharedCheck_1793_ = (!crate::leanh::lean_is_exclusive(v_x_1780_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1785_ = v_x_1780_;
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1783_);
                        crate::leanh::lean_inc(v_value_1782_);
                        crate::leanh::lean_inc(v_key_1781_);
                        crate::leanh::lean_dec(v_x_1780_);
                        v___x_1785_ = crate::leanh::lean_box(0);
                        v_isShared_1786_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1778_);
                crate::leanh::lean_inc(v_a_1779_);
                crate::leanh::lean_inc(v_key_1781_);
                v___x_1787_ = crate::leanh::lean_apply_2(v_inst_1778_, v_key_1781_, v_a_1779_);
                v___x_1788_ = (crate::leanh::lean_unbox(v___x_1787_) as u8);
                if v___x_1788_ == 0 {
                    v___x_1789_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(
                        v_inst_1778_,
                        v_a_1779_,
                        v_tail_1783_,
                    );
                    if v_isShared_1786_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1785_, 2, v___x_1789_);
                        v___x_1791_ = v___x_1785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1792_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_key_1781_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_value_1782_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1789_);
                        v___x_1791_ = v_reuseFailAlloc_1792_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1785_);
                    crate::leanh::lean_dec(v_value_1782_);
                    crate::leanh::lean_dec(v_key_1781_);
                    crate::leanh::lean_dec(v_a_1779_);
                    crate::leanh::lean_dec_ref(v_inst_1778_);
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
    mut v_00_u03b1_1794_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1795_: *mut crate::leanh::LeanObject,
    mut v_inst_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_x_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ =
        l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_1796_, v_a_1797_, v_x_1798_);
    return v___x_1799_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_modify___redArg(
    mut v_inst_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
    mut v_f_1802_: *mut crate::leanh::LeanObject,
    mut v_x_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1803_) == 0 {
                    crate::leanh::lean_dec(v_f_1802_);
                    crate::leanh::lean_dec(v_a_1801_);
                    crate::leanh::lean_dec_ref(v_inst_1800_);
                    return v_x_1803_;
                } else {
                    v_key_1804_ = crate::leanh::lean_ctor_get(v_x_1803_, 0);
                    v_value_1805_ = crate::leanh::lean_ctor_get(v_x_1803_, 1);
                    v_tail_1806_ = crate::leanh::lean_ctor_get(v_x_1803_, 2);
                    v_isSharedCheck_1820_ = (!crate::leanh::lean_is_exclusive(v_x_1803_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1808_ = v_x_1803_;
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1806_);
                        crate::leanh::lean_inc(v_value_1805_);
                        crate::leanh::lean_inc(v_key_1804_);
                        crate::leanh::lean_dec(v_x_1803_);
                        v___x_1808_ = crate::leanh::lean_box(0);
                        v_isShared_1809_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1800_);
                crate::leanh::lean_inc(v_a_1801_);
                crate::leanh::lean_inc(v_key_1804_);
                v___x_1810_ = crate::leanh::lean_apply_2(v_inst_1800_, v_key_1804_, v_a_1801_);
                v___x_1811_ = (crate::leanh::lean_unbox(v___x_1810_) as u8);
                if v___x_1811_ == 0 {
                    v___x_1812_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
                        v_inst_1800_,
                        v_a_1801_,
                        v_f_1802_,
                        v_tail_1806_,
                    );
                    if v_isShared_1809_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1808_, 2, v___x_1812_);
                        v___x_1814_ = v___x_1808_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1815_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_key_1804_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_value_1805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 2, v___x_1812_);
                        v___x_1814_ = v_reuseFailAlloc_1815_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_1804_);
                    crate::leanh::lean_dec_ref(v_inst_1800_);
                    v_b_1816_ = crate::leanh::lean_apply_1(v_f_1802_, v_value_1805_);
                    if v_isShared_1809_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1808_, 1, v_b_1816_);
                        crate::leanh::lean_ctor_set(v___x_1808_, 0, v_a_1801_);
                        v___x_1818_ = v___x_1808_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1819_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1801_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_b_1816_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_tail_1806_);
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
    mut v_00_u03b1_1821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1822_: *mut crate::leanh::LeanObject,
    mut v_inst_1823_: *mut crate::leanh::LeanObject,
    mut v_inst_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_f_1826_: *mut crate::leanh::LeanObject,
    mut v_x_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(
        v_inst_1823_,
        v_a_1825_,
        v_f_1826_,
        v_x_1827_,
    );
    return v___x_1828_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_alter___redArg(
    mut v_inst_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
    mut v_f_1831_: *mut crate::leanh::LeanObject,
    mut v_x_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v_tail_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1832_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_1829_);
                    v___x_1833_ = crate::leanh::lean_box(0);
                    v___x_1834_ = crate::leanh::lean_apply_1(v_f_1831_, v___x_1833_);
                    if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                        crate::leanh::lean_dec(v_a_1830_);
                        return v_x_1832_;
                    } else {
                        v_val_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                        crate::leanh::lean_inc(v_val_1835_);
                        crate::leanh::lean_dec_ref_known(v___x_1834_, 1);
                        v___x_1836_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1836_, 0, v_a_1830_);
                        crate::leanh::lean_ctor_set(v___x_1836_, 1, v_val_1835_);
                        crate::leanh::lean_ctor_set(v___x_1836_, 2, v_x_1832_);
                        return v___x_1836_;
                    }
                } else {
                    v_key_1837_ = crate::leanh::lean_ctor_get(v_x_1832_, 0);
                    v_value_1838_ = crate::leanh::lean_ctor_get(v_x_1832_, 1);
                    v_tail_1839_ = crate::leanh::lean_ctor_get(v_x_1832_, 2);
                    v_isSharedCheck_1855_ = (!crate::leanh::lean_is_exclusive(v_x_1832_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1841_ = v_x_1832_;
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1839_);
                        crate::leanh::lean_inc(v_value_1838_);
                        crate::leanh::lean_inc(v_key_1837_);
                        crate::leanh::lean_dec(v_x_1832_);
                        v___x_1841_ = crate::leanh::lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1829_);
                crate::leanh::lean_inc(v_a_1830_);
                crate::leanh::lean_inc(v_key_1837_);
                v___x_1843_ = crate::leanh::lean_apply_2(v_inst_1829_, v_key_1837_, v_a_1830_);
                v___x_1844_ = (crate::leanh::lean_unbox(v___x_1843_) as u8);
                if v___x_1844_ == 0 {
                    v_tail_1845_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
                        v_inst_1829_,
                        v_a_1830_,
                        v_f_1831_,
                        v_tail_1839_,
                    );
                    if v_isShared_1842_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1841_, 2, v_tail_1845_);
                        v___x_1847_ = v___x_1841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1848_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_key_1837_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_value_1838_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_tail_1845_);
                        v___x_1847_ = v_reuseFailAlloc_1848_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_1837_);
                    crate::leanh::lean_dec_ref(v_inst_1829_);
                    v___x_1849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v_value_1838_);
                    v___x_1850_ = crate::leanh::lean_apply_1(v_f_1831_, v___x_1849_);
                    if crate::leanh::lean_obj_tag(v___x_1850_) == 0 {
                        crate::leanh::lean_del_object(v___x_1841_);
                        crate::leanh::lean_dec(v_a_1830_);
                        return v_tail_1839_;
                    } else {
                        v_val_1851_ = crate::leanh::lean_ctor_get(v___x_1850_, 0);
                        crate::leanh::lean_inc(v_val_1851_);
                        crate::leanh::lean_dec_ref_known(v___x_1850_, 1);
                        if v_isShared_1842_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1841_, 1, v_val_1851_);
                            crate::leanh::lean_ctor_set(v___x_1841_, 0, v_a_1830_);
                            v___x_1853_ = v___x_1841_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1854_ =
                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1830_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_val_1851_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_tail_1839_);
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
    mut v_00_u03b1_1856_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1857_: *mut crate::leanh::LeanObject,
    mut v_inst_1858_: *mut crate::leanh::LeanObject,
    mut v_inst_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
    mut v_f_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(
        v_inst_1858_,
        v_a_1860_,
        v_f_1861_,
        v_x_1862_,
    );
    return v___x_1863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
    mut v_inst_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_f_1866_: *mut crate::leanh::LeanObject,
    mut v_x_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1867_) == 0 {
                    crate::leanh::lean_dec(v_f_1866_);
                    crate::leanh::lean_dec(v_a_1865_);
                    crate::leanh::lean_dec_ref(v_inst_1864_);
                    return v_x_1867_;
                } else {
                    v_key_1868_ = crate::leanh::lean_ctor_get(v_x_1867_, 0);
                    v_value_1869_ = crate::leanh::lean_ctor_get(v_x_1867_, 1);
                    v_tail_1870_ = crate::leanh::lean_ctor_get(v_x_1867_, 2);
                    v_isSharedCheck_1884_ = (!crate::leanh::lean_is_exclusive(v_x_1867_)) as u8;
                    if v_isSharedCheck_1884_ == 0 {
                        v___x_1872_ = v_x_1867_;
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1870_);
                        crate::leanh::lean_inc(v_value_1869_);
                        crate::leanh::lean_inc(v_key_1868_);
                        crate::leanh::lean_dec(v_x_1867_);
                        v___x_1872_ = crate::leanh::lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1884_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1864_);
                crate::leanh::lean_inc(v_a_1865_);
                crate::leanh::lean_inc(v_key_1868_);
                v___x_1874_ = crate::leanh::lean_apply_2(v_inst_1864_, v_key_1868_, v_a_1865_);
                v___x_1875_ = (crate::leanh::lean_unbox(v___x_1874_) as u8);
                if v___x_1875_ == 0 {
                    v___x_1876_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
                        v_inst_1864_,
                        v_a_1865_,
                        v_f_1866_,
                        v_tail_1870_,
                    );
                    if v_isShared_1873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1872_, 2, v___x_1876_);
                        v___x_1878_ = v___x_1872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_key_1868_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_value_1869_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 2, v___x_1876_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_1868_);
                    crate::leanh::lean_dec_ref(v_inst_1864_);
                    v___x_1880_ = crate::leanh::lean_apply_1(v_f_1866_, v_value_1869_);
                    if v_isShared_1873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1880_);
                        crate::leanh::lean_ctor_set(v___x_1872_, 0, v_a_1865_);
                        v___x_1882_ = v___x_1872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1883_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1865_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_tail_1870_);
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
    mut v_00_u03b1_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_f_1889_: *mut crate::leanh::LeanObject,
    mut v_x_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(
        v_inst_1886_,
        v_a_1888_,
        v_f_1889_,
        v_x_1890_,
    );
    return v___x_1891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
    mut v_inst_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_f_1894_: *mut crate::leanh::LeanObject,
    mut v_x_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v_tail_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1895_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_1892_);
                    v___x_1896_ = crate::leanh::lean_box(0);
                    v___x_1897_ = crate::leanh::lean_apply_1(v_f_1894_, v___x_1896_);
                    if crate::leanh::lean_obj_tag(v___x_1897_) == 0 {
                        crate::leanh::lean_dec(v_a_1893_);
                        return v_x_1895_;
                    } else {
                        v_val_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                        crate::leanh::lean_inc(v_val_1898_);
                        crate::leanh::lean_dec_ref_known(v___x_1897_, 1);
                        v___x_1899_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1899_, 0, v_a_1893_);
                        crate::leanh::lean_ctor_set(v___x_1899_, 1, v_val_1898_);
                        crate::leanh::lean_ctor_set(v___x_1899_, 2, v_x_1895_);
                        return v___x_1899_;
                    }
                } else {
                    v_key_1900_ = crate::leanh::lean_ctor_get(v_x_1895_, 0);
                    v_value_1901_ = crate::leanh::lean_ctor_get(v_x_1895_, 1);
                    v_tail_1902_ = crate::leanh::lean_ctor_get(v_x_1895_, 2);
                    v_isSharedCheck_1918_ = (!crate::leanh::lean_is_exclusive(v_x_1895_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1904_ = v_x_1895_;
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1902_);
                        crate::leanh::lean_inc(v_value_1901_);
                        crate::leanh::lean_inc(v_key_1900_);
                        crate::leanh::lean_dec(v_x_1895_);
                        v___x_1904_ = crate::leanh::lean_box(0);
                        v_isShared_1905_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1892_);
                crate::leanh::lean_inc(v_a_1893_);
                crate::leanh::lean_inc(v_key_1900_);
                v___x_1906_ = crate::leanh::lean_apply_2(v_inst_1892_, v_key_1900_, v_a_1893_);
                v___x_1907_ = (crate::leanh::lean_unbox(v___x_1906_) as u8);
                if v___x_1907_ == 0 {
                    v_tail_1908_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
                        v_inst_1892_,
                        v_a_1893_,
                        v_f_1894_,
                        v_tail_1902_,
                    );
                    if v_isShared_1905_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1904_, 2, v_tail_1908_);
                        v___x_1910_ = v___x_1904_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_key_1900_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_value_1901_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_tail_1908_);
                        v___x_1910_ = v_reuseFailAlloc_1911_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_1900_);
                    crate::leanh::lean_dec_ref(v_inst_1892_);
                    v___x_1912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1912_, 0, v_value_1901_);
                    v___x_1913_ = crate::leanh::lean_apply_1(v_f_1894_, v___x_1912_);
                    if crate::leanh::lean_obj_tag(v___x_1913_) == 0 {
                        crate::leanh::lean_del_object(v___x_1904_);
                        crate::leanh::lean_dec(v_a_1893_);
                        return v_tail_1902_;
                    } else {
                        v_val_1914_ = crate::leanh::lean_ctor_get(v___x_1913_, 0);
                        crate::leanh::lean_inc(v_val_1914_);
                        crate::leanh::lean_dec_ref_known(v___x_1913_, 1);
                        if v_isShared_1905_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1904_, 1, v_val_1914_);
                            crate::leanh::lean_ctor_set(v___x_1904_, 0, v_a_1893_);
                            v___x_1916_ = v___x_1904_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1917_ =
                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1893_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_val_1914_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_tail_1902_);
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
    mut v_00_u03b1_1919_: *mut crate::leanh::LeanObject,
    mut v_inst_1920_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1921_: *mut crate::leanh::LeanObject,
    mut v_a_1922_: *mut crate::leanh::LeanObject,
    mut v_f_1923_: *mut crate::leanh::LeanObject,
    mut v_x_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(
        v_inst_1920_,
        v_a_1922_,
        v_f_1923_,
        v_x_1924_,
    );
    return v___x_1925_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(
    mut v_f_1926_: *mut crate::leanh::LeanObject,
    mut v_acc_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1928_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_1926_);
                    return v_acc_1927_;
                } else {
                    v_key_1929_ = crate::leanh::lean_ctor_get(v_a_1928_, 0);
                    v_value_1930_ = crate::leanh::lean_ctor_get(v_a_1928_, 1);
                    v_tail_1931_ = crate::leanh::lean_ctor_get(v_a_1928_, 2);
                    v_isSharedCheck_1942_ = (!crate::leanh::lean_is_exclusive(v_a_1928_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1933_ = v_a_1928_;
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1931_);
                        crate::leanh::lean_inc(v_value_1930_);
                        crate::leanh::lean_inc(v_key_1929_);
                        crate::leanh::lean_dec(v_a_1928_);
                        v___x_1933_ = crate::leanh::lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_1942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_1926_);
                crate::leanh::lean_inc(v_key_1929_);
                v___x_1935_ = crate::leanh::lean_apply_2(v_f_1926_, v_key_1929_, v_value_1930_);
                if crate::leanh::lean_obj_tag(v___x_1935_) == 0 {
                    crate::leanh::lean_del_object(v___x_1933_);
                    crate::leanh::lean_dec(v_key_1929_);
                    v_a_1928_ = v_tail_1931_;
                    state = 0;
                    continue;
                } else {
                    v_val_1937_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                    crate::leanh::lean_inc(v_val_1937_);
                    crate::leanh::lean_dec_ref_known(v___x_1935_, 1);
                    if v_isShared_1934_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1933_, 2, v_acc_1927_);
                        crate::leanh::lean_ctor_set(v___x_1933_, 1, v_val_1937_);
                        v___x_1939_ = v___x_1933_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1941_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_key_1929_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_val_1937_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_acc_1927_);
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
    mut v_00_u03b1_1943_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1944_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1945_: *mut crate::leanh::LeanObject,
    mut v_f_1946_: *mut crate::leanh::LeanObject,
    mut v_acc_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1946_, v_acc_1947_, v_a_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap___redArg(
    mut v_f_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = crate::leanh::lean_box(0);
    v___x_1953_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1950_, v___x_1952_, v_a_1951_);
    return v___x_1953_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filterMap(
    mut v_00_u03b1_1954_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1955_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1956_: *mut crate::leanh::LeanObject,
    mut v_f_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = crate::leanh::lean_box(0);
    v___x_1960_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___redArg(v_f_1957_, v___x_1959_, v_a_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(
    mut v_f_1961_: *mut crate::leanh::LeanObject,
    mut v_acc_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1963_) == 0 {
                    crate::leanh::lean_dec(v_f_1961_);
                    return v_acc_1962_;
                } else {
                    v_key_1964_ = crate::leanh::lean_ctor_get(v_a_1963_, 0);
                    v_value_1965_ = crate::leanh::lean_ctor_get(v_a_1963_, 1);
                    v_tail_1966_ = crate::leanh::lean_ctor_get(v_a_1963_, 2);
                    v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v_a_1963_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1968_ = v_a_1963_;
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1966_);
                        crate::leanh::lean_inc(v_value_1965_);
                        crate::leanh::lean_inc(v_key_1964_);
                        crate::leanh::lean_dec(v_a_1963_);
                        v___x_1968_ = crate::leanh::lean_box(0);
                        v_isShared_1969_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_1961_);
                crate::leanh::lean_inc(v_key_1964_);
                v___x_1970_ = crate::leanh::lean_apply_2(v_f_1961_, v_key_1964_, v_value_1965_);
                if v_isShared_1969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1968_, 2, v_acc_1962_);
                    crate::leanh::lean_ctor_set(v___x_1968_, 1, v___x_1970_);
                    v___x_1972_ = v___x_1968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_key_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_acc_1962_);
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
    mut v_00_u03b1_1976_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1977_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1978_: *mut crate::leanh::LeanObject,
    mut v_f_1979_: *mut crate::leanh::LeanObject,
    mut v_acc_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1979_, v_acc_1980_, v_a_1981_);
    return v___x_1982_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map___redArg(
    mut v_f_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1985_ = crate::leanh::lean_box(0);
    v___x_1986_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1983_, v___x_1985_, v_a_1984_);
    return v___x_1986_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_map(
    mut v_00_u03b1_1987_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1988_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1989_: *mut crate::leanh::LeanObject,
    mut v_f_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = crate::leanh::lean_box(0);
    v___x_1993_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___redArg(v_f_1990_, v___x_1992_, v_a_1991_);
    return v___x_1993_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(
    mut v_f_1994_: *mut crate::leanh::LeanObject,
    mut v_acc_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2002_: u8 = 0;
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1996_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_1994_);
                    return v_acc_1995_;
                } else {
                    v_key_1997_ = crate::leanh::lean_ctor_get(v_a_1996_, 0);
                    v_value_1998_ = crate::leanh::lean_ctor_get(v_a_1996_, 1);
                    v_tail_1999_ = crate::leanh::lean_ctor_get(v_a_1996_, 2);
                    v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v_a_1996_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2001_ = v_a_1996_;
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1999_);
                        crate::leanh::lean_inc(v_value_1998_);
                        crate::leanh::lean_inc(v_key_1997_);
                        crate::leanh::lean_dec(v_a_1996_);
                        v___x_2001_ = crate::leanh::lean_box(0);
                        v_isShared_2002_ = v_isSharedCheck_2010_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_1994_);
                crate::leanh::lean_inc(v_value_1998_);
                crate::leanh::lean_inc(v_key_1997_);
                v___x_2003_ = crate::leanh::lean_apply_2(v_f_1994_, v_key_1997_, v_value_1998_);
                v___x_2004_ = (crate::leanh::lean_unbox(v___x_2003_) as u8);
                if v___x_2004_ == 0 {
                    crate::leanh::lean_del_object(v___x_2001_);
                    crate::leanh::lean_dec(v_value_1998_);
                    crate::leanh::lean_dec(v_key_1997_);
                    v_a_1996_ = v_tail_1999_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2002_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2001_, 2, v_acc_1995_);
                        v___x_2007_ = v___x_2001_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_key_1997_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_value_1998_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_acc_1995_);
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
    mut v_00_u03b1_2011_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2012_: *mut crate::leanh::LeanObject,
    mut v_f_2013_: *mut crate::leanh::LeanObject,
    mut v_acc_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2013_, v_acc_2014_, v_a_2015_);
    return v___x_2016_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter___redArg(
    mut v_f_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = crate::leanh::lean_box(0);
    v___x_2020_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2017_, v___x_2019_, v_a_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_filter(
    mut v_00_u03b1_2021_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2022_: *mut crate::leanh::LeanObject,
    mut v_f_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = crate::leanh::lean_box(0);
    v___x_2026_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___redArg(v_f_2023_, v___x_2025_, v_a_2024_);
    return v___x_2026_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
}
