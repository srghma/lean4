// Lean compiler output
// Module: Lake.Util.OrdHashSet
// Imports: Std.Data.HashSet.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
pub static l_Lake_OrdHashSet_instCoeHashSet___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_instCoeHashSet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_instCoeHashSet___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_OrdHashSet_empty___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdHashSet_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdHashSet_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_OrdHashSet_empty___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_empty___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_OrdHashSet_empty___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdHashSet_empty___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__0_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__1_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__2_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__3_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__4_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__5_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__6_value:
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
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__7_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__8_value: leanh::LeanCtorObject<
    5,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__9_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___lam__0(
    mut v_self_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toHashSet_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toHashSet_585_ = leanh::lean_ctor_get(v_self_584_, 0);
    leanh::lean_inc_ref(v_toHashSet_585_);
    return v_toHashSet_585_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed(
    mut v_self_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Lake_OrdHashSet_instCoeHashSet___lam__0(v_self_586_);
    leanh::lean_dec_ref(v_self_586_);
    return v_res_587_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet(
    mut v_00_u03b1_589_: *mut leanh::LeanObject,
    mut v_inst_590_: *mut leanh::LeanObject,
    mut v_inst_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_592_ = l_Lake_OrdHashSet_instCoeHashSet___closed__0;
    return v___f_592_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___boxed(
    mut v_00_u03b1_593_: *mut leanh::LeanObject,
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lake_OrdHashSet_instCoeHashSet(v_00_u03b1_593_, v_inst_594_, v_inst_595_);
    leanh::lean_dec_ref(v_inst_595_);
    leanh::lean_dec_ref(v_inst_594_);
    return v_res_596_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = leanh::lean_box(0);
    v___x_598_ = leanh::lean_unsigned_to_nat(16);
    v___x_599_ = lean_mk_array(v___x_598_, v___x_597_);
    return v___x_599_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__0_once),
        _init_l_Lake_OrdHashSet_empty___closed__0,
    );
    v___x_601_ = leanh::lean_unsigned_to_nat(0);
    v___x_602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_602_, 0, v___x_601_);
    leanh::lean_ctor_set(v___x_602_, 1, v___x_600_);
    return v___x_602_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = l_Lake_OrdHashSet_empty___closed__2;
    v___x_606_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1_once),
        _init_l_Lake_OrdHashSet_empty___closed__1,
    );
    v___x_607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_607_, 0, v___x_606_);
    leanh::lean_ctor_set(v___x_607_, 1, v___x_605_);
    return v___x_607_;
}
pub unsafe fn l_Lake_OrdHashSet_empty(
    mut v_00_u03b1_608_: *mut leanh::LeanObject,
    mut v_inst_609_: *mut leanh::LeanObject,
    mut v_inst_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__3),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__3_once),
        _init_l_Lake_OrdHashSet_empty___closed__3,
    );
    return v___x_611_;
}
pub unsafe fn l_Lake_OrdHashSet_empty___boxed(
    mut v_00_u03b1_612_: *mut leanh::LeanObject,
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_inst_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Lake_OrdHashSet_empty(v_00_u03b1_612_, v_inst_613_, v_inst_614_);
    leanh::lean_dec_ref(v_inst_614_);
    leanh::lean_dec_ref(v_inst_613_);
    return v_res_615_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___redArg(
    mut v_inst_616_: *mut leanh::LeanObject,
    mut v_inst_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Lake_OrdHashSet_empty(leanh::lean_box(0), v_inst_616_, v_inst_617_);
    return v___x_618_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(
    mut v_inst_619_: *mut leanh::LeanObject,
    mut v_inst_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lake_OrdHashSet_instEmptyCollection___redArg(v_inst_619_, v_inst_620_);
    leanh::lean_dec_ref(v_inst_620_);
    leanh::lean_dec_ref(v_inst_619_);
    return v_res_621_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection(
    mut v_00_u03b1_622_: *mut leanh::LeanObject,
    mut v_inst_623_: *mut leanh::LeanObject,
    mut v_inst_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lake_OrdHashSet_empty(leanh::lean_box(0), v_inst_623_, v_inst_624_);
    return v___x_625_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___boxed(
    mut v_00_u03b1_626_: *mut leanh::LeanObject,
    mut v_inst_627_: *mut leanh::LeanObject,
    mut v_inst_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_626_, v_inst_627_, v_inst_628_);
    leanh::lean_dec_ref(v_inst_628_);
    leanh::lean_dec_ref(v_inst_627_);
    return v_res_629_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___redArg(
    mut v_size_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1_once),
        _init_l_Lake_OrdHashSet_empty___closed__1,
    );
    v___x_632_ = lean_mk_empty_array_with_capacity(v_size_630_);
    v___x_633_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_633_, 0, v___x_631_);
    leanh::lean_ctor_set(v___x_633_, 1, v___x_632_);
    return v___x_633_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___redArg___boxed(
    mut v_size_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_634_);
    leanh::lean_dec(v_size_634_);
    return v_res_635_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty(
    mut v_00_u03b1_636_: *mut leanh::LeanObject,
    mut v_inst_637_: *mut leanh::LeanObject,
    mut v_inst_638_: *mut leanh::LeanObject,
    mut v_size_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_639_);
    return v___x_640_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___boxed(
    mut v_00_u03b1_641_: *mut leanh::LeanObject,
    mut v_inst_642_: *mut leanh::LeanObject,
    mut v_inst_643_: *mut leanh::LeanObject,
    mut v_size_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_645_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_641_, v_inst_642_, v_inst_643_, v_size_644_);
    leanh::lean_dec(v_size_644_);
    leanh::lean_dec_ref(v_inst_643_);
    leanh::lean_dec_ref(v_inst_642_);
    return v_res_645_;
}
pub unsafe fn l_Lake_OrdHashSet_insert___redArg(
    mut v_inst_646_: *mut leanh::LeanObject,
    mut v_inst_647_: *mut leanh::LeanObject,
    mut v_self_648_: *mut leanh::LeanObject,
    mut v_a_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toHashSet_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_unused_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_650_ = leanh::lean_ctor_get(v_self_648_, 0);
                v_toArray_651_ = leanh::lean_ctor_get(v_self_648_, 1);
                leanh::lean_inc(v_a_649_);
                leanh::lean_inc_ref(v_inst_646_);
                leanh::lean_inc_ref(v_inst_647_);
                v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v_inst_647_,
                    v_inst_646_,
                    v_toHashSet_650_,
                    v_a_649_,
                );
                if v___x_652_ == 0 {
                    leanh::lean_inc_ref(v_toArray_651_);
                    leanh::lean_inc_ref(v_toHashSet_650_);
                    v_isSharedCheck_662_ = (!leanh::lean_is_exclusive(v_self_648_)) as u8;
                    if v_isSharedCheck_662_ == 0 {
                        v_unused_663_ = leanh::lean_ctor_get(v_self_648_, 1);
                        leanh::lean_dec(v_unused_663_);
                        v_unused_664_ = leanh::lean_ctor_get(v_self_648_, 0);
                        leanh::lean_dec(v_unused_664_);
                        v___x_654_ = v_self_648_;
                        v_isShared_655_ = v_isSharedCheck_662_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_self_648_);
                        v___x_654_ = leanh::lean_box(0);
                        v_isShared_655_ = v_isSharedCheck_662_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_649_);
                    leanh::lean_dec_ref(v_inst_647_);
                    leanh::lean_dec_ref(v_inst_646_);
                    return v_self_648_;
                }
            }
            1 => {
                v___x_656_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_649_);
                v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v_inst_647_,
                    v_inst_646_,
                    v_toHashSet_650_,
                    v_a_649_,
                    v___x_656_,
                );
                v___x_658_ = lean_array_push(v_toArray_651_, v_a_649_);
                if v_isShared_655_ == 0 {
                    leanh::lean_ctor_set(v___x_654_, 1, v___x_658_);
                    leanh::lean_ctor_set(v___x_654_, 0, v___x_657_);
                    v___x_660_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_661_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
                    v___x_660_ = v_reuseFailAlloc_661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_insert(
    mut v_00_u03b1_665_: *mut leanh::LeanObject,
    mut v_inst_666_: *mut leanh::LeanObject,
    mut v_inst_667_: *mut leanh::LeanObject,
    mut v_self_668_: *mut leanh::LeanObject,
    mut v_a_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lake_OrdHashSet_insert___redArg(v_inst_666_, v_inst_667_, v_self_668_, v_a_669_);
    return v___x_670_;
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___redArg___lam__0(
    mut v_inst_671_: *mut leanh::LeanObject,
    mut v_inst_672_: *mut leanh::LeanObject,
    mut v_x1_673_: *mut leanh::LeanObject,
    mut v_x2_674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lake_OrdHashSet_insert___redArg(v_inst_671_, v_inst_672_, v_x1_673_, v_x2_674_);
    return v___x_675_;
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___redArg(
    mut v_inst_695_: *mut leanh::LeanObject,
    mut v_inst_696_: *mut leanh::LeanObject,
    mut v_self_697_: *mut leanh::LeanObject,
    mut v_arr_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    v___x_699_ = leanh::lean_unsigned_to_nat(0);
    v___x_700_ = lean_array_get_size(v_arr_698_);
    v___x_701_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_702_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
    if v___x_702_ == 0 {
        leanh::lean_dec_ref(v_arr_698_);
        leanh::lean_dec_ref(v_inst_696_);
        leanh::lean_dec_ref(v_inst_695_);
        return v_self_697_;
    } else {
        let mut v___f_703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: u8 = 0;
        v___f_703_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_appendArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_703_, 0, v_inst_695_);
        leanh::lean_closure_set(v___f_703_, 1, v_inst_696_);
        v___x_704_ = lean_nat_dec_le(v___x_700_, v___x_700_);
        if v___x_704_ == 0 {
            if v___x_702_ == 0 {
                leanh::lean_dec_ref(v___f_703_);
                leanh::lean_dec_ref(v_arr_698_);
                return v_self_697_;
            } else {
                let mut v___x_705_: usize = 0;
                let mut v___x_706_: usize = 0;
                let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_705_ = 0usize;
                v___x_706_ = lean_usize_of_nat(v___x_700_);
                v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_701_,
                    v___f_703_,
                    v_arr_698_,
                    v___x_705_,
                    v___x_706_,
                    v_self_697_,
                );
                return v___x_707_;
            }
        } else {
            let mut v___x_708_: usize = 0;
            let mut v___x_709_: usize = 0;
            let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_708_ = 0usize;
            v___x_709_ = lean_usize_of_nat(v___x_700_);
            v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_701_,
                v___f_703_,
                v_arr_698_,
                v___x_708_,
                v___x_709_,
                v_self_697_,
            );
            return v___x_710_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_appendArray(
    mut v_00_u03b1_711_: *mut leanh::LeanObject,
    mut v_inst_712_: *mut leanh::LeanObject,
    mut v_inst_713_: *mut leanh::LeanObject,
    mut v_self_714_: *mut leanh::LeanObject,
    mut v_arr_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ =
        l_Lake_OrdHashSet_appendArray___redArg(v_inst_712_, v_inst_713_, v_self_714_, v_arr_715_);
    return v___x_716_;
}
pub unsafe fn l_Lake_OrdHashSet_instHAppendArray___redArg(
    mut v_inst_717_: *mut leanh::LeanObject,
    mut v_inst_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_appendArray as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_719_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_719_, 1, v_inst_717_);
    leanh::lean_closure_set(v___x_719_, 2, v_inst_718_);
    return v___x_719_;
}
pub unsafe fn l_Lake_OrdHashSet_instHAppendArray(
    mut v_00_u03b1_720_: *mut leanh::LeanObject,
    mut v_inst_721_: *mut leanh::LeanObject,
    mut v_inst_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_appendArray as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_723_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_723_, 1, v_inst_721_);
    leanh::lean_closure_set(v___x_723_, 2, v_inst_722_);
    return v___x_723_;
}
pub unsafe fn l_Lake_OrdHashSet_append___redArg(
    mut v_inst_724_: *mut leanh::LeanObject,
    mut v_inst_725_: *mut leanh::LeanObject,
    mut v_self_726_: *mut leanh::LeanObject,
    mut v_other_727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_728_ = leanh::lean_ctor_get(v_other_727_, 1);
    leanh::lean_inc_ref(v_toArray_728_);
    leanh::lean_dec_ref(v_other_727_);
    v___x_729_ = l_Lake_OrdHashSet_appendArray___redArg(
        v_inst_724_,
        v_inst_725_,
        v_self_726_,
        v_toArray_728_,
    );
    return v___x_729_;
}
pub unsafe fn l_Lake_OrdHashSet_append(
    mut v_00_u03b1_730_: *mut leanh::LeanObject,
    mut v_inst_731_: *mut leanh::LeanObject,
    mut v_inst_732_: *mut leanh::LeanObject,
    mut v_self_733_: *mut leanh::LeanObject,
    mut v_other_734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ =
        l_Lake_OrdHashSet_append___redArg(v_inst_731_, v_inst_732_, v_self_733_, v_other_734_);
    return v___x_735_;
}
pub unsafe fn l_Lake_OrdHashSet_instAppend___redArg(
    mut v_inst_736_: *mut leanh::LeanObject,
    mut v_inst_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ =
        leanh::lean_alloc_closure(l_Lake_OrdHashSet_append as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_738_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_738_, 1, v_inst_736_);
    leanh::lean_closure_set(v___x_738_, 2, v_inst_737_);
    return v___x_738_;
}
pub unsafe fn l_Lake_OrdHashSet_instAppend(
    mut v_00_u03b1_739_: *mut leanh::LeanObject,
    mut v_inst_740_: *mut leanh::LeanObject,
    mut v_inst_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_742_ =
        leanh::lean_alloc_closure(l_Lake_OrdHashSet_append as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_742_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_742_, 1, v_inst_740_);
    leanh::lean_closure_set(v___x_742_, 2, v_inst_741_);
    return v___x_742_;
}
pub unsafe fn l_Lake_OrdHashSet_ofArray___redArg(
    mut v_inst_743_: *mut leanh::LeanObject,
    mut v_inst_744_: *mut leanh::LeanObject,
    mut v_arr_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_746_ = lean_array_get_size(v_arr_745_);
    v___x_747_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_746_);
    v___x_748_ =
        l_Lake_OrdHashSet_appendArray___redArg(v_inst_743_, v_inst_744_, v___x_747_, v_arr_745_);
    return v___x_748_;
}
pub unsafe fn l_Lake_OrdHashSet_ofArray(
    mut v_00_u03b1_749_: *mut leanh::LeanObject,
    mut v_inst_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
    mut v_arr_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_750_, v_inst_751_, v_arr_752_);
    return v___x_753_;
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg___lam__0(
    mut v_f_754_: *mut leanh::LeanObject,
    mut v___x_755_: u8,
    mut v_v_756_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    v___x_757_ = leanh::lean_apply_1(v_f_754_, v_v_756_);
    v___x_758_ = (leanh::lean_unbox(v___x_757_) as u8);
    if v___x_758_ == 0 {
        return v___x_755_;
    } else {
        let mut v___x_759_: u8 = 0;
        v___x_759_ = 0;
        return v___x_759_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg___lam__0___boxed(
    mut v_f_760_: *mut leanh::LeanObject,
    mut v___x_761_: *mut leanh::LeanObject,
    mut v_v_762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_83__boxed_763_: u8 = 0;
    let mut v_res_764_: u8 = 0;
    let mut v_r_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_83__boxed_763_ = (leanh::lean_unbox(v___x_761_) as u8);
    v_res_764_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_760_, v___x_83__boxed_763_, v_v_762_);
    v_r_765_ = leanh::lean_box((v_res_764_) as usize);
    return v_r_765_;
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg(
    mut v_f_766_: *mut leanh::LeanObject,
    mut v_self_767_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    v_toArray_768_ = leanh::lean_ctor_get(v_self_767_, 1);
    leanh::lean_inc_ref(v_toArray_768_);
    leanh::lean_dec_ref(v_self_767_);
    v___x_769_ = leanh::lean_unsigned_to_nat(0);
    v___x_770_ = lean_array_get_size(v_toArray_768_);
    v___x_771_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_772_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
    if v___x_772_ == 0 {
        let mut v___x_773_: u8 = 0;
        leanh::lean_dec_ref(v_toArray_768_);
        leanh::lean_dec_ref(v_f_766_);
        v___x_773_ = 1;
        return v___x_773_;
    } else {
        if v___x_772_ == 0 {
            leanh::lean_dec_ref(v_toArray_768_);
            leanh::lean_dec_ref(v_f_766_);
            return v___x_772_;
        } else {
            let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_776_: usize = 0;
            let mut v___x_777_: usize = 0;
            let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_779_: u8 = 0;
            v___x_774_ = leanh::lean_box((v___x_772_) as usize);
            v___f_775_ = leanh::lean_alloc_closure(
                l_Lake_OrdHashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_775_, 0, v_f_766_);
            leanh::lean_closure_set(v___f_775_, 1, v___x_774_);
            v___x_776_ = 0usize;
            v___x_777_ = lean_usize_of_nat(v___x_770_);
            v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_771_,
                v___f_775_,
                v_toArray_768_,
                v___x_776_,
                v___x_777_,
            );
            v___x_779_ = (leanh::lean_unbox(v___x_778_) as u8);
            leanh::lean_dec(v___x_778_);
            if v___x_779_ == 0 {
                return v___x_772_;
            } else {
                let mut v___x_780_: u8 = 0;
                v___x_780_ = 0;
                return v___x_780_;
            }
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg___boxed(
    mut v_f_781_: *mut leanh::LeanObject,
    mut v_self_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: u8 = 0;
    let mut v_r_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lake_OrdHashSet_all___redArg(v_f_781_, v_self_782_);
    v_r_784_ = leanh::lean_box((v_res_783_) as usize);
    return v_r_784_;
}
pub unsafe fn l_Lake_OrdHashSet_all(
    mut v_00_u03b1_785_: *mut leanh::LeanObject,
    mut v_inst_786_: *mut leanh::LeanObject,
    mut v_inst_787_: *mut leanh::LeanObject,
    mut v_f_788_: *mut leanh::LeanObject,
    mut v_self_789_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    v_toArray_790_ = leanh::lean_ctor_get(v_self_789_, 1);
    leanh::lean_inc_ref(v_toArray_790_);
    leanh::lean_dec_ref(v_self_789_);
    v___x_791_ = leanh::lean_unsigned_to_nat(0);
    v___x_792_ = lean_array_get_size(v_toArray_790_);
    v___x_793_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_794_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
    if v___x_794_ == 0 {
        let mut v___x_795_: u8 = 0;
        leanh::lean_dec_ref(v_toArray_790_);
        leanh::lean_dec_ref(v_f_788_);
        v___x_795_ = 1;
        return v___x_795_;
    } else {
        if v___x_794_ == 0 {
            leanh::lean_dec_ref(v_toArray_790_);
            leanh::lean_dec_ref(v_f_788_);
            return v___x_794_;
        } else {
            let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_797_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_798_: usize = 0;
            let mut v___x_799_: usize = 0;
            let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            v___x_796_ = leanh::lean_box((v___x_794_) as usize);
            v___f_797_ = leanh::lean_alloc_closure(
                l_Lake_OrdHashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_797_, 0, v_f_788_);
            leanh::lean_closure_set(v___f_797_, 1, v___x_796_);
            v___x_798_ = 0usize;
            v___x_799_ = lean_usize_of_nat(v___x_792_);
            v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_793_,
                v___f_797_,
                v_toArray_790_,
                v___x_798_,
                v___x_799_,
            );
            v___x_801_ = (leanh::lean_unbox(v___x_800_) as u8);
            leanh::lean_dec(v___x_800_);
            if v___x_801_ == 0 {
                return v___x_794_;
            } else {
                let mut v___x_802_: u8 = 0;
                v___x_802_ = 0;
                return v___x_802_;
            }
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_all___boxed(
    mut v_00_u03b1_803_: *mut leanh::LeanObject,
    mut v_inst_804_: *mut leanh::LeanObject,
    mut v_inst_805_: *mut leanh::LeanObject,
    mut v_f_806_: *mut leanh::LeanObject,
    mut v_self_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: u8 = 0;
    let mut v_r_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lake_OrdHashSet_all(
        v_00_u03b1_803_,
        v_inst_804_,
        v_inst_805_,
        v_f_806_,
        v_self_807_,
    );
    leanh::lean_dec_ref(v_inst_805_);
    leanh::lean_dec_ref(v_inst_804_);
    v_r_809_ = leanh::lean_box((v_res_808_) as usize);
    return v_r_809_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___lam__0(
    mut v_f_810_: *mut leanh::LeanObject,
    mut v_x_811_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    v___x_812_ = leanh::lean_apply_1(v_f_810_, v_x_811_);
    v___x_813_ = (leanh::lean_unbox(v___x_812_) as u8);
    return v___x_813_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___lam__0___boxed(
    mut v_f_814_: *mut leanh::LeanObject,
    mut v_x_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: u8 = 0;
    let mut v_r_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_814_, v_x_815_);
    v_r_817_ = leanh::lean_box((v_res_816_) as usize);
    return v_r_817_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg(
    mut v_f_818_: *mut leanh::LeanObject,
    mut v_self_819_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: u8 = 0;
    v_toArray_820_ = leanh::lean_ctor_get(v_self_819_, 1);
    leanh::lean_inc_ref(v_toArray_820_);
    leanh::lean_dec_ref(v_self_819_);
    v___x_821_ = leanh::lean_unsigned_to_nat(0);
    v___x_822_ = lean_array_get_size(v_toArray_820_);
    v___x_823_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_824_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
    if v___x_824_ == 0 {
        leanh::lean_dec_ref(v_toArray_820_);
        leanh::lean_dec_ref(v_f_818_);
        return v___x_824_;
    } else {
        if v___x_824_ == 0 {
            leanh::lean_dec_ref(v_toArray_820_);
            leanh::lean_dec_ref(v_f_818_);
            return v___x_824_;
        } else {
            let mut v___f_825_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_826_: usize = 0;
            let mut v___x_827_: usize = 0;
            let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_829_: u8 = 0;
            v___f_825_ = leanh::lean_alloc_closure(
                l_Lake_OrdHashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_825_, 0, v_f_818_);
            v___x_826_ = 0usize;
            v___x_827_ = lean_usize_of_nat(v___x_822_);
            v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_823_,
                v___f_825_,
                v_toArray_820_,
                v___x_826_,
                v___x_827_,
            );
            v___x_829_ = (leanh::lean_unbox(v___x_828_) as u8);
            leanh::lean_dec(v___x_828_);
            return v___x_829_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___boxed(
    mut v_f_830_: *mut leanh::LeanObject,
    mut v_self_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_832_: u8 = 0;
    let mut v_r_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lake_OrdHashSet_any___redArg(v_f_830_, v_self_831_);
    v_r_833_ = leanh::lean_box((v_res_832_) as usize);
    return v_r_833_;
}
pub unsafe fn l_Lake_OrdHashSet_any(
    mut v_00_u03b1_834_: *mut leanh::LeanObject,
    mut v_inst_835_: *mut leanh::LeanObject,
    mut v_inst_836_: *mut leanh::LeanObject,
    mut v_f_837_: *mut leanh::LeanObject,
    mut v_self_838_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toArray_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    v_toArray_839_ = leanh::lean_ctor_get(v_self_838_, 1);
    leanh::lean_inc_ref(v_toArray_839_);
    leanh::lean_dec_ref(v_self_838_);
    v___x_840_ = leanh::lean_unsigned_to_nat(0);
    v___x_841_ = lean_array_get_size(v_toArray_839_);
    v___x_842_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_843_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
    if v___x_843_ == 0 {
        leanh::lean_dec_ref(v_toArray_839_);
        leanh::lean_dec_ref(v_f_837_);
        return v___x_843_;
    } else {
        if v___x_843_ == 0 {
            leanh::lean_dec_ref(v_toArray_839_);
            leanh::lean_dec_ref(v_f_837_);
            return v___x_843_;
        } else {
            let mut v___f_844_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_845_: usize = 0;
            let mut v___x_846_: usize = 0;
            let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_848_: u8 = 0;
            v___f_844_ = leanh::lean_alloc_closure(
                l_Lake_OrdHashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_844_, 0, v_f_837_);
            v___x_845_ = 0usize;
            v___x_846_ = lean_usize_of_nat(v___x_841_);
            v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_842_,
                v___f_844_,
                v_toArray_839_,
                v___x_845_,
                v___x_846_,
            );
            v___x_848_ = (leanh::lean_unbox(v___x_847_) as u8);
            leanh::lean_dec(v___x_847_);
            return v___x_848_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_any___boxed(
    mut v_00_u03b1_849_: *mut leanh::LeanObject,
    mut v_inst_850_: *mut leanh::LeanObject,
    mut v_inst_851_: *mut leanh::LeanObject,
    mut v_f_852_: *mut leanh::LeanObject,
    mut v_self_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_854_: u8 = 0;
    let mut v_r_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lake_OrdHashSet_any(
        v_00_u03b1_849_,
        v_inst_850_,
        v_inst_851_,
        v_f_852_,
        v_self_853_,
    );
    leanh::lean_dec_ref(v_inst_851_);
    leanh::lean_dec_ref(v_inst_850_);
    v_r_855_ = leanh::lean_box((v_res_854_) as usize);
    return v_r_855_;
}
pub unsafe fn l_Lake_OrdHashSet_foldl___redArg___lam__0(
    mut v_f_856_: *mut leanh::LeanObject,
    mut v_x1_857_: *mut leanh::LeanObject,
    mut v_x2_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = leanh::lean_apply_2(v_f_856_, v_x1_857_, v_x2_858_);
    return v___x_859_;
}
pub unsafe fn l_Lake_OrdHashSet_foldl___redArg(
    mut v_f_860_: *mut leanh::LeanObject,
    mut v_init_861_: *mut leanh::LeanObject,
    mut v_self_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    v_toArray_863_ = leanh::lean_ctor_get(v_self_862_, 1);
    leanh::lean_inc_ref(v_toArray_863_);
    leanh::lean_dec_ref(v_self_862_);
    v___x_864_ = leanh::lean_unsigned_to_nat(0);
    v___x_865_ = lean_array_get_size(v_toArray_863_);
    v___x_866_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_867_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
    if v___x_867_ == 0 {
        leanh::lean_dec_ref(v_toArray_863_);
        leanh::lean_dec(v_f_860_);
        return v_init_861_;
    } else {
        let mut v___f_868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_869_: u8 = 0;
        v___f_868_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_868_, 0, v_f_860_);
        v___x_869_ = lean_nat_dec_le(v___x_865_, v___x_865_);
        if v___x_869_ == 0 {
            if v___x_867_ == 0 {
                leanh::lean_dec_ref(v___f_868_);
                leanh::lean_dec_ref(v_toArray_863_);
                return v_init_861_;
            } else {
                let mut v___x_870_: usize = 0;
                let mut v___x_871_: usize = 0;
                let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_870_ = 0usize;
                v___x_871_ = lean_usize_of_nat(v___x_865_);
                v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_866_,
                    v___f_868_,
                    v_toArray_863_,
                    v___x_870_,
                    v___x_871_,
                    v_init_861_,
                );
                return v___x_872_;
            }
        } else {
            let mut v___x_873_: usize = 0;
            let mut v___x_874_: usize = 0;
            let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_873_ = 0usize;
            v___x_874_ = lean_usize_of_nat(v___x_865_);
            v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_866_,
                v___f_868_,
                v_toArray_863_,
                v___x_873_,
                v___x_874_,
                v_init_861_,
            );
            return v___x_875_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldl(
    mut v_00_u03b1_876_: *mut leanh::LeanObject,
    mut v_inst_877_: *mut leanh::LeanObject,
    mut v_inst_878_: *mut leanh::LeanObject,
    mut v_00_u03b2_879_: *mut leanh::LeanObject,
    mut v_f_880_: *mut leanh::LeanObject,
    mut v_init_881_: *mut leanh::LeanObject,
    mut v_self_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    v_toArray_883_ = leanh::lean_ctor_get(v_self_882_, 1);
    leanh::lean_inc_ref(v_toArray_883_);
    leanh::lean_dec_ref(v_self_882_);
    v___x_884_ = leanh::lean_unsigned_to_nat(0);
    v___x_885_ = lean_array_get_size(v_toArray_883_);
    v___x_886_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_887_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
    if v___x_887_ == 0 {
        leanh::lean_dec_ref(v_toArray_883_);
        leanh::lean_dec(v_f_880_);
        return v_init_881_;
    } else {
        let mut v___f_888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_889_: u8 = 0;
        v___f_888_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_888_, 0, v_f_880_);
        v___x_889_ = lean_nat_dec_le(v___x_885_, v___x_885_);
        if v___x_889_ == 0 {
            if v___x_887_ == 0 {
                leanh::lean_dec_ref(v___f_888_);
                leanh::lean_dec_ref(v_toArray_883_);
                return v_init_881_;
            } else {
                let mut v___x_890_: usize = 0;
                let mut v___x_891_: usize = 0;
                let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_890_ = 0usize;
                v___x_891_ = lean_usize_of_nat(v___x_885_);
                v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_886_,
                    v___f_888_,
                    v_toArray_883_,
                    v___x_890_,
                    v___x_891_,
                    v_init_881_,
                );
                return v___x_892_;
            }
        } else {
            let mut v___x_893_: usize = 0;
            let mut v___x_894_: usize = 0;
            let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_893_ = 0usize;
            v___x_894_ = lean_usize_of_nat(v___x_885_);
            v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_886_,
                v___f_888_,
                v_toArray_883_,
                v___x_893_,
                v___x_894_,
                v_init_881_,
            );
            return v___x_895_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldl___boxed(
    mut v_00_u03b1_896_: *mut leanh::LeanObject,
    mut v_inst_897_: *mut leanh::LeanObject,
    mut v_inst_898_: *mut leanh::LeanObject,
    mut v_00_u03b2_899_: *mut leanh::LeanObject,
    mut v_f_900_: *mut leanh::LeanObject,
    mut v_init_901_: *mut leanh::LeanObject,
    mut v_self_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Lake_OrdHashSet_foldl(
        v_00_u03b1_896_,
        v_inst_897_,
        v_inst_898_,
        v_00_u03b2_899_,
        v_f_900_,
        v_init_901_,
        v_self_902_,
    );
    leanh::lean_dec_ref(v_inst_898_);
    leanh::lean_dec_ref(v_inst_897_);
    return v_res_903_;
}
pub unsafe fn l_Lake_OrdHashSet_foldlM___redArg(
    mut v_inst_904_: *mut leanh::LeanObject,
    mut v_f_905_: *mut leanh::LeanObject,
    mut v_init_906_: *mut leanh::LeanObject,
    mut v_self_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: u8 = 0;
    v_toArray_908_ = leanh::lean_ctor_get(v_self_907_, 1);
    leanh::lean_inc_ref(v_toArray_908_);
    leanh::lean_dec_ref(v_self_907_);
    v___x_909_ = leanh::lean_unsigned_to_nat(0);
    v___x_910_ = lean_array_get_size(v_toArray_908_);
    v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
    if v___x_911_ == 0 {
        let mut v_toApplicative_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_908_);
        leanh::lean_dec(v_f_905_);
        v_toApplicative_912_ = leanh::lean_ctor_get(v_inst_904_, 0);
        leanh::lean_inc_ref(v_toApplicative_912_);
        leanh::lean_dec_ref(v_inst_904_);
        v_toPure_913_ = leanh::lean_ctor_get(v_toApplicative_912_, 1);
        leanh::lean_inc(v_toPure_913_);
        leanh::lean_dec_ref(v_toApplicative_912_);
        v___x_914_ =
            leanh::lean_apply_2(v_toPure_913_, leanh::lean_box(0), v_init_906_);
        return v___x_914_;
    } else {
        let mut v___x_915_: u8 = 0;
        v___x_915_ = lean_nat_dec_le(v___x_910_, v___x_910_);
        if v___x_915_ == 0 {
            if v___x_911_ == 0 {
                let mut v_toApplicative_916_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_917_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toArray_908_);
                leanh::lean_dec(v_f_905_);
                v_toApplicative_916_ = leanh::lean_ctor_get(v_inst_904_, 0);
                leanh::lean_inc_ref(v_toApplicative_916_);
                leanh::lean_dec_ref(v_inst_904_);
                v_toPure_917_ = leanh::lean_ctor_get(v_toApplicative_916_, 1);
                leanh::lean_inc(v_toPure_917_);
                leanh::lean_dec_ref(v_toApplicative_916_);
                v___x_918_ = leanh::lean_apply_2(
                    v_toPure_917_,
                    leanh::lean_box(0),
                    v_init_906_,
                );
                return v___x_918_;
            } else {
                let mut v___x_919_: usize = 0;
                let mut v___x_920_: usize = 0;
                let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_919_ = 0usize;
                v___x_920_ = lean_usize_of_nat(v___x_910_);
                v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_904_,
                    v_f_905_,
                    v_toArray_908_,
                    v___x_919_,
                    v___x_920_,
                    v_init_906_,
                );
                return v___x_921_;
            }
        } else {
            let mut v___x_922_: usize = 0;
            let mut v___x_923_: usize = 0;
            let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_922_ = 0usize;
            v___x_923_ = lean_usize_of_nat(v___x_910_);
            v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_904_,
                v_f_905_,
                v_toArray_908_,
                v___x_922_,
                v___x_923_,
                v_init_906_,
            );
            return v___x_924_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldlM(
    mut v_00_u03b1_925_: *mut leanh::LeanObject,
    mut v_inst_926_: *mut leanh::LeanObject,
    mut v_inst_927_: *mut leanh::LeanObject,
    mut v_m_928_: *mut leanh::LeanObject,
    mut v_00_u03b2_929_: *mut leanh::LeanObject,
    mut v_inst_930_: *mut leanh::LeanObject,
    mut v_f_931_: *mut leanh::LeanObject,
    mut v_init_932_: *mut leanh::LeanObject,
    mut v_self_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: u8 = 0;
    v_toArray_934_ = leanh::lean_ctor_get(v_self_933_, 1);
    leanh::lean_inc_ref(v_toArray_934_);
    leanh::lean_dec_ref(v_self_933_);
    v___x_935_ = leanh::lean_unsigned_to_nat(0);
    v___x_936_ = lean_array_get_size(v_toArray_934_);
    v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
    if v___x_937_ == 0 {
        let mut v_toApplicative_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_934_);
        leanh::lean_dec(v_f_931_);
        v_toApplicative_938_ = leanh::lean_ctor_get(v_inst_930_, 0);
        leanh::lean_inc_ref(v_toApplicative_938_);
        leanh::lean_dec_ref(v_inst_930_);
        v_toPure_939_ = leanh::lean_ctor_get(v_toApplicative_938_, 1);
        leanh::lean_inc(v_toPure_939_);
        leanh::lean_dec_ref(v_toApplicative_938_);
        v___x_940_ =
            leanh::lean_apply_2(v_toPure_939_, leanh::lean_box(0), v_init_932_);
        return v___x_940_;
    } else {
        let mut v___x_941_: u8 = 0;
        v___x_941_ = lean_nat_dec_le(v___x_936_, v___x_936_);
        if v___x_941_ == 0 {
            if v___x_937_ == 0 {
                let mut v_toApplicative_942_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_943_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_toArray_934_);
                leanh::lean_dec(v_f_931_);
                v_toApplicative_942_ = leanh::lean_ctor_get(v_inst_930_, 0);
                leanh::lean_inc_ref(v_toApplicative_942_);
                leanh::lean_dec_ref(v_inst_930_);
                v_toPure_943_ = leanh::lean_ctor_get(v_toApplicative_942_, 1);
                leanh::lean_inc(v_toPure_943_);
                leanh::lean_dec_ref(v_toApplicative_942_);
                v___x_944_ = leanh::lean_apply_2(
                    v_toPure_943_,
                    leanh::lean_box(0),
                    v_init_932_,
                );
                return v___x_944_;
            } else {
                let mut v___x_945_: usize = 0;
                let mut v___x_946_: usize = 0;
                let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_945_ = 0usize;
                v___x_946_ = lean_usize_of_nat(v___x_936_);
                v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_930_,
                    v_f_931_,
                    v_toArray_934_,
                    v___x_945_,
                    v___x_946_,
                    v_init_932_,
                );
                return v___x_947_;
            }
        } else {
            let mut v___x_948_: usize = 0;
            let mut v___x_949_: usize = 0;
            let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_948_ = 0usize;
            v___x_949_ = lean_usize_of_nat(v___x_936_);
            v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_930_,
                v_f_931_,
                v_toArray_934_,
                v___x_948_,
                v___x_949_,
                v_init_932_,
            );
            return v___x_950_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldlM___boxed(
    mut v_00_u03b1_951_: *mut leanh::LeanObject,
    mut v_inst_952_: *mut leanh::LeanObject,
    mut v_inst_953_: *mut leanh::LeanObject,
    mut v_m_954_: *mut leanh::LeanObject,
    mut v_00_u03b2_955_: *mut leanh::LeanObject,
    mut v_inst_956_: *mut leanh::LeanObject,
    mut v_f_957_: *mut leanh::LeanObject,
    mut v_init_958_: *mut leanh::LeanObject,
    mut v_self_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Lake_OrdHashSet_foldlM(
        v_00_u03b1_951_,
        v_inst_952_,
        v_inst_953_,
        v_m_954_,
        v_00_u03b2_955_,
        v_inst_956_,
        v_f_957_,
        v_init_958_,
        v_self_959_,
    );
    leanh::lean_dec_ref(v_inst_953_);
    leanh::lean_dec_ref(v_inst_952_);
    return v_res_960_;
}
pub unsafe fn l_Lake_OrdHashSet_foldr___redArg(
    mut v_f_961_: *mut leanh::LeanObject,
    mut v_init_962_: *mut leanh::LeanObject,
    mut v_self_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    v_toArray_964_ = leanh::lean_ctor_get(v_self_963_, 1);
    leanh::lean_inc_ref(v_toArray_964_);
    leanh::lean_dec_ref(v_self_963_);
    v___x_965_ = lean_array_get_size(v_toArray_964_);
    v___x_966_ = leanh::lean_unsigned_to_nat(0);
    v___x_967_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_965_);
    if v___x_968_ == 0 {
        leanh::lean_dec_ref(v_toArray_964_);
        leanh::lean_dec(v_f_961_);
        return v_init_962_;
    } else {
        let mut v___f_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: usize = 0;
        let mut v___x_971_: usize = 0;
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_969_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_969_, 0, v_f_961_);
        v___x_970_ = lean_usize_of_nat(v___x_965_);
        v___x_971_ = 0usize;
        v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_967_,
            v___f_969_,
            v_toArray_964_,
            v___x_970_,
            v___x_971_,
            v_init_962_,
        );
        return v___x_972_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldr(
    mut v_00_u03b1_973_: *mut leanh::LeanObject,
    mut v_inst_974_: *mut leanh::LeanObject,
    mut v_inst_975_: *mut leanh::LeanObject,
    mut v_00_u03b2_976_: *mut leanh::LeanObject,
    mut v_f_977_: *mut leanh::LeanObject,
    mut v_init_978_: *mut leanh::LeanObject,
    mut v_self_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    v_toArray_980_ = leanh::lean_ctor_get(v_self_979_, 1);
    leanh::lean_inc_ref(v_toArray_980_);
    leanh::lean_dec_ref(v_self_979_);
    v___x_981_ = lean_array_get_size(v_toArray_980_);
    v___x_982_ = leanh::lean_unsigned_to_nat(0);
    v___x_983_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_984_ = lean_nat_dec_lt(v___x_982_, v___x_981_);
    if v___x_984_ == 0 {
        leanh::lean_dec_ref(v_toArray_980_);
        leanh::lean_dec(v_f_977_);
        return v_init_978_;
    } else {
        let mut v___f_985_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: usize = 0;
        let mut v___x_987_: usize = 0;
        let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_985_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_985_, 0, v_f_977_);
        v___x_986_ = lean_usize_of_nat(v___x_981_);
        v___x_987_ = 0usize;
        v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_983_,
            v___f_985_,
            v_toArray_980_,
            v___x_986_,
            v___x_987_,
            v_init_978_,
        );
        return v___x_988_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldr___boxed(
    mut v_00_u03b1_989_: *mut leanh::LeanObject,
    mut v_inst_990_: *mut leanh::LeanObject,
    mut v_inst_991_: *mut leanh::LeanObject,
    mut v_00_u03b2_992_: *mut leanh::LeanObject,
    mut v_f_993_: *mut leanh::LeanObject,
    mut v_init_994_: *mut leanh::LeanObject,
    mut v_self_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Lake_OrdHashSet_foldr(
        v_00_u03b1_989_,
        v_inst_990_,
        v_inst_991_,
        v_00_u03b2_992_,
        v_f_993_,
        v_init_994_,
        v_self_995_,
    );
    leanh::lean_dec_ref(v_inst_991_);
    leanh::lean_dec_ref(v_inst_990_);
    return v_res_996_;
}
pub unsafe fn l_Lake_OrdHashSet_foldrM___redArg(
    mut v_inst_997_: *mut leanh::LeanObject,
    mut v_f_998_: *mut leanh::LeanObject,
    mut v_init_999_: *mut leanh::LeanObject,
    mut v_self_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    v_toArray_1001_ = leanh::lean_ctor_get(v_self_1000_, 1);
    leanh::lean_inc_ref(v_toArray_1001_);
    leanh::lean_dec_ref(v_self_1000_);
    v___x_1002_ = lean_array_get_size(v_toArray_1001_);
    v___x_1003_ = leanh::lean_unsigned_to_nat(0);
    v___x_1004_ = lean_nat_dec_lt(v___x_1003_, v___x_1002_);
    if v___x_1004_ == 0 {
        let mut v_toApplicative_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1001_);
        leanh::lean_dec(v_f_998_);
        v_toApplicative_1005_ = leanh::lean_ctor_get(v_inst_997_, 0);
        leanh::lean_inc_ref(v_toApplicative_1005_);
        leanh::lean_dec_ref(v_inst_997_);
        v_toPure_1006_ = leanh::lean_ctor_get(v_toApplicative_1005_, 1);
        leanh::lean_inc(v_toPure_1006_);
        leanh::lean_dec_ref(v_toApplicative_1005_);
        v___x_1007_ =
            leanh::lean_apply_2(v_toPure_1006_, leanh::lean_box(0), v_init_999_);
        return v___x_1007_;
    } else {
        let mut v___x_1008_: usize = 0;
        let mut v___x_1009_: usize = 0;
        let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1008_ = lean_usize_of_nat(v___x_1002_);
        v___x_1009_ = 0usize;
        v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_997_,
            v_f_998_,
            v_toArray_1001_,
            v___x_1008_,
            v___x_1009_,
            v_init_999_,
        );
        return v___x_1010_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldrM(
    mut v_00_u03b1_1011_: *mut leanh::LeanObject,
    mut v_inst_1012_: *mut leanh::LeanObject,
    mut v_inst_1013_: *mut leanh::LeanObject,
    mut v_m_1014_: *mut leanh::LeanObject,
    mut v_00_u03b2_1015_: *mut leanh::LeanObject,
    mut v_inst_1016_: *mut leanh::LeanObject,
    mut v_f_1017_: *mut leanh::LeanObject,
    mut v_init_1018_: *mut leanh::LeanObject,
    mut v_self_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    v_toArray_1020_ = leanh::lean_ctor_get(v_self_1019_, 1);
    leanh::lean_inc_ref(v_toArray_1020_);
    leanh::lean_dec_ref(v_self_1019_);
    v___x_1021_ = lean_array_get_size(v_toArray_1020_);
    v___x_1022_ = leanh::lean_unsigned_to_nat(0);
    v___x_1023_ = lean_nat_dec_lt(v___x_1022_, v___x_1021_);
    if v___x_1023_ == 0 {
        let mut v_toApplicative_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1020_);
        leanh::lean_dec(v_f_1017_);
        v_toApplicative_1024_ = leanh::lean_ctor_get(v_inst_1016_, 0);
        leanh::lean_inc_ref(v_toApplicative_1024_);
        leanh::lean_dec_ref(v_inst_1016_);
        v_toPure_1025_ = leanh::lean_ctor_get(v_toApplicative_1024_, 1);
        leanh::lean_inc(v_toPure_1025_);
        leanh::lean_dec_ref(v_toApplicative_1024_);
        v___x_1026_ =
            leanh::lean_apply_2(v_toPure_1025_, leanh::lean_box(0), v_init_1018_);
        return v___x_1026_;
    } else {
        let mut v___x_1027_: usize = 0;
        let mut v___x_1028_: usize = 0;
        let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1027_ = lean_usize_of_nat(v___x_1021_);
        v___x_1028_ = 0usize;
        v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_1016_,
            v_f_1017_,
            v_toArray_1020_,
            v___x_1027_,
            v___x_1028_,
            v_init_1018_,
        );
        return v___x_1029_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_foldrM___boxed(
    mut v_00_u03b1_1030_: *mut leanh::LeanObject,
    mut v_inst_1031_: *mut leanh::LeanObject,
    mut v_inst_1032_: *mut leanh::LeanObject,
    mut v_m_1033_: *mut leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut leanh::LeanObject,
    mut v_inst_1035_: *mut leanh::LeanObject,
    mut v_f_1036_: *mut leanh::LeanObject,
    mut v_init_1037_: *mut leanh::LeanObject,
    mut v_self_1038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Lake_OrdHashSet_foldrM(
        v_00_u03b1_1030_,
        v_inst_1031_,
        v_inst_1032_,
        v_m_1033_,
        v_00_u03b2_1034_,
        v_inst_1035_,
        v_f_1036_,
        v_init_1037_,
        v_self_1038_,
    );
    leanh::lean_dec_ref(v_inst_1032_);
    leanh::lean_dec_ref(v_inst_1031_);
    return v_res_1039_;
}
pub unsafe fn l_Lake_OrdHashSet_forM___redArg___lam__0(
    mut v_f_1040_: *mut leanh::LeanObject,
    mut v_x_1041_: *mut leanh::LeanObject,
    mut v___y_1042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = leanh::lean_apply_1(v_f_1040_, v___y_1042_);
    return v___x_1043_;
}
pub unsafe fn l_Lake_OrdHashSet_forM___redArg(
    mut v_inst_1044_: *mut leanh::LeanObject,
    mut v_f_1045_: *mut leanh::LeanObject,
    mut v_self_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    v_toArray_1047_ = leanh::lean_ctor_get(v_self_1046_, 1);
    leanh::lean_inc_ref(v_toArray_1047_);
    leanh::lean_dec_ref(v_self_1046_);
    v___x_1048_ = leanh::lean_unsigned_to_nat(0);
    v___x_1049_ = lean_array_get_size(v_toArray_1047_);
    v___x_1050_ = leanh::lean_box(0);
    v___x_1051_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
    if v___x_1051_ == 0 {
        let mut v_toApplicative_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1047_);
        leanh::lean_dec(v_f_1045_);
        v_toApplicative_1052_ = leanh::lean_ctor_get(v_inst_1044_, 0);
        leanh::lean_inc_ref(v_toApplicative_1052_);
        leanh::lean_dec_ref(v_inst_1044_);
        v_toPure_1053_ = leanh::lean_ctor_get(v_toApplicative_1052_, 1);
        leanh::lean_inc(v_toPure_1053_);
        leanh::lean_dec_ref(v_toApplicative_1052_);
        v___x_1054_ =
            leanh::lean_apply_2(v_toPure_1053_, leanh::lean_box(0), v___x_1050_);
        return v___x_1054_;
    } else {
        let mut v___f_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: u8 = 0;
        v___f_1055_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1055_, 0, v_f_1045_);
        v___x_1056_ = lean_nat_dec_le(v___x_1049_, v___x_1049_);
        if v___x_1056_ == 0 {
            if v___x_1051_ == 0 {
                let mut v_toApplicative_1057_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1055_);
                leanh::lean_dec_ref(v_toArray_1047_);
                v_toApplicative_1057_ = leanh::lean_ctor_get(v_inst_1044_, 0);
                leanh::lean_inc_ref(v_toApplicative_1057_);
                leanh::lean_dec_ref(v_inst_1044_);
                v_toPure_1058_ = leanh::lean_ctor_get(v_toApplicative_1057_, 1);
                leanh::lean_inc(v_toPure_1058_);
                leanh::lean_dec_ref(v_toApplicative_1057_);
                v___x_1059_ = leanh::lean_apply_2(
                    v_toPure_1058_,
                    leanh::lean_box(0),
                    v___x_1050_,
                );
                return v___x_1059_;
            } else {
                let mut v___x_1060_: usize = 0;
                let mut v___x_1061_: usize = 0;
                let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1060_ = 0usize;
                v___x_1061_ = lean_usize_of_nat(v___x_1049_);
                v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1044_,
                    v___f_1055_,
                    v_toArray_1047_,
                    v___x_1060_,
                    v___x_1061_,
                    v___x_1050_,
                );
                return v___x_1062_;
            }
        } else {
            let mut v___x_1063_: usize = 0;
            let mut v___x_1064_: usize = 0;
            let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1063_ = 0usize;
            v___x_1064_ = lean_usize_of_nat(v___x_1049_);
            v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1044_,
                v___f_1055_,
                v_toArray_1047_,
                v___x_1063_,
                v___x_1064_,
                v___x_1050_,
            );
            return v___x_1065_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_forM(
    mut v_00_u03b1_1066_: *mut leanh::LeanObject,
    mut v_inst_1067_: *mut leanh::LeanObject,
    mut v_inst_1068_: *mut leanh::LeanObject,
    mut v_m_1069_: *mut leanh::LeanObject,
    mut v_inst_1070_: *mut leanh::LeanObject,
    mut v_f_1071_: *mut leanh::LeanObject,
    mut v_self_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    v_toArray_1073_ = leanh::lean_ctor_get(v_self_1072_, 1);
    leanh::lean_inc_ref(v_toArray_1073_);
    leanh::lean_dec_ref(v_self_1072_);
    v___x_1074_ = leanh::lean_unsigned_to_nat(0);
    v___x_1075_ = lean_array_get_size(v_toArray_1073_);
    v___x_1076_ = leanh::lean_box(0);
    v___x_1077_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
    if v___x_1077_ == 0 {
        let mut v_toApplicative_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toArray_1073_);
        leanh::lean_dec(v_f_1071_);
        v_toApplicative_1078_ = leanh::lean_ctor_get(v_inst_1070_, 0);
        leanh::lean_inc_ref(v_toApplicative_1078_);
        leanh::lean_dec_ref(v_inst_1070_);
        v_toPure_1079_ = leanh::lean_ctor_get(v_toApplicative_1078_, 1);
        leanh::lean_inc(v_toPure_1079_);
        leanh::lean_dec_ref(v_toApplicative_1078_);
        v___x_1080_ =
            leanh::lean_apply_2(v_toPure_1079_, leanh::lean_box(0), v___x_1076_);
        return v___x_1080_;
    } else {
        let mut v___f_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: u8 = 0;
        v___f_1081_ = leanh::lean_alloc_closure(
            l_Lake_OrdHashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1081_, 0, v_f_1071_);
        v___x_1082_ = lean_nat_dec_le(v___x_1075_, v___x_1075_);
        if v___x_1082_ == 0 {
            if v___x_1077_ == 0 {
                let mut v_toApplicative_1083_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1081_);
                leanh::lean_dec_ref(v_toArray_1073_);
                v_toApplicative_1083_ = leanh::lean_ctor_get(v_inst_1070_, 0);
                leanh::lean_inc_ref(v_toApplicative_1083_);
                leanh::lean_dec_ref(v_inst_1070_);
                v_toPure_1084_ = leanh::lean_ctor_get(v_toApplicative_1083_, 1);
                leanh::lean_inc(v_toPure_1084_);
                leanh::lean_dec_ref(v_toApplicative_1083_);
                v___x_1085_ = leanh::lean_apply_2(
                    v_toPure_1084_,
                    leanh::lean_box(0),
                    v___x_1076_,
                );
                return v___x_1085_;
            } else {
                let mut v___x_1086_: usize = 0;
                let mut v___x_1087_: usize = 0;
                let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1086_ = 0usize;
                v___x_1087_ = lean_usize_of_nat(v___x_1075_);
                v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1070_,
                    v___f_1081_,
                    v_toArray_1073_,
                    v___x_1086_,
                    v___x_1087_,
                    v___x_1076_,
                );
                return v___x_1088_;
            }
        } else {
            let mut v___x_1089_: usize = 0;
            let mut v___x_1090_: usize = 0;
            let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1089_ = 0usize;
            v___x_1090_ = lean_usize_of_nat(v___x_1075_);
            v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1070_,
                v___f_1081_,
                v_toArray_1073_,
                v___x_1089_,
                v___x_1090_,
                v___x_1076_,
            );
            return v___x_1091_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_forM___boxed(
    mut v_00_u03b1_1092_: *mut leanh::LeanObject,
    mut v_inst_1093_: *mut leanh::LeanObject,
    mut v_inst_1094_: *mut leanh::LeanObject,
    mut v_m_1095_: *mut leanh::LeanObject,
    mut v_inst_1096_: *mut leanh::LeanObject,
    mut v_f_1097_: *mut leanh::LeanObject,
    mut v_self_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lake_OrdHashSet_forM(
        v_00_u03b1_1092_,
        v_inst_1093_,
        v_inst_1094_,
        v_m_1095_,
        v_inst_1096_,
        v_f_1097_,
        v_self_1098_,
    );
    leanh::lean_dec_ref(v_inst_1094_);
    leanh::lean_dec_ref(v_inst_1093_);
    return v_res_1099_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn___redArg___lam__0(
    mut v_f_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_x_1102_: *mut leanh::LeanObject,
    mut v___y_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = leanh::lean_apply_2(v_f_1100_, v_a_1101_, v___y_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn___redArg(
    mut v_inst_1105_: *mut leanh::LeanObject,
    mut v_self_1106_: *mut leanh::LeanObject,
    mut v_init_1107_: *mut leanh::LeanObject,
    mut v_f_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1111_: usize = 0;
    let mut v___x_1112_: usize = 0;
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1109_ = leanh::lean_ctor_get(v_self_1106_, 1);
    leanh::lean_inc_ref(v_toArray_1109_);
    leanh::lean_dec_ref(v_self_1106_);
    v___f_1110_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1110_, 0, v_f_1108_);
    v_sz_1111_ = lean_array_size(v_toArray_1109_);
    v___x_1112_ = 0usize;
    v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1105_,
        v_toArray_1109_,
        v___f_1110_,
        v_sz_1111_,
        v___x_1112_,
        v_init_1107_,
    );
    return v___x_1113_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn(
    mut v_00_u03b1_1114_: *mut leanh::LeanObject,
    mut v_inst_1115_: *mut leanh::LeanObject,
    mut v_inst_1116_: *mut leanh::LeanObject,
    mut v_m_1117_: *mut leanh::LeanObject,
    mut v_00_u03b2_1118_: *mut leanh::LeanObject,
    mut v_inst_1119_: *mut leanh::LeanObject,
    mut v_self_1120_: *mut leanh::LeanObject,
    mut v_init_1121_: *mut leanh::LeanObject,
    mut v_f_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1123_ = leanh::lean_ctor_get(v_self_1120_, 1);
    leanh::lean_inc_ref(v_toArray_1123_);
    leanh::lean_dec_ref(v_self_1120_);
    v___f_1124_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1124_, 0, v_f_1122_);
    v_sz_1125_ = lean_array_size(v_toArray_1123_);
    v___x_1126_ = 0usize;
    v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1119_,
        v_toArray_1123_,
        v___f_1124_,
        v_sz_1125_,
        v___x_1126_,
        v_init_1121_,
    );
    return v___x_1127_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn___boxed(
    mut v_00_u03b1_1128_: *mut leanh::LeanObject,
    mut v_inst_1129_: *mut leanh::LeanObject,
    mut v_inst_1130_: *mut leanh::LeanObject,
    mut v_m_1131_: *mut leanh::LeanObject,
    mut v_00_u03b2_1132_: *mut leanh::LeanObject,
    mut v_inst_1133_: *mut leanh::LeanObject,
    mut v_self_1134_: *mut leanh::LeanObject,
    mut v_init_1135_: *mut leanh::LeanObject,
    mut v_f_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lake_OrdHashSet_forIn(
        v_00_u03b1_1128_,
        v_inst_1129_,
        v_inst_1130_,
        v_m_1131_,
        v_00_u03b2_1132_,
        v_inst_1133_,
        v_self_1134_,
        v_init_1135_,
        v_f_1136_,
    );
    leanh::lean_dec_ref(v_inst_1130_);
    leanh::lean_dec_ref(v_inst_1129_);
    return v_res_1137_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v_a_1139_: *mut leanh::LeanObject,
    mut v_x_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = leanh::lean_apply_2(v___y_1138_, v_a_1139_, v___y_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(
    mut v_inst_1143_: *mut leanh::LeanObject,
    mut v_00_u03b2_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toArray_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1150_: usize = 0;
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toArray_1148_ = leanh::lean_ctor_get(v___y_1145_, 1);
    leanh::lean_inc_ref(v_toArray_1148_);
    leanh::lean_dec_ref(v___y_1145_);
    v___f_1149_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1149_, 0, v___y_1147_);
    v_sz_1150_ = lean_array_size(v_toArray_1148_);
    v___x_1151_ = 0usize;
    v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1143_,
        v_toArray_1148_,
        v___f_1149_,
        v_sz_1150_,
        v___x_1151_,
        v___y_1146_,
    );
    return v___x_1152_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___redArg(
    mut v_inst_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1154_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1154_, 0, v_inst_1153_);
    return v___f_1154_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad(
    mut v_00_u03b1_1155_: *mut leanh::LeanObject,
    mut v_inst_1156_: *mut leanh::LeanObject,
    mut v_inst_1157_: *mut leanh::LeanObject,
    mut v_m_1158_: *mut leanh::LeanObject,
    mut v_inst_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1160_ = leanh::lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1160_, 0, v_inst_1159_);
    return v___f_1160_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___boxed(
    mut v_00_u03b1_1161_: *mut leanh::LeanObject,
    mut v_inst_1162_: *mut leanh::LeanObject,
    mut v_inst_1163_: *mut leanh::LeanObject,
    mut v_m_1164_: *mut leanh::LeanObject,
    mut v_inst_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lake_OrdHashSet_instForInOfMonad(
        v_00_u03b1_1161_,
        v_inst_1162_,
        v_inst_1163_,
        v_m_1164_,
        v_inst_1165_,
    );
    leanh::lean_dec_ref(v_inst_1163_);
    leanh::lean_dec_ref(v_inst_1162_);
    return v_res_1166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OrdHashSet(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OrdHashSet(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OrdHashSet(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OrdHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_OrdHashSet(builtin);
}