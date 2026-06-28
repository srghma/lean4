// Lean compiler output
// Module: Lake.Util.OrdHashSet
// Imports: Std.Data.HashSet.Basic
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lake_OrdHashSet_instCoeHashSet___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_instCoeHashSet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_instCoeHashSet___closed__0_value) as *mut LeanObject;
static mut l_Lake_OrdHashSet_empty___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_OrdHashSet_empty___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_OrdHashSet_empty___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_OrdHashSet_empty___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_empty___closed__2_value) as *mut LeanObject;
static mut l_Lake_OrdHashSet_empty___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_OrdHashSet_empty___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__8_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_OrdHashSet_appendArray___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_OrdHashSet_appendArray___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_OrdHashSet_appendArray___redArg___closed__9_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___lam__0(
    mut v_self_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toHashSet_585_: *mut LeanObject = core::ptr::null_mut();
    v_toHashSet_585_ = lean_ctor_get(v_self_584_, 0);
    lean_inc_ref(v_toHashSet_585_);
    return v_toHashSet_585_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed(
    mut v_self_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_587_: *mut LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Lake_OrdHashSet_instCoeHashSet___lam__0(v_self_586_);
    lean_dec_ref(v_self_586_);
    return v_res_587_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet(
    mut v_00_u03b1_589_: *mut LeanObject,
    mut v_inst_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_592_: *mut LeanObject = core::ptr::null_mut();
    v___f_592_ = l_Lake_OrdHashSet_instCoeHashSet___closed__0;
    return v___f_592_;
}
pub unsafe fn l_Lake_OrdHashSet_instCoeHashSet___boxed(
    mut v_00_u03b1_593_: *mut LeanObject,
    mut v_inst_594_: *mut LeanObject,
    mut v_inst_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_596_: *mut LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lake_OrdHashSet_instCoeHashSet(v_00_u03b1_593_, v_inst_594_, v_inst_595_);
    lean_dec_ref(v_inst_595_);
    lean_dec_ref(v_inst_594_);
    return v_res_596_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__0() -> *mut LeanObject {
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_597_ = lean_box(0);
    v___x_598_ = lean_unsigned_to_nat(16);
    v___x_599_ = lean_mk_array(v___x_598_, v___x_597_);
    return v___x_599_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__1() -> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__0_once),
        _init_l_Lake_OrdHashSet_empty___closed__0,
    );
    v___x_601_ = lean_unsigned_to_nat(0);
    v___x_602_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_602_, 0, v___x_601_);
    lean_ctor_set(v___x_602_, 1, v___x_600_);
    return v___x_602_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___closed__3() -> *mut LeanObject {
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_605_ = l_Lake_OrdHashSet_empty___closed__2;
    v___x_606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1_once),
        _init_l_Lake_OrdHashSet_empty___closed__1,
    );
    v___x_607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_607_, 0, v___x_606_);
    lean_ctor_set(v___x_607_, 1, v___x_605_);
    return v___x_607_;
}
pub unsafe fn l_Lake_OrdHashSet_empty(
    mut v_00_u03b1_608_: *mut LeanObject,
    mut v_inst_609_: *mut LeanObject,
    mut v_inst_610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    v___x_611_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__3),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__3_once),
        _init_l_Lake_OrdHashSet_empty___closed__3,
    );
    return v___x_611_;
}
pub unsafe fn l_Lake_OrdHashSet_empty___boxed(
    mut v_00_u03b1_612_: *mut LeanObject,
    mut v_inst_613_: *mut LeanObject,
    mut v_inst_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_615_: *mut LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Lake_OrdHashSet_empty(v_00_u03b1_612_, v_inst_613_, v_inst_614_);
    lean_dec_ref(v_inst_614_);
    lean_dec_ref(v_inst_613_);
    return v_res_615_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___redArg(
    mut v_inst_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_616_, v_inst_617_);
    return v___x_618_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(
    mut v_inst_619_: *mut LeanObject,
    mut v_inst_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lake_OrdHashSet_instEmptyCollection___redArg(v_inst_619_, v_inst_620_);
    lean_dec_ref(v_inst_620_);
    lean_dec_ref(v_inst_619_);
    return v_res_621_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection(
    mut v_00_u03b1_622_: *mut LeanObject,
    mut v_inst_623_: *mut LeanObject,
    mut v_inst_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_623_, v_inst_624_);
    return v___x_625_;
}
pub unsafe fn l_Lake_OrdHashSet_instEmptyCollection___boxed(
    mut v_00_u03b1_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
    mut v_inst_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_629_: *mut LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_626_, v_inst_627_, v_inst_628_);
    lean_dec_ref(v_inst_628_);
    lean_dec_ref(v_inst_627_);
    return v_res_629_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___redArg(
    mut v_size_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___closed__1_once),
        _init_l_Lake_OrdHashSet_empty___closed__1,
    );
    v___x_632_ = lean_mk_empty_array_with_capacity(v_size_630_);
    v___x_633_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_633_, 0, v___x_631_);
    lean_ctor_set(v___x_633_, 1, v___x_632_);
    return v___x_633_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___redArg___boxed(
    mut v_size_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_635_: *mut LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_634_);
    lean_dec(v_size_634_);
    return v_res_635_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty(
    mut v_00_u03b1_636_: *mut LeanObject,
    mut v_inst_637_: *mut LeanObject,
    mut v_inst_638_: *mut LeanObject,
    mut v_size_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_639_);
    return v___x_640_;
}
pub unsafe fn l_Lake_OrdHashSet_mkEmpty___boxed(
    mut v_00_u03b1_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
    mut v_size_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_645_: *mut LeanObject = core::ptr::null_mut();
    v_res_645_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_641_, v_inst_642_, v_inst_643_, v_size_644_);
    lean_dec(v_size_644_);
    lean_dec_ref(v_inst_643_);
    lean_dec_ref(v_inst_642_);
    return v_res_645_;
}
pub unsafe fn l_Lake_OrdHashSet_insert___redArg(
    mut v_inst_646_: *mut LeanObject,
    mut v_inst_647_: *mut LeanObject,
    mut v_self_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toHashSet_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_unused_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_650_ = lean_ctor_get(v_self_648_, 0);
                v_toArray_651_ = lean_ctor_get(v_self_648_, 1);
                lean_inc(v_a_649_);
                lean_inc_ref(v_inst_646_);
                lean_inc_ref(v_inst_647_);
                v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v_inst_647_,
                    v_inst_646_,
                    v_toHashSet_650_,
                    v_a_649_,
                );
                if v___x_652_ == 0 {
                    lean_inc_ref(v_toArray_651_);
                    lean_inc_ref(v_toHashSet_650_);
                    v_isSharedCheck_662_ = (!lean_is_exclusive(v_self_648_)) as u8;
                    if v_isSharedCheck_662_ == 0 {
                        v_unused_663_ = lean_ctor_get(v_self_648_, 1);
                        lean_dec(v_unused_663_);
                        v_unused_664_ = lean_ctor_get(v_self_648_, 0);
                        lean_dec(v_unused_664_);
                        v___x_654_ = v_self_648_;
                        v_isShared_655_ = v_isSharedCheck_662_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_self_648_);
                        v___x_654_ = lean_box(0);
                        v_isShared_655_ = v_isSharedCheck_662_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_649_);
                    lean_dec_ref(v_inst_647_);
                    lean_dec_ref(v_inst_646_);
                    return v_self_648_;
                }
            }
            1 => {
                v___x_656_ = lean_box(0);
                lean_inc(v_a_649_);
                v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v_inst_647_,
                    v_inst_646_,
                    v_toHashSet_650_,
                    v_a_649_,
                    v___x_656_,
                );
                v___x_658_ = lean_array_push(v_toArray_651_, v_a_649_);
                if v_isShared_655_ == 0 {
                    lean_ctor_set(v___x_654_, 1, v___x_658_);
                    lean_ctor_set(v___x_654_, 0, v___x_657_);
                    v___x_660_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_657_);
                    lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
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
    mut v_00_u03b1_665_: *mut LeanObject,
    mut v_inst_666_: *mut LeanObject,
    mut v_inst_667_: *mut LeanObject,
    mut v_self_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lake_OrdHashSet_insert___redArg(v_inst_666_, v_inst_667_, v_self_668_, v_a_669_);
    return v___x_670_;
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___redArg___lam__0(
    mut v_inst_671_: *mut LeanObject,
    mut v_inst_672_: *mut LeanObject,
    mut v_x1_673_: *mut LeanObject,
    mut v_x2_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lake_OrdHashSet_insert___redArg(v_inst_671_, v_inst_672_, v_x1_673_, v_x2_674_);
    return v___x_675_;
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___redArg(
    mut v_inst_695_: *mut LeanObject,
    mut v_inst_696_: *mut LeanObject,
    mut v_self_697_: *mut LeanObject,
    mut v_arr_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    v___x_699_ = lean_unsigned_to_nat(0);
    v___x_700_ = lean_array_get_size(v_arr_698_);
    v___x_701_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_702_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
    if v___x_702_ == 0 {
        lean_dec_ref(v_arr_698_);
        lean_dec_ref(v_inst_696_);
        lean_dec_ref(v_inst_695_);
        return v_self_697_;
    } else {
        let mut v___f_703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_704_: u8 = 0;
        v___f_703_ = lean_alloc_closure(
            l_Lake_OrdHashSet_appendArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_703_, 0, v_inst_695_);
        lean_closure_set(v___f_703_, 1, v_inst_696_);
        v___x_704_ = lean_nat_dec_le(v___x_700_, v___x_700_);
        if v___x_704_ == 0 {
            if v___x_702_ == 0 {
                lean_dec_ref(v___f_703_);
                lean_dec_ref(v_arr_698_);
                return v_self_697_;
            } else {
                let mut v___x_705_: usize = 0;
                let mut v___x_706_: usize = 0;
                let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
                v___x_705_ = 0usize;
                v___x_706_ = lean_usize_of_nat(v___x_700_);
                v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
            v___x_708_ = 0usize;
            v___x_709_ = lean_usize_of_nat(v___x_700_);
            v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_711_: *mut LeanObject,
    mut v_inst_712_: *mut LeanObject,
    mut v_inst_713_: *mut LeanObject,
    mut v_self_714_: *mut LeanObject,
    mut v_arr_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ =
        l_Lake_OrdHashSet_appendArray___redArg(v_inst_712_, v_inst_713_, v_self_714_, v_arr_715_);
    return v___x_716_;
}
pub unsafe fn l_Lake_OrdHashSet_instHAppendArray___redArg(
    mut v_inst_717_: *mut LeanObject,
    mut v_inst_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = lean_alloc_closure(
        l_Lake_OrdHashSet_appendArray as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_719_, 0, lean_box(0));
    lean_closure_set(v___x_719_, 1, v_inst_717_);
    lean_closure_set(v___x_719_, 2, v_inst_718_);
    return v___x_719_;
}
pub unsafe fn l_Lake_OrdHashSet_instHAppendArray(
    mut v_00_u03b1_720_: *mut LeanObject,
    mut v_inst_721_: *mut LeanObject,
    mut v_inst_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    v___x_723_ = lean_alloc_closure(
        l_Lake_OrdHashSet_appendArray as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_723_, 0, lean_box(0));
    lean_closure_set(v___x_723_, 1, v_inst_721_);
    lean_closure_set(v___x_723_, 2, v_inst_722_);
    return v___x_723_;
}
pub unsafe fn l_Lake_OrdHashSet_append___redArg(
    mut v_inst_724_: *mut LeanObject,
    mut v_inst_725_: *mut LeanObject,
    mut v_self_726_: *mut LeanObject,
    mut v_other_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_728_ = lean_ctor_get(v_other_727_, 1);
    lean_inc_ref(v_toArray_728_);
    lean_dec_ref(v_other_727_);
    v___x_729_ = l_Lake_OrdHashSet_appendArray___redArg(
        v_inst_724_,
        v_inst_725_,
        v_self_726_,
        v_toArray_728_,
    );
    return v___x_729_;
}
pub unsafe fn l_Lake_OrdHashSet_append(
    mut v_00_u03b1_730_: *mut LeanObject,
    mut v_inst_731_: *mut LeanObject,
    mut v_inst_732_: *mut LeanObject,
    mut v_self_733_: *mut LeanObject,
    mut v_other_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ =
        l_Lake_OrdHashSet_append___redArg(v_inst_731_, v_inst_732_, v_self_733_, v_other_734_);
    return v___x_735_;
}
pub unsafe fn l_Lake_OrdHashSet_instAppend___redArg(
    mut v_inst_736_: *mut LeanObject,
    mut v_inst_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = lean_alloc_closure(l_Lake_OrdHashSet_append as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_738_, 0, lean_box(0));
    lean_closure_set(v___x_738_, 1, v_inst_736_);
    lean_closure_set(v___x_738_, 2, v_inst_737_);
    return v___x_738_;
}
pub unsafe fn l_Lake_OrdHashSet_instAppend(
    mut v_00_u03b1_739_: *mut LeanObject,
    mut v_inst_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = lean_alloc_closure(l_Lake_OrdHashSet_append as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_742_, 0, lean_box(0));
    lean_closure_set(v___x_742_, 1, v_inst_740_);
    lean_closure_set(v___x_742_, 2, v_inst_741_);
    return v___x_742_;
}
pub unsafe fn l_Lake_OrdHashSet_ofArray___redArg(
    mut v_inst_743_: *mut LeanObject,
    mut v_inst_744_: *mut LeanObject,
    mut v_arr_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = lean_array_get_size(v_arr_745_);
    v___x_747_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_746_);
    v___x_748_ =
        l_Lake_OrdHashSet_appendArray___redArg(v_inst_743_, v_inst_744_, v___x_747_, v_arr_745_);
    return v___x_748_;
}
pub unsafe fn l_Lake_OrdHashSet_ofArray(
    mut v_00_u03b1_749_: *mut LeanObject,
    mut v_inst_750_: *mut LeanObject,
    mut v_inst_751_: *mut LeanObject,
    mut v_arr_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_750_, v_inst_751_, v_arr_752_);
    return v___x_753_;
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg___lam__0(
    mut v_f_754_: *mut LeanObject,
    mut v___x_755_: u8,
    mut v_v_756_: *mut LeanObject,
) -> u8 {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    v___x_757_ = lean_apply_1(v_f_754_, v_v_756_);
    v___x_758_ = (lean_unbox(v___x_757_) as u8);
    if v___x_758_ == 0 {
        return v___x_755_;
    } else {
        let mut v___x_759_: u8 = 0;
        v___x_759_ = 0;
        return v___x_759_;
    }
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg___lam__0___boxed(
    mut v_f_760_: *mut LeanObject,
    mut v___x_761_: *mut LeanObject,
    mut v_v_762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_83__boxed_763_: u8 = 0;
    let mut v_res_764_: u8 = 0;
    let mut v_r_765_: *mut LeanObject = core::ptr::null_mut();
    v___x_83__boxed_763_ = (lean_unbox(v___x_761_) as u8);
    v_res_764_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_760_, v___x_83__boxed_763_, v_v_762_);
    v_r_765_ = lean_box((v_res_764_) as usize);
    return v_r_765_;
}
pub unsafe fn l_Lake_OrdHashSet_all___redArg(
    mut v_f_766_: *mut LeanObject,
    mut v_self_767_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    v_toArray_768_ = lean_ctor_get(v_self_767_, 1);
    lean_inc_ref(v_toArray_768_);
    lean_dec_ref(v_self_767_);
    v___x_769_ = lean_unsigned_to_nat(0);
    v___x_770_ = lean_array_get_size(v_toArray_768_);
    v___x_771_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_772_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
    if v___x_772_ == 0 {
        let mut v___x_773_: u8 = 0;
        lean_dec_ref(v_toArray_768_);
        lean_dec_ref(v_f_766_);
        v___x_773_ = 1;
        return v___x_773_;
    } else {
        if v___x_772_ == 0 {
            lean_dec_ref(v_toArray_768_);
            lean_dec_ref(v_f_766_);
            return v___x_772_;
        } else {
            let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_775_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_776_: usize = 0;
            let mut v___x_777_: usize = 0;
            let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_779_: u8 = 0;
            v___x_774_ = lean_box((v___x_772_) as usize);
            v___f_775_ = lean_alloc_closure(
                l_Lake_OrdHashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_775_, 0, v_f_766_);
            lean_closure_set(v___f_775_, 1, v___x_774_);
            v___x_776_ = 0usize;
            v___x_777_ = lean_usize_of_nat(v___x_770_);
            v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_771_,
                v___f_775_,
                v_toArray_768_,
                v___x_776_,
                v___x_777_,
            );
            v___x_779_ = (lean_unbox(v___x_778_) as u8);
            lean_dec(v___x_778_);
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
    mut v_f_781_: *mut LeanObject,
    mut v_self_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: u8 = 0;
    let mut v_r_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lake_OrdHashSet_all___redArg(v_f_781_, v_self_782_);
    v_r_784_ = lean_box((v_res_783_) as usize);
    return v_r_784_;
}
pub unsafe fn l_Lake_OrdHashSet_all(
    mut v_00_u03b1_785_: *mut LeanObject,
    mut v_inst_786_: *mut LeanObject,
    mut v_inst_787_: *mut LeanObject,
    mut v_f_788_: *mut LeanObject,
    mut v_self_789_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    v_toArray_790_ = lean_ctor_get(v_self_789_, 1);
    lean_inc_ref(v_toArray_790_);
    lean_dec_ref(v_self_789_);
    v___x_791_ = lean_unsigned_to_nat(0);
    v___x_792_ = lean_array_get_size(v_toArray_790_);
    v___x_793_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_794_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
    if v___x_794_ == 0 {
        let mut v___x_795_: u8 = 0;
        lean_dec_ref(v_toArray_790_);
        lean_dec_ref(v_f_788_);
        v___x_795_ = 1;
        return v___x_795_;
    } else {
        if v___x_794_ == 0 {
            lean_dec_ref(v_toArray_790_);
            lean_dec_ref(v_f_788_);
            return v___x_794_;
        } else {
            let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_797_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_798_: usize = 0;
            let mut v___x_799_: usize = 0;
            let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            v___x_796_ = lean_box((v___x_794_) as usize);
            v___f_797_ = lean_alloc_closure(
                l_Lake_OrdHashSet_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_797_, 0, v_f_788_);
            lean_closure_set(v___f_797_, 1, v___x_796_);
            v___x_798_ = 0usize;
            v___x_799_ = lean_usize_of_nat(v___x_792_);
            v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_793_,
                v___f_797_,
                v_toArray_790_,
                v___x_798_,
                v___x_799_,
            );
            v___x_801_ = (lean_unbox(v___x_800_) as u8);
            lean_dec(v___x_800_);
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
    mut v_00_u03b1_803_: *mut LeanObject,
    mut v_inst_804_: *mut LeanObject,
    mut v_inst_805_: *mut LeanObject,
    mut v_f_806_: *mut LeanObject,
    mut v_self_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: u8 = 0;
    let mut v_r_809_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lake_OrdHashSet_all(
        v_00_u03b1_803_,
        v_inst_804_,
        v_inst_805_,
        v_f_806_,
        v_self_807_,
    );
    lean_dec_ref(v_inst_805_);
    lean_dec_ref(v_inst_804_);
    v_r_809_ = lean_box((v_res_808_) as usize);
    return v_r_809_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___lam__0(
    mut v_f_810_: *mut LeanObject,
    mut v_x_811_: *mut LeanObject,
) -> u8 {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    v___x_812_ = lean_apply_1(v_f_810_, v_x_811_);
    v___x_813_ = (lean_unbox(v___x_812_) as u8);
    return v___x_813_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___lam__0___boxed(
    mut v_f_814_: *mut LeanObject,
    mut v_x_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_816_: u8 = 0;
    let mut v_r_817_: *mut LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_814_, v_x_815_);
    v_r_817_ = lean_box((v_res_816_) as usize);
    return v_r_817_;
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg(
    mut v_f_818_: *mut LeanObject,
    mut v_self_819_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: u8 = 0;
    v_toArray_820_ = lean_ctor_get(v_self_819_, 1);
    lean_inc_ref(v_toArray_820_);
    lean_dec_ref(v_self_819_);
    v___x_821_ = lean_unsigned_to_nat(0);
    v___x_822_ = lean_array_get_size(v_toArray_820_);
    v___x_823_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_824_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
    if v___x_824_ == 0 {
        lean_dec_ref(v_toArray_820_);
        lean_dec_ref(v_f_818_);
        return v___x_824_;
    } else {
        if v___x_824_ == 0 {
            lean_dec_ref(v_toArray_820_);
            lean_dec_ref(v_f_818_);
            return v___x_824_;
        } else {
            let mut v___f_825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_826_: usize = 0;
            let mut v___x_827_: usize = 0;
            let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_829_: u8 = 0;
            v___f_825_ = lean_alloc_closure(
                l_Lake_OrdHashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_825_, 0, v_f_818_);
            v___x_826_ = 0usize;
            v___x_827_ = lean_usize_of_nat(v___x_822_);
            v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_823_,
                v___f_825_,
                v_toArray_820_,
                v___x_826_,
                v___x_827_,
            );
            v___x_829_ = (lean_unbox(v___x_828_) as u8);
            lean_dec(v___x_828_);
            return v___x_829_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_any___redArg___boxed(
    mut v_f_830_: *mut LeanObject,
    mut v_self_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_832_: u8 = 0;
    let mut v_r_833_: *mut LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lake_OrdHashSet_any___redArg(v_f_830_, v_self_831_);
    v_r_833_ = lean_box((v_res_832_) as usize);
    return v_r_833_;
}
pub unsafe fn l_Lake_OrdHashSet_any(
    mut v_00_u03b1_834_: *mut LeanObject,
    mut v_inst_835_: *mut LeanObject,
    mut v_inst_836_: *mut LeanObject,
    mut v_f_837_: *mut LeanObject,
    mut v_self_838_: *mut LeanObject,
) -> u8 {
    let mut v_toArray_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    v_toArray_839_ = lean_ctor_get(v_self_838_, 1);
    lean_inc_ref(v_toArray_839_);
    lean_dec_ref(v_self_838_);
    v___x_840_ = lean_unsigned_to_nat(0);
    v___x_841_ = lean_array_get_size(v_toArray_839_);
    v___x_842_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_843_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
    if v___x_843_ == 0 {
        lean_dec_ref(v_toArray_839_);
        lean_dec_ref(v_f_837_);
        return v___x_843_;
    } else {
        if v___x_843_ == 0 {
            lean_dec_ref(v_toArray_839_);
            lean_dec_ref(v_f_837_);
            return v___x_843_;
        } else {
            let mut v___f_844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_845_: usize = 0;
            let mut v___x_846_: usize = 0;
            let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_848_: u8 = 0;
            v___f_844_ = lean_alloc_closure(
                l_Lake_OrdHashSet_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_844_, 0, v_f_837_);
            v___x_845_ = 0usize;
            v___x_846_ = lean_usize_of_nat(v___x_841_);
            v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_842_,
                v___f_844_,
                v_toArray_839_,
                v___x_845_,
                v___x_846_,
            );
            v___x_848_ = (lean_unbox(v___x_847_) as u8);
            lean_dec(v___x_847_);
            return v___x_848_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_any___boxed(
    mut v_00_u03b1_849_: *mut LeanObject,
    mut v_inst_850_: *mut LeanObject,
    mut v_inst_851_: *mut LeanObject,
    mut v_f_852_: *mut LeanObject,
    mut v_self_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_854_: u8 = 0;
    let mut v_r_855_: *mut LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lake_OrdHashSet_any(
        v_00_u03b1_849_,
        v_inst_850_,
        v_inst_851_,
        v_f_852_,
        v_self_853_,
    );
    lean_dec_ref(v_inst_851_);
    lean_dec_ref(v_inst_850_);
    v_r_855_ = lean_box((v_res_854_) as usize);
    return v_r_855_;
}
pub unsafe fn l_Lake_OrdHashSet_foldl___redArg___lam__0(
    mut v_f_856_: *mut LeanObject,
    mut v_x1_857_: *mut LeanObject,
    mut v_x2_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = lean_apply_2(v_f_856_, v_x1_857_, v_x2_858_);
    return v___x_859_;
}
pub unsafe fn l_Lake_OrdHashSet_foldl___redArg(
    mut v_f_860_: *mut LeanObject,
    mut v_init_861_: *mut LeanObject,
    mut v_self_862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    v_toArray_863_ = lean_ctor_get(v_self_862_, 1);
    lean_inc_ref(v_toArray_863_);
    lean_dec_ref(v_self_862_);
    v___x_864_ = lean_unsigned_to_nat(0);
    v___x_865_ = lean_array_get_size(v_toArray_863_);
    v___x_866_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_867_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
    if v___x_867_ == 0 {
        lean_dec_ref(v_toArray_863_);
        lean_dec(v_f_860_);
        return v_init_861_;
    } else {
        let mut v___f_868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_869_: u8 = 0;
        v___f_868_ = lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_868_, 0, v_f_860_);
        v___x_869_ = lean_nat_dec_le(v___x_865_, v___x_865_);
        if v___x_869_ == 0 {
            if v___x_867_ == 0 {
                lean_dec_ref(v___f_868_);
                lean_dec_ref(v_toArray_863_);
                return v_init_861_;
            } else {
                let mut v___x_870_: usize = 0;
                let mut v___x_871_: usize = 0;
                let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
                v___x_870_ = 0usize;
                v___x_871_ = lean_usize_of_nat(v___x_865_);
                v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
            v___x_873_ = 0usize;
            v___x_874_ = lean_usize_of_nat(v___x_865_);
            v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_876_: *mut LeanObject,
    mut v_inst_877_: *mut LeanObject,
    mut v_inst_878_: *mut LeanObject,
    mut v_00_u03b2_879_: *mut LeanObject,
    mut v_f_880_: *mut LeanObject,
    mut v_init_881_: *mut LeanObject,
    mut v_self_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    v_toArray_883_ = lean_ctor_get(v_self_882_, 1);
    lean_inc_ref(v_toArray_883_);
    lean_dec_ref(v_self_882_);
    v___x_884_ = lean_unsigned_to_nat(0);
    v___x_885_ = lean_array_get_size(v_toArray_883_);
    v___x_886_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_887_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
    if v___x_887_ == 0 {
        lean_dec_ref(v_toArray_883_);
        lean_dec(v_f_880_);
        return v_init_881_;
    } else {
        let mut v___f_888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_889_: u8 = 0;
        v___f_888_ = lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_888_, 0, v_f_880_);
        v___x_889_ = lean_nat_dec_le(v___x_885_, v___x_885_);
        if v___x_889_ == 0 {
            if v___x_887_ == 0 {
                lean_dec_ref(v___f_888_);
                lean_dec_ref(v_toArray_883_);
                return v_init_881_;
            } else {
                let mut v___x_890_: usize = 0;
                let mut v___x_891_: usize = 0;
                let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
                v___x_890_ = 0usize;
                v___x_891_ = lean_usize_of_nat(v___x_885_);
                v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
            v___x_893_ = 0usize;
            v___x_894_ = lean_usize_of_nat(v___x_885_);
            v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_896_: *mut LeanObject,
    mut v_inst_897_: *mut LeanObject,
    mut v_inst_898_: *mut LeanObject,
    mut v_00_u03b2_899_: *mut LeanObject,
    mut v_f_900_: *mut LeanObject,
    mut v_init_901_: *mut LeanObject,
    mut v_self_902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_903_: *mut LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Lake_OrdHashSet_foldl(
        v_00_u03b1_896_,
        v_inst_897_,
        v_inst_898_,
        v_00_u03b2_899_,
        v_f_900_,
        v_init_901_,
        v_self_902_,
    );
    lean_dec_ref(v_inst_898_);
    lean_dec_ref(v_inst_897_);
    return v_res_903_;
}
pub unsafe fn l_Lake_OrdHashSet_foldlM___redArg(
    mut v_inst_904_: *mut LeanObject,
    mut v_f_905_: *mut LeanObject,
    mut v_init_906_: *mut LeanObject,
    mut v_self_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: u8 = 0;
    v_toArray_908_ = lean_ctor_get(v_self_907_, 1);
    lean_inc_ref(v_toArray_908_);
    lean_dec_ref(v_self_907_);
    v___x_909_ = lean_unsigned_to_nat(0);
    v___x_910_ = lean_array_get_size(v_toArray_908_);
    v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
    if v___x_911_ == 0 {
        let mut v_toApplicative_912_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_908_);
        lean_dec(v_f_905_);
        v_toApplicative_912_ = lean_ctor_get(v_inst_904_, 0);
        lean_inc_ref(v_toApplicative_912_);
        lean_dec_ref(v_inst_904_);
        v_toPure_913_ = lean_ctor_get(v_toApplicative_912_, 1);
        lean_inc(v_toPure_913_);
        lean_dec_ref(v_toApplicative_912_);
        v___x_914_ = lean_apply_2(v_toPure_913_, lean_box(0), v_init_906_);
        return v___x_914_;
    } else {
        let mut v___x_915_: u8 = 0;
        v___x_915_ = lean_nat_dec_le(v___x_910_, v___x_910_);
        if v___x_915_ == 0 {
            if v___x_911_ == 0 {
                let mut v_toApplicative_916_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_917_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toArray_908_);
                lean_dec(v_f_905_);
                v_toApplicative_916_ = lean_ctor_get(v_inst_904_, 0);
                lean_inc_ref(v_toApplicative_916_);
                lean_dec_ref(v_inst_904_);
                v_toPure_917_ = lean_ctor_get(v_toApplicative_916_, 1);
                lean_inc(v_toPure_917_);
                lean_dec_ref(v_toApplicative_916_);
                v___x_918_ = lean_apply_2(v_toPure_917_, lean_box(0), v_init_906_);
                return v___x_918_;
            } else {
                let mut v___x_919_: usize = 0;
                let mut v___x_920_: usize = 0;
                let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
                v___x_919_ = 0usize;
                v___x_920_ = lean_usize_of_nat(v___x_910_);
                v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
            v___x_922_ = 0usize;
            v___x_923_ = lean_usize_of_nat(v___x_910_);
            v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_925_: *mut LeanObject,
    mut v_inst_926_: *mut LeanObject,
    mut v_inst_927_: *mut LeanObject,
    mut v_m_928_: *mut LeanObject,
    mut v_00_u03b2_929_: *mut LeanObject,
    mut v_inst_930_: *mut LeanObject,
    mut v_f_931_: *mut LeanObject,
    mut v_init_932_: *mut LeanObject,
    mut v_self_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: u8 = 0;
    v_toArray_934_ = lean_ctor_get(v_self_933_, 1);
    lean_inc_ref(v_toArray_934_);
    lean_dec_ref(v_self_933_);
    v___x_935_ = lean_unsigned_to_nat(0);
    v___x_936_ = lean_array_get_size(v_toArray_934_);
    v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
    if v___x_937_ == 0 {
        let mut v_toApplicative_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_934_);
        lean_dec(v_f_931_);
        v_toApplicative_938_ = lean_ctor_get(v_inst_930_, 0);
        lean_inc_ref(v_toApplicative_938_);
        lean_dec_ref(v_inst_930_);
        v_toPure_939_ = lean_ctor_get(v_toApplicative_938_, 1);
        lean_inc(v_toPure_939_);
        lean_dec_ref(v_toApplicative_938_);
        v___x_940_ = lean_apply_2(v_toPure_939_, lean_box(0), v_init_932_);
        return v___x_940_;
    } else {
        let mut v___x_941_: u8 = 0;
        v___x_941_ = lean_nat_dec_le(v___x_936_, v___x_936_);
        if v___x_941_ == 0 {
            if v___x_937_ == 0 {
                let mut v_toApplicative_942_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_943_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toArray_934_);
                lean_dec(v_f_931_);
                v_toApplicative_942_ = lean_ctor_get(v_inst_930_, 0);
                lean_inc_ref(v_toApplicative_942_);
                lean_dec_ref(v_inst_930_);
                v_toPure_943_ = lean_ctor_get(v_toApplicative_942_, 1);
                lean_inc(v_toPure_943_);
                lean_dec_ref(v_toApplicative_942_);
                v___x_944_ = lean_apply_2(v_toPure_943_, lean_box(0), v_init_932_);
                return v___x_944_;
            } else {
                let mut v___x_945_: usize = 0;
                let mut v___x_946_: usize = 0;
                let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
                v___x_945_ = 0usize;
                v___x_946_ = lean_usize_of_nat(v___x_936_);
                v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
            v___x_948_ = 0usize;
            v___x_949_ = lean_usize_of_nat(v___x_936_);
            v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_951_: *mut LeanObject,
    mut v_inst_952_: *mut LeanObject,
    mut v_inst_953_: *mut LeanObject,
    mut v_m_954_: *mut LeanObject,
    mut v_00_u03b2_955_: *mut LeanObject,
    mut v_inst_956_: *mut LeanObject,
    mut v_f_957_: *mut LeanObject,
    mut v_init_958_: *mut LeanObject,
    mut v_self_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_960_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_953_);
    lean_dec_ref(v_inst_952_);
    return v_res_960_;
}
pub unsafe fn l_Lake_OrdHashSet_foldr___redArg(
    mut v_f_961_: *mut LeanObject,
    mut v_init_962_: *mut LeanObject,
    mut v_self_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    v_toArray_964_ = lean_ctor_get(v_self_963_, 1);
    lean_inc_ref(v_toArray_964_);
    lean_dec_ref(v_self_963_);
    v___x_965_ = lean_array_get_size(v_toArray_964_);
    v___x_966_ = lean_unsigned_to_nat(0);
    v___x_967_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_965_);
    if v___x_968_ == 0 {
        lean_dec_ref(v_toArray_964_);
        lean_dec(v_f_961_);
        return v_init_962_;
    } else {
        let mut v___f_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: usize = 0;
        let mut v___x_971_: usize = 0;
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        v___f_969_ = lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_969_, 0, v_f_961_);
        v___x_970_ = lean_usize_of_nat(v___x_965_);
        v___x_971_ = 0usize;
        v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_973_: *mut LeanObject,
    mut v_inst_974_: *mut LeanObject,
    mut v_inst_975_: *mut LeanObject,
    mut v_00_u03b2_976_: *mut LeanObject,
    mut v_f_977_: *mut LeanObject,
    mut v_init_978_: *mut LeanObject,
    mut v_self_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    v_toArray_980_ = lean_ctor_get(v_self_979_, 1);
    lean_inc_ref(v_toArray_980_);
    lean_dec_ref(v_self_979_);
    v___x_981_ = lean_array_get_size(v_toArray_980_);
    v___x_982_ = lean_unsigned_to_nat(0);
    v___x_983_ = l_Lake_OrdHashSet_appendArray___redArg___closed__9;
    v___x_984_ = lean_nat_dec_lt(v___x_982_, v___x_981_);
    if v___x_984_ == 0 {
        lean_dec_ref(v_toArray_980_);
        lean_dec(v_f_977_);
        return v_init_978_;
    } else {
        let mut v___f_985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_986_: usize = 0;
        let mut v___x_987_: usize = 0;
        let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
        v___f_985_ = lean_alloc_closure(
            l_Lake_OrdHashSet_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_985_, 0, v_f_977_);
        v___x_986_ = lean_usize_of_nat(v___x_981_);
        v___x_987_ = 0usize;
        v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_989_: *mut LeanObject,
    mut v_inst_990_: *mut LeanObject,
    mut v_inst_991_: *mut LeanObject,
    mut v_00_u03b2_992_: *mut LeanObject,
    mut v_f_993_: *mut LeanObject,
    mut v_init_994_: *mut LeanObject,
    mut v_self_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_996_: *mut LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Lake_OrdHashSet_foldr(
        v_00_u03b1_989_,
        v_inst_990_,
        v_inst_991_,
        v_00_u03b2_992_,
        v_f_993_,
        v_init_994_,
        v_self_995_,
    );
    lean_dec_ref(v_inst_991_);
    lean_dec_ref(v_inst_990_);
    return v_res_996_;
}
pub unsafe fn l_Lake_OrdHashSet_foldrM___redArg(
    mut v_inst_997_: *mut LeanObject,
    mut v_f_998_: *mut LeanObject,
    mut v_init_999_: *mut LeanObject,
    mut v_self_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    v_toArray_1001_ = lean_ctor_get(v_self_1000_, 1);
    lean_inc_ref(v_toArray_1001_);
    lean_dec_ref(v_self_1000_);
    v___x_1002_ = lean_array_get_size(v_toArray_1001_);
    v___x_1003_ = lean_unsigned_to_nat(0);
    v___x_1004_ = lean_nat_dec_lt(v___x_1003_, v___x_1002_);
    if v___x_1004_ == 0 {
        let mut v_toApplicative_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1001_);
        lean_dec(v_f_998_);
        v_toApplicative_1005_ = lean_ctor_get(v_inst_997_, 0);
        lean_inc_ref(v_toApplicative_1005_);
        lean_dec_ref(v_inst_997_);
        v_toPure_1006_ = lean_ctor_get(v_toApplicative_1005_, 1);
        lean_inc(v_toPure_1006_);
        lean_dec_ref(v_toApplicative_1005_);
        v___x_1007_ = lean_apply_2(v_toPure_1006_, lean_box(0), v_init_999_);
        return v___x_1007_;
    } else {
        let mut v___x_1008_: usize = 0;
        let mut v___x_1009_: usize = 0;
        let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
        v___x_1008_ = lean_usize_of_nat(v___x_1002_);
        v___x_1009_ = 0usize;
        v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_1011_: *mut LeanObject,
    mut v_inst_1012_: *mut LeanObject,
    mut v_inst_1013_: *mut LeanObject,
    mut v_m_1014_: *mut LeanObject,
    mut v_00_u03b2_1015_: *mut LeanObject,
    mut v_inst_1016_: *mut LeanObject,
    mut v_f_1017_: *mut LeanObject,
    mut v_init_1018_: *mut LeanObject,
    mut v_self_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    v_toArray_1020_ = lean_ctor_get(v_self_1019_, 1);
    lean_inc_ref(v_toArray_1020_);
    lean_dec_ref(v_self_1019_);
    v___x_1021_ = lean_array_get_size(v_toArray_1020_);
    v___x_1022_ = lean_unsigned_to_nat(0);
    v___x_1023_ = lean_nat_dec_lt(v___x_1022_, v___x_1021_);
    if v___x_1023_ == 0 {
        let mut v_toApplicative_1024_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1020_);
        lean_dec(v_f_1017_);
        v_toApplicative_1024_ = lean_ctor_get(v_inst_1016_, 0);
        lean_inc_ref(v_toApplicative_1024_);
        lean_dec_ref(v_inst_1016_);
        v_toPure_1025_ = lean_ctor_get(v_toApplicative_1024_, 1);
        lean_inc(v_toPure_1025_);
        lean_dec_ref(v_toApplicative_1024_);
        v___x_1026_ = lean_apply_2(v_toPure_1025_, lean_box(0), v_init_1018_);
        return v___x_1026_;
    } else {
        let mut v___x_1027_: usize = 0;
        let mut v___x_1028_: usize = 0;
        let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
        v___x_1027_ = lean_usize_of_nat(v___x_1021_);
        v___x_1028_ = 0usize;
        v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_1030_: *mut LeanObject,
    mut v_inst_1031_: *mut LeanObject,
    mut v_inst_1032_: *mut LeanObject,
    mut v_m_1033_: *mut LeanObject,
    mut v_00_u03b2_1034_: *mut LeanObject,
    mut v_inst_1035_: *mut LeanObject,
    mut v_f_1036_: *mut LeanObject,
    mut v_init_1037_: *mut LeanObject,
    mut v_self_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1039_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_1032_);
    lean_dec_ref(v_inst_1031_);
    return v_res_1039_;
}
pub unsafe fn l_Lake_OrdHashSet_forM___redArg___lam__0(
    mut v_f_1040_: *mut LeanObject,
    mut v_x_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = lean_apply_1(v_f_1040_, v___y_1042_);
    return v___x_1043_;
}
pub unsafe fn l_Lake_OrdHashSet_forM___redArg(
    mut v_inst_1044_: *mut LeanObject,
    mut v_f_1045_: *mut LeanObject,
    mut v_self_1046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    v_toArray_1047_ = lean_ctor_get(v_self_1046_, 1);
    lean_inc_ref(v_toArray_1047_);
    lean_dec_ref(v_self_1046_);
    v___x_1048_ = lean_unsigned_to_nat(0);
    v___x_1049_ = lean_array_get_size(v_toArray_1047_);
    v___x_1050_ = lean_box(0);
    v___x_1051_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
    if v___x_1051_ == 0 {
        let mut v_toApplicative_1052_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1047_);
        lean_dec(v_f_1045_);
        v_toApplicative_1052_ = lean_ctor_get(v_inst_1044_, 0);
        lean_inc_ref(v_toApplicative_1052_);
        lean_dec_ref(v_inst_1044_);
        v_toPure_1053_ = lean_ctor_get(v_toApplicative_1052_, 1);
        lean_inc(v_toPure_1053_);
        lean_dec_ref(v_toApplicative_1052_);
        v___x_1054_ = lean_apply_2(v_toPure_1053_, lean_box(0), v___x_1050_);
        return v___x_1054_;
    } else {
        let mut v___f_1055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: u8 = 0;
        v___f_1055_ = lean_alloc_closure(
            l_Lake_OrdHashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1055_, 0, v_f_1045_);
        v___x_1056_ = lean_nat_dec_le(v___x_1049_, v___x_1049_);
        if v___x_1056_ == 0 {
            if v___x_1051_ == 0 {
                let mut v_toApplicative_1057_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1058_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_1055_);
                lean_dec_ref(v_toArray_1047_);
                v_toApplicative_1057_ = lean_ctor_get(v_inst_1044_, 0);
                lean_inc_ref(v_toApplicative_1057_);
                lean_dec_ref(v_inst_1044_);
                v_toPure_1058_ = lean_ctor_get(v_toApplicative_1057_, 1);
                lean_inc(v_toPure_1058_);
                lean_dec_ref(v_toApplicative_1057_);
                v___x_1059_ = lean_apply_2(v_toPure_1058_, lean_box(0), v___x_1050_);
                return v___x_1059_;
            } else {
                let mut v___x_1060_: usize = 0;
                let mut v___x_1061_: usize = 0;
                let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
                v___x_1060_ = 0usize;
                v___x_1061_ = lean_usize_of_nat(v___x_1049_);
                v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
            v___x_1063_ = 0usize;
            v___x_1064_ = lean_usize_of_nat(v___x_1049_);
            v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_1066_: *mut LeanObject,
    mut v_inst_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_m_1069_: *mut LeanObject,
    mut v_inst_1070_: *mut LeanObject,
    mut v_f_1071_: *mut LeanObject,
    mut v_self_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    v_toArray_1073_ = lean_ctor_get(v_self_1072_, 1);
    lean_inc_ref(v_toArray_1073_);
    lean_dec_ref(v_self_1072_);
    v___x_1074_ = lean_unsigned_to_nat(0);
    v___x_1075_ = lean_array_get_size(v_toArray_1073_);
    v___x_1076_ = lean_box(0);
    v___x_1077_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
    if v___x_1077_ == 0 {
        let mut v_toApplicative_1078_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toArray_1073_);
        lean_dec(v_f_1071_);
        v_toApplicative_1078_ = lean_ctor_get(v_inst_1070_, 0);
        lean_inc_ref(v_toApplicative_1078_);
        lean_dec_ref(v_inst_1070_);
        v_toPure_1079_ = lean_ctor_get(v_toApplicative_1078_, 1);
        lean_inc(v_toPure_1079_);
        lean_dec_ref(v_toApplicative_1078_);
        v___x_1080_ = lean_apply_2(v_toPure_1079_, lean_box(0), v___x_1076_);
        return v___x_1080_;
    } else {
        let mut v___f_1081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: u8 = 0;
        v___f_1081_ = lean_alloc_closure(
            l_Lake_OrdHashSet_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1081_, 0, v_f_1071_);
        v___x_1082_ = lean_nat_dec_le(v___x_1075_, v___x_1075_);
        if v___x_1082_ == 0 {
            if v___x_1077_ == 0 {
                let mut v_toApplicative_1083_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_1084_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_1081_);
                lean_dec_ref(v_toArray_1073_);
                v_toApplicative_1083_ = lean_ctor_get(v_inst_1070_, 0);
                lean_inc_ref(v_toApplicative_1083_);
                lean_dec_ref(v_inst_1070_);
                v_toPure_1084_ = lean_ctor_get(v_toApplicative_1083_, 1);
                lean_inc(v_toPure_1084_);
                lean_dec_ref(v_toApplicative_1083_);
                v___x_1085_ = lean_apply_2(v_toPure_1084_, lean_box(0), v___x_1076_);
                return v___x_1085_;
            } else {
                let mut v___x_1086_: usize = 0;
                let mut v___x_1087_: usize = 0;
                let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
                v___x_1086_ = 0usize;
                v___x_1087_ = lean_usize_of_nat(v___x_1075_);
                v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
            v___x_1089_ = 0usize;
            v___x_1090_ = lean_usize_of_nat(v___x_1075_);
            v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_1092_: *mut LeanObject,
    mut v_inst_1093_: *mut LeanObject,
    mut v_inst_1094_: *mut LeanObject,
    mut v_m_1095_: *mut LeanObject,
    mut v_inst_1096_: *mut LeanObject,
    mut v_f_1097_: *mut LeanObject,
    mut v_self_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lake_OrdHashSet_forM(
        v_00_u03b1_1092_,
        v_inst_1093_,
        v_inst_1094_,
        v_m_1095_,
        v_inst_1096_,
        v_f_1097_,
        v_self_1098_,
    );
    lean_dec_ref(v_inst_1094_);
    lean_dec_ref(v_inst_1093_);
    return v_res_1099_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn___redArg___lam__0(
    mut v_f_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
    mut v_x_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = lean_apply_2(v_f_1100_, v_a_1101_, v___y_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Lake_OrdHashSet_forIn___redArg(
    mut v_inst_1105_: *mut LeanObject,
    mut v_self_1106_: *mut LeanObject,
    mut v_init_1107_: *mut LeanObject,
    mut v_f_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1111_: usize = 0;
    let mut v___x_1112_: usize = 0;
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1109_ = lean_ctor_get(v_self_1106_, 1);
    lean_inc_ref(v_toArray_1109_);
    lean_dec_ref(v_self_1106_);
    v___f_1110_ = lean_alloc_closure(
        l_Lake_OrdHashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1110_, 0, v_f_1108_);
    v_sz_1111_ = lean_array_size(v_toArray_1109_);
    v___x_1112_ = 0usize;
    v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_00_u03b1_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_inst_1116_: *mut LeanObject,
    mut v_m_1117_: *mut LeanObject,
    mut v_00_u03b2_1118_: *mut LeanObject,
    mut v_inst_1119_: *mut LeanObject,
    mut v_self_1120_: *mut LeanObject,
    mut v_init_1121_: *mut LeanObject,
    mut v_f_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1123_ = lean_ctor_get(v_self_1120_, 1);
    lean_inc_ref(v_toArray_1123_);
    lean_dec_ref(v_self_1120_);
    v___f_1124_ = lean_alloc_closure(
        l_Lake_OrdHashSet_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1124_, 0, v_f_1122_);
    v_sz_1125_ = lean_array_size(v_toArray_1123_);
    v___x_1126_ = 0usize;
    v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_00_u03b1_1128_: *mut LeanObject,
    mut v_inst_1129_: *mut LeanObject,
    mut v_inst_1130_: *mut LeanObject,
    mut v_m_1131_: *mut LeanObject,
    mut v_00_u03b2_1132_: *mut LeanObject,
    mut v_inst_1133_: *mut LeanObject,
    mut v_self_1134_: *mut LeanObject,
    mut v_init_1135_: *mut LeanObject,
    mut v_f_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_1130_);
    lean_dec_ref(v_inst_1129_);
    return v_res_1137_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(
    mut v___y_1138_: *mut LeanObject,
    mut v_a_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ = lean_apply_2(v___y_1138_, v_a_1139_, v___y_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(
    mut v_inst_1143_: *mut LeanObject,
    mut v_00_u03b2_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toArray_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1150_: usize = 0;
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    v_toArray_1148_ = lean_ctor_get(v___y_1145_, 1);
    lean_inc_ref(v_toArray_1148_);
    lean_dec_ref(v___y_1145_);
    v___f_1149_ = lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1149_, 0, v___y_1147_);
    v_sz_1150_ = lean_array_size(v_toArray_1148_);
    v___x_1151_ = 0usize;
    v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
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
    mut v_inst_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1154_: *mut LeanObject = core::ptr::null_mut();
    v___f_1154_ = lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1154_, 0, v_inst_1153_);
    return v___f_1154_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad(
    mut v_00_u03b1_1155_: *mut LeanObject,
    mut v_inst_1156_: *mut LeanObject,
    mut v_inst_1157_: *mut LeanObject,
    mut v_m_1158_: *mut LeanObject,
    mut v_inst_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1160_: *mut LeanObject = core::ptr::null_mut();
    v___f_1160_ = lean_alloc_closure(
        l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1160_, 0, v_inst_1159_);
    return v___f_1160_;
}
pub unsafe fn l_Lake_OrdHashSet_instForInOfMonad___boxed(
    mut v_00_u03b1_1161_: *mut LeanObject,
    mut v_inst_1162_: *mut LeanObject,
    mut v_inst_1163_: *mut LeanObject,
    mut v_m_1164_: *mut LeanObject,
    mut v_inst_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1166_: *mut LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lake_OrdHashSet_instForInOfMonad(
        v_00_u03b1_1161_,
        v_inst_1162_,
        v_inst_1163_,
        v_m_1164_,
        v_inst_1165_,
    );
    lean_dec_ref(v_inst_1163_);
    lean_dec_ref(v_inst_1162_);
    return v_res_1166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OrdHashSet(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OrdHashSet(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OrdHashSet(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OrdHashSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_OrdHashSet(builtin);
}
