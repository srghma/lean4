// Lean compiler output
// Module: Init.GrindInstances.ToInt
// Imports: Init.Grind.ToInt Init.Data.SInt.Basic Init.Grind.ToInt Init.Data.BitVec.Bootstrap Init.Data.Int.LemmasAux Init.Data.Int.Pow Init.Data.SInt.Lemmas Init.Data.UInt.Lemmas Init.System.Platform
use crate::ffi::{
    lean_nat_to_int, lean_uint8_to_nat, lean_uint16_to_nat, lean_uint32_to_nat, lean_uint64_to_nat,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::Cast::l_Nat_cast;
use crate::r#gen::Init::Data::Int::Basic::l_Int_ofNat___boxed;
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, l_ISize_toInt___boxed, l_Int8_toInt___boxed,
    l_Int16_toInt___boxed, l_Int32_toInt___boxed, l_Int64_toInt___boxed,
    runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::SInt::Lemmas::{
    initialize_Init_Data_SInt_Lemmas, runtime_initialize_Init_Data_SInt_Lemmas,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, runtime_initialize_Init_System_Platform,
};
pub static l_Lean_Grind_instToIntIntIi___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Grind_instToIntIntIi___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntIntIi___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntIntIi: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntIntIi___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_instToIntNatCiOfNatInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_instToIntNatCiOfNatInt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value:
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
    m_fun: l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntUInt8UintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value:
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
    m_fun: l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntUInt16UintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value:
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
    m_fun: l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntUInt32UintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value:
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
    m_fun: l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntUInt64UintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value:
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
    m_fun: l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntUSizeUintNumBits___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntUSizeUintNumBits: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value:
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
    m_fun: l_Int8_toInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntInt8SintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value:
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
    m_fun: l_Int16_toInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntInt16SintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value:
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
    m_fun: l_Int32_toInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntInt32SintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value:
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
    m_fun: l_Int64_toInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntInt64SintOfNatNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value:
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
    m_fun: l_ISize_toInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instToIntISizeSintNumBits___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instToIntISizeSintNumBits: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___f_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_66_ =
        crate::leanh::lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    v___x_67_ = crate::leanh::lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_67_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_67_, 1, v___f_66_);
    return v___x_67_;
}
pub unsafe fn _init_l_Lean_Grind_instToIntNatCiOfNatInt() -> *mut crate::leanh::LeanObject {
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instToIntNatCiOfNatInt___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_once),
        _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0,
    );
    return v___x_68_;
}
pub unsafe fn l_Lean_Grind_instToIntFinCoOfNatIntCast(
    mut v_n_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_70_ =
        crate::leanh::lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    return v___f_70_;
}
pub unsafe fn l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(
    mut v_n_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l_Lean_Grind_instToIntFinCoOfNatIntCast(v_n_71_);
    crate::leanh::lean_dec(v_n_71_);
    return v_res_72_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(
    mut v_x_73_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = lean_uint8_to_nat(v_x_73_);
    v___x_75_ = lean_nat_to_int(v___x_74_);
    return v___x_75_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed(
    mut v_x_76_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_77_: u8 = 0;
    let mut v_res_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_77_ = (crate::leanh::lean_unbox(v_x_76_) as u8);
    v_res_78_ = l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(v_x_boxed_77_);
    return v_res_78_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(
    mut v_x_81_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = lean_uint16_to_nat(v_x_81_);
    v___x_83_ = lean_nat_to_int(v___x_82_);
    return v___x_83_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed(
    mut v_x_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_85_: u16 = 0;
    let mut v_res_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_85_ = (crate::leanh::lean_unbox(v_x_84_) as u16);
    v_res_86_ = l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(v_x_boxed_85_);
    return v_res_86_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(
    mut v_x_89_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_90_ = lean_uint32_to_nat(v_x_89_);
    v___x_91_ = lean_nat_to_int(v___x_90_);
    return v___x_91_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed(
    mut v_x_92_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_93_: u32 = 0;
    let mut v_res_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_93_ = crate::leanh::lean_unbox_uint32(v_x_92_);
    crate::leanh::lean_dec(v_x_92_);
    v_res_94_ = l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(v_x_boxed_93_);
    return v_res_94_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(
    mut v_x_97_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_98_ = lean_uint64_to_nat(v_x_97_);
    v___x_99_ = lean_nat_to_int(v___x_98_);
    return v___x_99_;
}
pub unsafe fn l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(
    mut v_x_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_101_: u64 = 0;
    let mut v_res_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_101_ = crate::leanh::lean_unbox_uint64(v_x_100_);
    crate::leanh::lean_dec_ref(v_x_100_);
    v_res_102_ = l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(v_x_boxed_101_);
    return v_res_102_;
}
pub unsafe fn l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(
    mut v_x_105_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = lean_usize_to_nat(v_x_105_);
    v___x_107_ = lean_nat_to_int(v___x_106_);
    return v___x_107_;
}
pub unsafe fn l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed(
    mut v_x_108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_109_: usize = 0;
    let mut v_res_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_109_ = crate::leanh::lean_unbox_usize(v_x_108_);
    crate::leanh::lean_dec(v_x_108_);
    v_res_110_ = l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(v_x_boxed_109_);
    return v_res_110_;
}
pub unsafe fn l_Lean_Grind_instToIntBitVecUint(
    mut v_v_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_122_ =
        crate::leanh::lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    return v___f_122_;
}
pub unsafe fn l_Lean_Grind_instToIntBitVecUint___boxed(
    mut v_v_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_124_ = l_Lean_Grind_instToIntBitVecUint(v_v_123_);
    crate::leanh::lean_dec(v_v_123_);
    return v_res_124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_ToInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Grind_instToIntNatCiOfNatInt = _init_l_Lean_Grind_instToIntNatCiOfNatInt();
    crate::leanh::lean_mark_persistent(l_Lean_Grind_instToIntNatCiOfNatInt);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_ToInt(
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
pub unsafe fn initialize_Init_GrindInstances_ToInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_ToInt(builtin);
}
