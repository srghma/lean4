// Lean compiler output
// Module: Lake.Config.Dependency
// Imports: Init.Dynamic Init.System.FilePath Lean.Data.NameMap.Basic Lake.Util.Git Init.Data.ToString.Name Init.Data.ToString.Macro
use crate::ffi::{lean_nat_dec_le, lean_nat_to_int, lean_string_append};
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Dynamic::{initialize_Init_Dynamic, runtime_initialize_Init_Dynamic};
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, runtime_initialize_Init_System_FilePath,
};
use crate::r#gen::Lake::Util::Git::{initialize_Lake_Util_Git, runtime_initialize_Lake_Util_Git};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic, runtime_initialize_Lean_Data_NameMap_Basic,
};
pub static l_Lake_instInhabitedDependencySrc_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedDependencySrc_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedDependencySrc_default___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedDependencySrc_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependencySrc_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependencySrc: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 97, 107, 101, 46, 68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 83, 114, 99, 46,
            112, 97, 116, 104, 0,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprDependencySrc_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDependencySrc_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprDependencySrc_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDependencySrc_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDependencySrc_repr___closed__5_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            76, 97, 107, 101, 46, 68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 83, 114, 99, 46,
            103, 105, 116, 0,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprDependencySrc___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprDependencySrc_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprDependencySrc___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprDependencySrc: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedDependency_default___closed__0_value: leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedDependency_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependency_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependency: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut leanh::LeanObject;
pub static l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0]};
static mut l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut leanh::LeanObject;
static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
pub static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut leanh::LeanObject,4262777339930964728 as *mut leanh::LeanObject] };
static mut l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut leanh::LeanObject;
pub static mut l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value
) as *mut leanh::LeanObject;
pub static mut l_Lake_instTypeNameDependency: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value
)
    as *mut leanh::LeanObject;
pub static l_Lake_Dependency_fullName___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [47, 0],
    };
static mut l_Lake_Dependency_fullName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_fullName___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_DependencySrc_ctorIdx(
    mut v_x_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_192_) == 0 {
        let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_193_ = leanh::lean_unsigned_to_nat(0);
        return v___x_193_;
    } else {
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_194_ = leanh::lean_unsigned_to_nat(1);
        return v___x_194_;
    }
}
pub unsafe fn l_Lake_DependencySrc_ctorIdx___boxed(
    mut v_x_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lake_DependencySrc_ctorIdx(v_x_195_);
    leanh::lean_dec_ref(v_x_195_);
    return v_res_196_;
}
pub unsafe fn l_Lake_DependencySrc_ctorElim___redArg(
    mut v_t_197_: *mut leanh::LeanObject,
    mut v_k_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_197_) == 0 {
        let mut v_dir_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_dir_199_ = leanh::lean_ctor_get(v_t_197_, 0);
        leanh::lean_inc_ref(v_dir_199_);
        leanh::lean_dec_ref_known(v_t_197_, 1);
        v___x_200_ = leanh::lean_apply_1(v_k_198_, v_dir_199_);
        return v___x_200_;
    } else {
        let mut v_url_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_url_201_ = leanh::lean_ctor_get(v_t_197_, 0);
        leanh::lean_inc_ref(v_url_201_);
        v_rev_202_ = leanh::lean_ctor_get(v_t_197_, 1);
        leanh::lean_inc(v_rev_202_);
        v_subDir_203_ = leanh::lean_ctor_get(v_t_197_, 2);
        leanh::lean_inc(v_subDir_203_);
        leanh::lean_dec_ref_known(v_t_197_, 3);
        v___x_204_ = leanh::lean_apply_3(v_k_198_, v_url_201_, v_rev_202_, v_subDir_203_);
        return v___x_204_;
    }
}
pub unsafe fn l_Lake_DependencySrc_ctorElim(
    mut v_motive_205_: *mut leanh::LeanObject,
    mut v_ctorIdx_206_: *mut leanh::LeanObject,
    mut v_t_207_: *mut leanh::LeanObject,
    mut v_h_208_: *mut leanh::LeanObject,
    mut v_k_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_207_, v_k_209_);
    return v___x_210_;
}
pub unsafe fn l_Lake_DependencySrc_ctorElim___boxed(
    mut v_motive_211_: *mut leanh::LeanObject,
    mut v_ctorIdx_212_: *mut leanh::LeanObject,
    mut v_t_213_: *mut leanh::LeanObject,
    mut v_h_214_: *mut leanh::LeanObject,
    mut v_k_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ =
        l_Lake_DependencySrc_ctorElim(v_motive_211_, v_ctorIdx_212_, v_t_213_, v_h_214_, v_k_215_);
    leanh::lean_dec(v_ctorIdx_212_);
    return v_res_216_;
}
pub unsafe fn l_Lake_DependencySrc_path_elim___redArg(
    mut v_t_217_: *mut leanh::LeanObject,
    mut v_path_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_219_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_217_, v_path_218_);
    return v___x_219_;
}
pub unsafe fn l_Lake_DependencySrc_path_elim(
    mut v_motive_220_: *mut leanh::LeanObject,
    mut v_t_221_: *mut leanh::LeanObject,
    mut v_h_222_: *mut leanh::LeanObject,
    mut v_path_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_221_, v_path_223_);
    return v___x_224_;
}
pub unsafe fn l_Lake_DependencySrc_git_elim___redArg(
    mut v_t_225_: *mut leanh::LeanObject,
    mut v_git_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_225_, v_git_226_);
    return v___x_227_;
}
pub unsafe fn l_Lake_DependencySrc_git_elim(
    mut v_motive_228_: *mut leanh::LeanObject,
    mut v_t_229_: *mut leanh::LeanObject,
    mut v_h_230_: *mut leanh::LeanObject,
    mut v_git_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_229_, v_git_231_);
    return v___x_232_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(
    mut v_x_244_: *mut leanh::LeanObject,
    mut v_x_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_244_) == 0 {
                    v___x_246_ =
                        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1;
                    return v___x_246_;
                } else {
                    v_val_247_ = leanh::lean_ctor_get(v_x_244_, 0);
                    v_isSharedCheck_258_ = (!leanh::lean_is_exclusive(v_x_244_)) as u8;
                    if v_isSharedCheck_258_ == 0 {
                        v___x_249_ = v_x_244_;
                        v_isShared_250_ = v_isSharedCheck_258_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_247_);
                        leanh::lean_dec(v_x_244_);
                        v___x_249_ = leanh::lean_box(0);
                        v_isShared_250_ = v_isSharedCheck_258_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_251_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3;
                v___x_252_ = l_String_quote(v_val_247_);
                if v_isShared_250_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_249_, 3);
                    leanh::lean_ctor_set(v___x_249_, 0, v___x_252_);
                    v___x_254_ = v___x_249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_257_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_252_);
                    v___x_254_ = v_reuseFailAlloc_257_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_255_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_255_, 0, v___x_251_);
                leanh::lean_ctor_set(v___x_255_, 1, v___x_254_);
                v___x_256_ = l_Repr_addAppParen(v___x_255_, v_x_245_);
                return v___x_256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(
    mut v_x_259_: *mut leanh::LeanObject,
    mut v_x_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_x_259_, v_x_260_);
    leanh::lean_dec(v_x_260_);
    return v_res_261_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_271_: u8 = 0;
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_265_) == 0 {
                    v___x_267_ =
                        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1;
                    return v___x_267_;
                } else {
                    v_val_268_ = leanh::lean_ctor_get(v_x_265_, 0);
                    v_isSharedCheck_283_ = (!leanh::lean_is_exclusive(v_x_265_)) as u8;
                    if v_isSharedCheck_283_ == 0 {
                        v___x_270_ = v_x_265_;
                        v_isShared_271_ = v_isSharedCheck_283_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_268_);
                        leanh::lean_dec(v_x_265_);
                        v___x_270_ = leanh::lean_box(0);
                        v_isShared_271_ = v_isSharedCheck_283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_272_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3;
                v___x_273_ = leanh::lean_unsigned_to_nat(1024);
                v___x_274_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1;
                v___x_275_ = l_String_quote(v_val_268_);
                if v_isShared_271_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_270_, 3);
                    leanh::lean_ctor_set(v___x_270_, 0, v___x_275_);
                    v___x_277_ = v___x_270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_282_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_275_);
                    v___x_277_ = v_reuseFailAlloc_282_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_278_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_278_, 0, v___x_274_);
                leanh::lean_ctor_set(v___x_278_, 1, v___x_277_);
                v___x_279_ = l_Repr_addAppParen(v___x_278_, v___x_273_);
                v___x_280_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_280_, 0, v___x_272_);
                leanh::lean_ctor_set(v___x_280_, 1, v___x_279_);
                v___x_281_ = l_Repr_addAppParen(v___x_280_, v_x_266_);
                return v___x_281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(
    mut v_x_284_: *mut leanh::LeanObject,
    mut v_x_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_x_284_, v_x_285_);
    leanh::lean_dec(v_x_285_);
    return v_res_286_;
}
pub unsafe fn _init_l_Lake_instReprDependencySrc_repr___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = leanh::lean_unsigned_to_nat(2);
    v___x_294_ = lean_nat_to_int(v___x_293_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lake_instReprDependencySrc_repr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = leanh::lean_unsigned_to_nat(1);
    v___x_296_ = lean_nat_to_int(v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Lake_instReprDependencySrc_repr(
    mut v_x_303_: *mut leanh::LeanObject,
    mut v_prec_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dir_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_308_: u8 = 0;
    let mut v___y_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: u8 = 0;
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: u8 = 0;
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_329_: u8 = 0;
    let mut v_url_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: u8 = 0;
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u8 = 0;
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_303_) == 0 {
                    v_dir_305_ = leanh::lean_ctor_get(v_x_303_, 0);
                    v_isSharedCheck_329_ = (!leanh::lean_is_exclusive(v_x_303_)) as u8;
                    if v_isSharedCheck_329_ == 0 {
                        v___x_307_ = v_x_303_;
                        v_isShared_308_ = v_isSharedCheck_329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_dir_305_);
                        leanh::lean_dec(v_x_303_);
                        v___x_307_ = leanh::lean_box(0);
                        v_isShared_308_ = v_isSharedCheck_329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_url_330_ = leanh::lean_ctor_get(v_x_303_, 0);
                    leanh::lean_inc_ref(v_url_330_);
                    v_rev_331_ = leanh::lean_ctor_get(v_x_303_, 1);
                    leanh::lean_inc(v_rev_331_);
                    v_subDir_332_ = leanh::lean_ctor_get(v_x_303_, 2);
                    leanh::lean_inc(v_subDir_332_);
                    leanh::lean_dec_ref_known(v_x_303_, 3);
                    v___x_351_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_304_);
                    if v___x_352_ == 0 {
                        v___x_353_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprDependencySrc_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprDependencySrc_repr___closed__3,
                        );
                        v___y_334_ = v___x_353_;
                        state = 4;
                        continue;
                    } else {
                        v___x_354_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprDependencySrc_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprDependencySrc_repr___closed__4,
                        );
                        v___y_334_ = v___x_354_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_325_ = leanh::lean_unsigned_to_nat(1024);
                v___x_326_ = lean_nat_dec_le(v___x_325_, v_prec_304_);
                if v___x_326_ == 0 {
                    v___x_327_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__3_once),
                        _init_l_Lake_instReprDependencySrc_repr___closed__3,
                    );
                    v___y_310_ = v___x_327_;
                    state = 2;
                    continue;
                } else {
                    v___x_328_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__4_once),
                        _init_l_Lake_instReprDependencySrc_repr___closed__4,
                    );
                    v___y_310_ = v___x_328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_311_ = l_Lake_instReprDependencySrc_repr___closed__2;
                v___x_312_ = leanh::lean_unsigned_to_nat(1024);
                v___x_313_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1;
                v___x_314_ = l_String_quote(v_dir_305_);
                if v_isShared_308_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_307_, 3);
                    leanh::lean_ctor_set(v___x_307_, 0, v___x_314_);
                    v___x_316_ = v___x_307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_324_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_314_);
                    v___x_316_ = v_reuseFailAlloc_324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_317_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_317_, 0, v___x_313_);
                leanh::lean_ctor_set(v___x_317_, 1, v___x_316_);
                v___x_318_ = l_Repr_addAppParen(v___x_317_, v___x_312_);
                v___x_319_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_319_, 0, v___x_311_);
                leanh::lean_ctor_set(v___x_319_, 1, v___x_318_);
                leanh::lean_inc(v___y_310_);
                v___x_320_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_320_, 0, v___y_310_);
                leanh::lean_ctor_set(v___x_320_, 1, v___x_319_);
                v___x_321_ = 0;
                v___x_322_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_322_, 0, v___x_320_);
                leanh::lean_ctor_set_uint8(
                    v___x_322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_321_,
                );
                v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_304_);
                return v___x_323_;
            }
            4 => {
                v___x_335_ = leanh::lean_box(1);
                v___x_336_ = l_Lake_instReprDependencySrc_repr___closed__7;
                v___x_337_ = l_String_quote(v_url_330_);
                v___x_338_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_338_, 0, v___x_337_);
                v___x_339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_339_, 0, v___x_336_);
                leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                v___x_340_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_340_, 0, v___x_339_);
                leanh::lean_ctor_set(v___x_340_, 1, v___x_335_);
                v___x_341_ = leanh::lean_unsigned_to_nat(1024);
                v___x_342_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(
                    v_rev_331_, v___x_341_,
                );
                v___x_343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_343_, 0, v___x_340_);
                leanh::lean_ctor_set(v___x_343_, 1, v___x_342_);
                v___x_344_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_344_, 0, v___x_343_);
                leanh::lean_ctor_set(v___x_344_, 1, v___x_335_);
                v___x_345_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(
                    v_subDir_332_,
                    v___x_341_,
                );
                v___x_346_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_346_, 0, v___x_344_);
                leanh::lean_ctor_set(v___x_346_, 1, v___x_345_);
                leanh::lean_inc(v___y_334_);
                v___x_347_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_347_, 0, v___y_334_);
                leanh::lean_ctor_set(v___x_347_, 1, v___x_346_);
                v___x_348_ = 0;
                v___x_349_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_349_, 0, v___x_347_);
                leanh::lean_ctor_set_uint8(
                    v___x_349_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_348_,
                );
                v___x_350_ = l_Repr_addAppParen(v___x_349_, v_prec_304_);
                return v___x_350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprDependencySrc_repr___boxed(
    mut v_x_355_: *mut leanh::LeanObject,
    mut v_prec_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lake_instReprDependencySrc_repr(v_x_355_, v_prec_356_);
    leanh::lean_dec(v_prec_356_);
    return v_res_357_;
}
pub unsafe fn l_Lake_Dependency_fullName(
    mut v_dep_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: u8 = 0;
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_376_ = leanh::lean_ctor_get(v_dep_375_, 0);
    leanh::lean_inc(v_name_376_);
    v_scope_377_ = leanh::lean_ctor_get(v_dep_375_, 1);
    leanh::lean_inc_ref(v_scope_377_);
    leanh::lean_dec_ref(v_dep_375_);
    v___x_378_ = l_Lake_Dependency_fullName___closed__0;
    v___x_379_ = lean_string_append(v_scope_377_, v___x_378_);
    v___x_380_ = 1;
    v___x_381_ = l_Lean_Name_toString(v_name_376_, v___x_380_);
    v___x_382_ = lean_string_append(v___x_379_, v___x_381_);
    leanh::lean_dec_ref(v___x_381_);
    return v___x_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Dependency(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Dependency(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Dependency(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dependency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Dependency(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Dependency(builtin);
}