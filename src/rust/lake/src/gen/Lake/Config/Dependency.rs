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
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instInhabitedDependencySrc_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedDependencySrc_default___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedDependencySrc_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependencySrc_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependencySrc: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__0_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instReprDependencySrc_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDependencySrc_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDependencySrc_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprDependencySrc_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDependencySrc_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDependencySrc_repr___closed__5_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instReprDependencySrc_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc_repr___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDependencySrc_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDependencySrc___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprDependencySrc_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprDependencySrc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprDependencySrc: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDependencySrc___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedDependency_default___closed__0_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedDependencySrc_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedDependency_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependency_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDependency: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDependency_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [68, 101, 112, 101, 110, 100, 101, 110, 99, 121, 0]};
static mut l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut crate::leanh::LeanObject;
static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut crate::leanh::LeanObject,4262777339930964728 as *mut crate::leanh::LeanObject] };
static mut l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameDependency: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value
)
    as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_fullName___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Dependency_fullName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_fullName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_DependencySrc_ctorIdx(
    mut v_x_192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_192_) == 0 {
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_193_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_193_;
    } else {
        let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_194_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_194_;
    }
}
pub unsafe fn l_Lake_DependencySrc_ctorIdx___boxed(
    mut v_x_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Lake_DependencySrc_ctorIdx(v_x_195_);
    crate::leanh::lean_dec_ref(v_x_195_);
    return v_res_196_;
}
pub unsafe fn l_Lake_DependencySrc_ctorElim___redArg(
    mut v_t_197_: *mut crate::leanh::LeanObject,
    mut v_k_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_197_) == 0 {
        let mut v_dir_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dir_199_ = crate::leanh::lean_ctor_get(v_t_197_, 0);
        crate::leanh::lean_inc_ref(v_dir_199_);
        crate::leanh::lean_dec_ref_known(v_t_197_, 1);
        v___x_200_ = crate::leanh::lean_apply_1(v_k_198_, v_dir_199_);
        return v___x_200_;
    } else {
        let mut v_url_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_url_201_ = crate::leanh::lean_ctor_get(v_t_197_, 0);
        crate::leanh::lean_inc_ref(v_url_201_);
        v_rev_202_ = crate::leanh::lean_ctor_get(v_t_197_, 1);
        crate::leanh::lean_inc(v_rev_202_);
        v_subDir_203_ = crate::leanh::lean_ctor_get(v_t_197_, 2);
        crate::leanh::lean_inc(v_subDir_203_);
        crate::leanh::lean_dec_ref_known(v_t_197_, 3);
        v___x_204_ = crate::leanh::lean_apply_3(v_k_198_, v_url_201_, v_rev_202_, v_subDir_203_);
        return v___x_204_;
    }
}
pub unsafe fn l_Lake_DependencySrc_ctorElim(
    mut v_motive_205_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_206_: *mut crate::leanh::LeanObject,
    mut v_t_207_: *mut crate::leanh::LeanObject,
    mut v_h_208_: *mut crate::leanh::LeanObject,
    mut v_k_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_207_, v_k_209_);
    return v___x_210_;
}
pub unsafe fn l_Lake_DependencySrc_ctorElim___boxed(
    mut v_motive_211_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_212_: *mut crate::leanh::LeanObject,
    mut v_t_213_: *mut crate::leanh::LeanObject,
    mut v_h_214_: *mut crate::leanh::LeanObject,
    mut v_k_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ =
        l_Lake_DependencySrc_ctorElim(v_motive_211_, v_ctorIdx_212_, v_t_213_, v_h_214_, v_k_215_);
    crate::leanh::lean_dec(v_ctorIdx_212_);
    return v_res_216_;
}
pub unsafe fn l_Lake_DependencySrc_path_elim___redArg(
    mut v_t_217_: *mut crate::leanh::LeanObject,
    mut v_path_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_219_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_217_, v_path_218_);
    return v___x_219_;
}
pub unsafe fn l_Lake_DependencySrc_path_elim(
    mut v_motive_220_: *mut crate::leanh::LeanObject,
    mut v_t_221_: *mut crate::leanh::LeanObject,
    mut v_h_222_: *mut crate::leanh::LeanObject,
    mut v_path_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_221_, v_path_223_);
    return v___x_224_;
}
pub unsafe fn l_Lake_DependencySrc_git_elim___redArg(
    mut v_t_225_: *mut crate::leanh::LeanObject,
    mut v_git_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_225_, v_git_226_);
    return v___x_227_;
}
pub unsafe fn l_Lake_DependencySrc_git_elim(
    mut v_motive_228_: *mut crate::leanh::LeanObject,
    mut v_t_229_: *mut crate::leanh::LeanObject,
    mut v_h_230_: *mut crate::leanh::LeanObject,
    mut v_git_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_229_, v_git_231_);
    return v___x_232_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(
    mut v_x_244_: *mut crate::leanh::LeanObject,
    mut v_x_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_244_) == 0 {
                    v___x_246_ =
                        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1;
                    return v___x_246_;
                } else {
                    v_val_247_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
                    v_isSharedCheck_258_ = (!crate::leanh::lean_is_exclusive(v_x_244_)) as u8;
                    if v_isSharedCheck_258_ == 0 {
                        v___x_249_ = v_x_244_;
                        v_isShared_250_ = v_isSharedCheck_258_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_247_);
                        crate::leanh::lean_dec(v_x_244_);
                        v___x_249_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set_tag(v___x_249_, 3);
                    crate::leanh::lean_ctor_set(v___x_249_, 0, v___x_252_);
                    v___x_254_ = v___x_249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_257_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_252_);
                    v___x_254_ = v_reuseFailAlloc_257_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_255_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_255_, 0, v___x_251_);
                crate::leanh::lean_ctor_set(v___x_255_, 1, v___x_254_);
                v___x_256_ = l_Repr_addAppParen(v___x_255_, v_x_245_);
                return v___x_256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(
    mut v_x_259_: *mut crate::leanh::LeanObject,
    mut v_x_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_x_259_, v_x_260_);
    crate::leanh::lean_dec(v_x_260_);
    return v_res_261_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(
    mut v_x_265_: *mut crate::leanh::LeanObject,
    mut v_x_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_271_: u8 = 0;
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_265_) == 0 {
                    v___x_267_ =
                        l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1;
                    return v___x_267_;
                } else {
                    v_val_268_ = crate::leanh::lean_ctor_get(v_x_265_, 0);
                    v_isSharedCheck_283_ = (!crate::leanh::lean_is_exclusive(v_x_265_)) as u8;
                    if v_isSharedCheck_283_ == 0 {
                        v___x_270_ = v_x_265_;
                        v_isShared_271_ = v_isSharedCheck_283_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_268_);
                        crate::leanh::lean_dec(v_x_265_);
                        v___x_270_ = crate::leanh::lean_box(0);
                        v_isShared_271_ = v_isSharedCheck_283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_272_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3;
                v___x_273_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_274_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1;
                v___x_275_ = l_String_quote(v_val_268_);
                if v_isShared_271_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_270_, 3);
                    crate::leanh::lean_ctor_set(v___x_270_, 0, v___x_275_);
                    v___x_277_ = v___x_270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_282_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_275_);
                    v___x_277_ = v_reuseFailAlloc_282_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_278_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_278_, 0, v___x_274_);
                crate::leanh::lean_ctor_set(v___x_278_, 1, v___x_277_);
                v___x_279_ = l_Repr_addAppParen(v___x_278_, v___x_273_);
                v___x_280_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_280_, 0, v___x_272_);
                crate::leanh::lean_ctor_set(v___x_280_, 1, v___x_279_);
                v___x_281_ = l_Repr_addAppParen(v___x_280_, v_x_266_);
                return v___x_281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(
    mut v_x_284_: *mut crate::leanh::LeanObject,
    mut v_x_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_x_284_, v_x_285_);
    crate::leanh::lean_dec(v_x_285_);
    return v_res_286_;
}
pub unsafe fn _init_l_Lake_instReprDependencySrc_repr___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_294_ = lean_nat_to_int(v___x_293_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lake_instReprDependencySrc_repr___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_296_ = lean_nat_to_int(v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Lake_instReprDependencySrc_repr(
    mut v_x_303_: *mut crate::leanh::LeanObject,
    mut v_prec_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_308_: u8 = 0;
    let mut v___y_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: u8 = 0;
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: u8 = 0;
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_329_: u8 = 0;
    let mut v_url_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: u8 = 0;
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u8 = 0;
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_303_) == 0 {
                    v_dir_305_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
                    v_isSharedCheck_329_ = (!crate::leanh::lean_is_exclusive(v_x_303_)) as u8;
                    if v_isSharedCheck_329_ == 0 {
                        v___x_307_ = v_x_303_;
                        v_isShared_308_ = v_isSharedCheck_329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_dir_305_);
                        crate::leanh::lean_dec(v_x_303_);
                        v___x_307_ = crate::leanh::lean_box(0);
                        v_isShared_308_ = v_isSharedCheck_329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_url_330_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
                    crate::leanh::lean_inc_ref(v_url_330_);
                    v_rev_331_ = crate::leanh::lean_ctor_get(v_x_303_, 1);
                    crate::leanh::lean_inc(v_rev_331_);
                    v_subDir_332_ = crate::leanh::lean_ctor_get(v_x_303_, 2);
                    crate::leanh::lean_inc(v_subDir_332_);
                    crate::leanh::lean_dec_ref_known(v_x_303_, 3);
                    v___x_351_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_304_);
                    if v___x_352_ == 0 {
                        v___x_353_ = crate::leanh::lean_obj_once(
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
                        v___x_354_ = crate::leanh::lean_obj_once(
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
                v___x_325_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_326_ = lean_nat_dec_le(v___x_325_, v_prec_304_);
                if v___x_326_ == 0 {
                    v___x_327_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprDependencySrc_repr___closed__3_once),
                        _init_l_Lake_instReprDependencySrc_repr___closed__3,
                    );
                    v___y_310_ = v___x_327_;
                    state = 2;
                    continue;
                } else {
                    v___x_328_ = crate::leanh::lean_obj_once(
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
                v___x_312_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_313_ =
                    l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1;
                v___x_314_ = l_String_quote(v_dir_305_);
                if v_isShared_308_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_307_, 3);
                    crate::leanh::lean_ctor_set(v___x_307_, 0, v___x_314_);
                    v___x_316_ = v___x_307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_324_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_314_);
                    v___x_316_ = v_reuseFailAlloc_324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_317_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_317_, 0, v___x_313_);
                crate::leanh::lean_ctor_set(v___x_317_, 1, v___x_316_);
                v___x_318_ = l_Repr_addAppParen(v___x_317_, v___x_312_);
                v___x_319_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_319_, 0, v___x_311_);
                crate::leanh::lean_ctor_set(v___x_319_, 1, v___x_318_);
                crate::leanh::lean_inc(v___y_310_);
                v___x_320_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_320_, 0, v___y_310_);
                crate::leanh::lean_ctor_set(v___x_320_, 1, v___x_319_);
                v___x_321_ = 0;
                v___x_322_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_320_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_322_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_321_,
                );
                v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_304_);
                return v___x_323_;
            }
            4 => {
                v___x_335_ = crate::leanh::lean_box(1);
                v___x_336_ = l_Lake_instReprDependencySrc_repr___closed__7;
                v___x_337_ = l_String_quote(v_url_330_);
                v___x_338_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_338_, 0, v___x_337_);
                v___x_339_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_339_, 0, v___x_336_);
                crate::leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                v___x_340_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_339_);
                crate::leanh::lean_ctor_set(v___x_340_, 1, v___x_335_);
                v___x_341_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_342_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(
                    v_rev_331_, v___x_341_,
                );
                v___x_343_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_340_);
                crate::leanh::lean_ctor_set(v___x_343_, 1, v___x_342_);
                v___x_344_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_344_, 0, v___x_343_);
                crate::leanh::lean_ctor_set(v___x_344_, 1, v___x_335_);
                v___x_345_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(
                    v_subDir_332_,
                    v___x_341_,
                );
                v___x_346_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_346_, 0, v___x_344_);
                crate::leanh::lean_ctor_set(v___x_346_, 1, v___x_345_);
                crate::leanh::lean_inc(v___y_334_);
                v___x_347_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_347_, 0, v___y_334_);
                crate::leanh::lean_ctor_set(v___x_347_, 1, v___x_346_);
                v___x_348_ = 0;
                v___x_349_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_349_, 0, v___x_347_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_349_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_355_: *mut crate::leanh::LeanObject,
    mut v_prec_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lake_instReprDependencySrc_repr(v_x_355_, v_prec_356_);
    crate::leanh::lean_dec(v_prec_356_);
    return v_res_357_;
}
pub unsafe fn l_Lake_Dependency_fullName(
    mut v_dep_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: u8 = 0;
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_376_ = crate::leanh::lean_ctor_get(v_dep_375_, 0);
    crate::leanh::lean_inc(v_name_376_);
    v_scope_377_ = crate::leanh::lean_ctor_get(v_dep_375_, 1);
    crate::leanh::lean_inc_ref(v_scope_377_);
    crate::leanh::lean_dec_ref(v_dep_375_);
    v___x_378_ = l_Lake_Dependency_fullName___closed__0;
    v___x_379_ = lean_string_append(v_scope_377_, v___x_378_);
    v___x_380_ = 1;
    v___x_381_ = l_Lean_Name_toString(v_name_376_, v___x_380_);
    v___x_382_ = lean_string_append(v___x_379_, v___x_381_);
    crate::leanh::lean_dec_ref(v___x_381_);
    return v___x_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Dependency(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Dependency(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Dependency(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dependency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Dependency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Dependency(builtin);
}
