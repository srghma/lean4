// Lean compiler output
// Module: Lean.ProjFns
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_MapDeclarationExtension_contains___redArg,
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
    runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_find_x3f};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedProjectionFunctionInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedProjectionFunctionInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 116, 111, 114, 78, 97, 109, 101, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 117, 109, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [105, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [102, 114, 111, 109, 67, 108, 97, 115, 115, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value
    ) as *mut LeanObject],
};
static mut l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_instReprProjectionFunctionInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprProjectionFunctionInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprProjectionFunctionInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprProjectionFunctionInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 70, 110, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject,5140131695607655440 as *mut LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedAuxParentProjectionInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedAuxParentProjectionInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprAuxParentProjectionInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprAuxParentProjectionInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprAuxParentProjectionInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instReprAuxParentProjectionInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprAuxParentProjectionInfo___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 117, 120, 80, 97, 114, 101, 110, 116, 80, 114, 111, 106, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject,3130712378843676676 as *mut LeanObject] };
static mut l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Lean_instReprProjectionFunctionInfo_repr_spec__0(
    mut v_a_488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v___x_489_ = lean_nat_to_int(v_a_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = lean_unsigned_to_nat(12);
    v___x_504_ = lean_nat_to_int(v___x_503_);
    return v___x_504_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_unsigned_to_nat(13);
    v___x_512_ = lean_nat_to_int(v___x_511_);
    return v___x_512_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_unsigned_to_nat(5);
    v___x_517_ = lean_nat_to_int(v___x_516_);
    return v___x_517_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0;
    v___x_523_ = lean_string_length(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20()
-> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19,
    );
    v___x_525_ = lean_nat_to_int(v___x_524_);
    return v___x_525_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr___redArg(
    mut v_x_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctorName_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fromClass_534_: u8 = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: u8 = 0;
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v_ctorName_531_ = lean_ctor_get(v_x_530_, 0);
    lean_inc(v_ctorName_531_);
    v_numParams_532_ = lean_ctor_get(v_x_530_, 1);
    lean_inc(v_numParams_532_);
    v_i_533_ = lean_ctor_get(v_x_530_, 2);
    lean_inc(v_i_533_);
    v_fromClass_534_ = lean_ctor_get_uint8(
        v_x_530_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_x_530_);
    v___x_535_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5;
    v___x_536_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6;
    v___x_537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7,
    );
    v___x_538_ = lean_unsigned_to_nat(0);
    v___x_539_ = l_Lean_Name_reprPrec(v_ctorName_531_, v___x_538_);
    v___x_540_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_540_, 0, v___x_537_);
    lean_ctor_set(v___x_540_, 1, v___x_539_);
    v___x_541_ = 0;
    v___x_542_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_542_, 0, v___x_540_);
    lean_ctor_set_uint8(
        v___x_542_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_543_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_543_, 0, v___x_536_);
    lean_ctor_set(v___x_543_, 1, v___x_542_);
    v___x_544_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9;
    v___x_545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_545_, 0, v___x_543_);
    lean_ctor_set(v___x_545_, 1, v___x_544_);
    v___x_546_ = lean_box(1);
    v___x_547_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_547_, 0, v___x_545_);
    lean_ctor_set(v___x_547_, 1, v___x_546_);
    v___x_548_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11;
    v___x_549_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_549_, 0, v___x_547_);
    lean_ctor_set(v___x_549_, 1, v___x_548_);
    v___x_550_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_550_, 0, v___x_549_);
    lean_ctor_set(v___x_550_, 1, v___x_535_);
    v___x_551_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12,
    );
    v___x_552_ = l_Nat_reprFast(v_numParams_532_);
    v___x_553_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_553_, 0, v___x_552_);
    v___x_554_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_554_, 0, v___x_551_);
    lean_ctor_set(v___x_554_, 1, v___x_553_);
    v___x_555_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_555_, 0, v___x_554_);
    lean_ctor_set_uint8(
        v___x_555_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_556_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_556_, 0, v___x_550_);
    lean_ctor_set(v___x_556_, 1, v___x_555_);
    v___x_557_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_557_, 0, v___x_556_);
    lean_ctor_set(v___x_557_, 1, v___x_544_);
    v___x_558_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_558_, 0, v___x_557_);
    lean_ctor_set(v___x_558_, 1, v___x_546_);
    v___x_559_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14;
    v___x_560_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_560_, 0, v___x_558_);
    lean_ctor_set(v___x_560_, 1, v___x_559_);
    v___x_561_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_561_, 0, v___x_560_);
    lean_ctor_set(v___x_561_, 1, v___x_535_);
    v___x_562_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15,
    );
    v___x_563_ = l_Nat_reprFast(v_i_533_);
    v___x_564_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_564_, 0, v___x_563_);
    v___x_565_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_565_, 0, v___x_562_);
    lean_ctor_set(v___x_565_, 1, v___x_564_);
    v___x_566_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_566_, 0, v___x_565_);
    lean_ctor_set_uint8(
        v___x_566_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_567_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_567_, 0, v___x_561_);
    lean_ctor_set(v___x_567_, 1, v___x_566_);
    v___x_568_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_568_, 0, v___x_567_);
    lean_ctor_set(v___x_568_, 1, v___x_544_);
    v___x_569_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_569_, 0, v___x_568_);
    lean_ctor_set(v___x_569_, 1, v___x_546_);
    v___x_570_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17;
    v___x_571_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_571_, 0, v___x_569_);
    lean_ctor_set(v___x_571_, 1, v___x_570_);
    v___x_572_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_572_, 0, v___x_571_);
    lean_ctor_set(v___x_572_, 1, v___x_535_);
    v___x_573_ = l_Bool_repr___redArg(v_fromClass_534_);
    v___x_574_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_574_, 0, v___x_551_);
    lean_ctor_set(v___x_574_, 1, v___x_573_);
    v___x_575_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_575_, 0, v___x_574_);
    lean_ctor_set_uint8(
        v___x_575_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_541_,
    );
    v___x_576_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_576_, 0, v___x_572_);
    lean_ctor_set(v___x_576_, 1, v___x_575_);
    v___x_577_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once
        ),
        _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20,
    );
    v___x_578_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21;
    v___x_579_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_579_, 0, v___x_578_);
    lean_ctor_set(v___x_579_, 1, v___x_576_);
    v___x_580_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22;
    v___x_581_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_581_, 0, v___x_579_);
    lean_ctor_set(v___x_581_, 1, v___x_580_);
    v___x_582_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_582_, 0, v___x_577_);
    lean_ctor_set(v___x_582_, 1, v___x_581_);
    v___x_583_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_583_, 0, v___x_582_);
    lean_ctor_set_uint8(
        v___x_583_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_541_,
    );
    return v___x_583_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr(
    mut v_x_584_: *mut LeanObject,
    mut v_prec_585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg(v_x_584_);
    return v___x_586_;
}
pub unsafe fn l_Lean_instReprProjectionFunctionInfo_repr___boxed(
    mut v_x_587_: *mut LeanObject,
    mut v_prec_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_589_: *mut LeanObject = core::ptr::null_mut();
    v_res_589_ = l_Lean_instReprProjectionFunctionInfo_repr(v_x_587_, v_prec_588_);
    lean_dec(v_prec_588_);
    return v_res_589_;
}
pub unsafe fn lean_mk_projection_info(
    mut v_ctorName_592_: *mut LeanObject,
    mut v_numParams_593_: *mut LeanObject,
    mut v_i_594_: *mut LeanObject,
    mut v_fromClass_595_: u8,
) -> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_596_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_596_, 0, v_ctorName_592_);
    lean_ctor_set(v___x_596_, 1, v_numParams_593_);
    lean_ctor_set(v___x_596_, 2, v_i_594_);
    lean_ctor_set_uint8(
        v___x_596_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_fromClass_595_,
    );
    return v___x_596_;
}
pub unsafe fn l_Lean_mkProjectionInfoEx___boxed(
    mut v_ctorName_597_: *mut LeanObject,
    mut v_numParams_598_: *mut LeanObject,
    mut v_i_599_: *mut LeanObject,
    mut v_fromClass_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromClass_boxed_601_: u8 = 0;
    let mut v_res_602_: *mut LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_601_ = (lean_unbox(v_fromClass_600_) as u8);
    v_res_602_ = lean_mk_projection_info(
        v_ctorName_597_,
        v_numParams_598_,
        v_i_599_,
        v_fromClass_boxed_601_,
    );
    return v_res_602_;
}
pub unsafe fn lean_projection_info_from_class(mut v_info_603_: *mut LeanObject) -> u8 {
    let mut v_fromClass_604_: u8 = 0;
    v_fromClass_604_ = lean_ctor_get_uint8(
        v_info_603_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_info_603_);
    return v_fromClass_604_;
}
pub unsafe fn l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(
    mut v_info_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_606_: u8 = 0;
    let mut v_r_607_: *mut LeanObject = core::ptr::null_mut();
    v_res_606_ = lean_projection_info_from_class(v_info_605_);
    v_r_607_ = lean_box((v_res_606_) as usize);
    return v_r_607_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_608_: *mut LeanObject,
    mut v_x_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_609_) == 0 {
                    v_k_610_ = lean_ctor_get(v_x_609_, 1);
                    v_v_611_ = lean_ctor_get(v_x_609_, 2);
                    v_l_612_ = lean_ctor_get(v_x_609_, 3);
                    v_r_613_ = lean_ctor_get(v_x_609_, 4);
                    v___x_614_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_608_, v_l_612_);
                    lean_inc(v_v_611_);
                    lean_inc(v_k_610_);
                    v___x_615_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_615_, 0, v_k_610_);
                    lean_ctor_set(v___x_615_, 1, v_v_611_);
                    v___x_616_ = lean_array_push(v___x_614_, v___x_615_);
                    v_init_608_ = v___x_616_;
                    v_x_609_ = v_r_613_;
                    state = 0;
                    continue;
                } else {
                    return v_init_608_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_618_: *mut LeanObject,
    mut v_x_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_620_: *mut LeanObject = core::ptr::null_mut();
    v_res_620_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_618_, v_x_619_);
    lean_dec(v_x_619_);
    return v_res_620_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(
    mut v_env_621_: *mut LeanObject,
    mut v_as_622_: *mut LeanObject,
    mut v_i_623_: usize,
    mut v_stop_624_: usize,
    mut v_b_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: usize = 0;
    let mut v___x_629_: usize = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_631_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
                if v___x_631_ == 0 {
                    v___x_632_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
                    v_fst_633_ = lean_ctor_get(v___x_632_, 0);
                    lean_inc(v_fst_633_);
                    lean_inc_ref(v_env_621_);
                    v___x_634_ = l_Lean_Environment_contains(v_env_621_, v_fst_633_, v___x_631_);
                    if v___x_634_ == 0 {
                        v___y_627_ = v_b_625_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_632_);
                        v___x_635_ = lean_array_push(v_b_625_, v___x_632_);
                        v___y_627_ = v___x_635_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_621_);
                    return v_b_625_;
                }
            }
            1 => {
                v___x_628_ = 1usize;
                v___x_629_ = lean_usize_add(v_i_623_, v___x_628_);
                v_i_623_ = v___x_629_;
                v_b_625_ = v___y_627_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_636_: *mut LeanObject,
    mut v_as_637_: *mut LeanObject,
    mut v_i_638_: *mut LeanObject,
    mut v_stop_639_: *mut LeanObject,
    mut v_b_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_641_: usize = 0;
    let mut v_stop_boxed_642_: usize = 0;
    let mut v_res_643_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_641_ = lean_unbox_usize(v_i_638_);
    lean_dec(v_i_638_);
    v_stop_boxed_642_ = lean_unbox_usize(v_stop_639_);
    lean_dec(v_stop_639_);
    v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_636_, v_as_637_, v_i_boxed_641_, v_stop_boxed_642_, v_b_640_);
    lean_dec_ref(v_as_637_);
    return v_res_643_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
    mut v_env_650_: *mut LeanObject,
    mut v_s_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: u8 = 0;
    v___x_652_ = lean_unsigned_to_nat(0);
    v___x_653_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_654_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v___x_653_, v_s_651_);
    v___x_655_ = lean_array_get_size(v___x_654_);
    v___x_656_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_657_ = lean_nat_dec_lt(v___x_652_, v___x_655_);
    if v___x_657_ == 0 {
        let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_654_);
        lean_dec_ref(v_env_650_);
        v___x_658_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
        return v___x_658_;
    } else {
        let mut v___x_659_: u8 = 0;
        v___x_659_ = lean_nat_dec_le(v___x_655_, v___x_655_);
        if v___x_659_ == 0 {
            if v___x_657_ == 0 {
                let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_654_);
                lean_dec_ref(v_env_650_);
                v___x_660_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
                return v___x_660_;
            } else {
                let mut v___x_661_: usize = 0;
                let mut v___x_662_: usize = 0;
                let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
                v___x_661_ = 0usize;
                v___x_662_ = lean_usize_of_nat(v___x_655_);
                v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_650_, v___x_654_, v___x_661_, v___x_662_, v___x_656_);
                lean_dec_ref(v___x_654_);
                lean_inc_ref_n(v___x_663_, 2);
                v___x_664_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_664_, 0, v___x_663_);
                lean_ctor_set(v___x_664_, 1, v___x_663_);
                lean_ctor_set(v___x_664_, 2, v___x_663_);
                return v___x_664_;
            }
        } else {
            let mut v___x_665_: usize = 0;
            let mut v___x_666_: usize = 0;
            let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
            v___x_665_ = 0usize;
            v___x_666_ = lean_usize_of_nat(v___x_655_);
            v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_650_, v___x_654_, v___x_665_, v___x_666_, v___x_656_);
            lean_dec_ref(v___x_654_);
            lean_inc_ref_n(v___x_667_, 2);
            v___x_668_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_668_, 0, v___x_667_);
            lean_ctor_set(v___x_668_, 1, v___x_667_);
            lean_ctor_set(v___x_668_, 2, v___x_667_);
            return v___x_668_;
        }
    }
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(
    mut v_env_669_: *mut LeanObject,
    mut v_s_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_671_: *mut LeanObject = core::ptr::null_mut();
    v_res_671_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(v_env_669_, v_s_670_);
    lean_dec(v_s_670_);
    return v_res_671_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v___f_681_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_682_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_683_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_684_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_682_, v___x_683_, v___f_681_);
    return v___x_684_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(
    mut v_a_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_686_: *mut LeanObject = core::ptr::null_mut();
    v_res_686_ =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
        );
    return v_res_686_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(
    mut v_init_687_: *mut LeanObject,
    mut v_t_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_687_, v_t_688_);
    return v___x_689_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_690_: *mut LeanObject,
    mut v_t_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(v_init_690_, v_t_691_);
    lean_dec(v_t_691_);
    return v_res_692_;
}
pub unsafe fn l_Lean_addProjectionFnInfo(
    mut v_env_693_: *mut LeanObject,
    mut v_projName_694_: *mut LeanObject,
    mut v_ctorName_695_: *mut LeanObject,
    mut v_numParams_696_: *mut LeanObject,
    mut v_i_697_: *mut LeanObject,
    mut v_fromClass_698_: u8,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_699_ = l_Lean_projectionFnInfoExt;
    v___x_700_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_700_, 0, v_ctorName_695_);
    lean_ctor_set(v___x_700_, 1, v_numParams_696_);
    lean_ctor_set(v___x_700_, 2, v_i_697_);
    lean_ctor_set_uint8(
        v___x_700_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_fromClass_698_,
    );
    v___x_701_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_699_,
        v_env_693_,
        v_projName_694_,
        v___x_700_,
    );
    return v___x_701_;
}
pub unsafe fn l_Lean_addProjectionFnInfo___boxed(
    mut v_env_702_: *mut LeanObject,
    mut v_projName_703_: *mut LeanObject,
    mut v_ctorName_704_: *mut LeanObject,
    mut v_numParams_705_: *mut LeanObject,
    mut v_i_706_: *mut LeanObject,
    mut v_fromClass_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromClass_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_708_ = (lean_unbox(v_fromClass_707_) as u8);
    v_res_709_ = l_Lean_addProjectionFnInfo(
        v_env_702_,
        v_projName_703_,
        v_ctorName_704_,
        v_numParams_705_,
        v_i_706_,
        v_fromClass_boxed_708_,
    );
    return v_res_709_;
}
pub unsafe fn l_Lean_Environment_getProjectionFnInfo_x3f(
    mut v_env_710_: *mut LeanObject,
    mut v_projName_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_projectionFnInfoExt;
    v_toEnvExtension_713_ = lean_ctor_get(v___x_712_, 0);
    v_asyncMode_714_ = lean_ctor_get(v_toEnvExtension_713_, 2);
    v___x_715_ = l_Lean_instInhabitedProjectionFunctionInfo_default;
    v___x_716_ = 0;
    v___x_717_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_715_,
        v___x_712_,
        v_env_710_,
        v_projName_711_,
        v_asyncMode_714_,
        v___x_716_,
    );
    return v___x_717_;
}
pub unsafe fn l_Lean_Environment_isProjectionFn(
    mut v_env_718_: *mut LeanObject,
    mut v_declName_719_: *mut LeanObject,
) -> u8 {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    v___x_720_ = l_Lean_instInhabitedProjectionFunctionInfo_default;
    v___x_721_ = l_Lean_projectionFnInfoExt;
    v___x_722_ = l_Lean_MapDeclarationExtension_contains___redArg(
        v___x_720_,
        v___x_721_,
        v_env_718_,
        v_declName_719_,
    );
    return v___x_722_;
}
pub unsafe fn l_Lean_Environment_isProjectionFn___boxed(
    mut v_env_723_: *mut LeanObject,
    mut v_declName_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_725_: u8 = 0;
    let mut v_r_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_Environment_isProjectionFn(v_env_723_, v_declName_724_);
    v_r_726_ = lean_box((v_res_725_) as usize);
    return v_r_726_;
}
pub unsafe fn l_Lean_Environment_getProjectionStructureName_x3f(
    mut v_env_727_: *mut LeanObject,
    mut v_projName_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_738_: u8 = 0;
    let mut v_val_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_induct_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_env_727_);
                v___x_729_ =
                    l_Lean_Environment_getProjectionFnInfo_x3f(v_env_727_, v_projName_728_);
                if lean_obj_tag(v___x_729_) == 0 {
                    lean_dec_ref(v_env_727_);
                    v___x_730_ = lean_box(0);
                    return v___x_730_;
                } else {
                    v_val_731_ = lean_ctor_get(v___x_729_, 0);
                    lean_inc(v_val_731_);
                    lean_dec_ref_known(v___x_729_, 1);
                    v_ctorName_732_ = lean_ctor_get(v_val_731_, 0);
                    lean_inc(v_ctorName_732_);
                    lean_dec(v_val_731_);
                    v___x_733_ = 0;
                    v___x_734_ =
                        l_Lean_Environment_find_x3f(v_env_727_, v_ctorName_732_, v___x_733_);
                    if lean_obj_tag(v___x_734_) == 1 {
                        v_val_735_ = lean_ctor_get(v___x_734_, 0);
                        v_isSharedCheck_745_ = (!lean_is_exclusive(v___x_734_)) as u8;
                        if v_isSharedCheck_745_ == 0 {
                            v___x_737_ = v___x_734_;
                            v_isShared_738_ = v_isSharedCheck_745_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_735_);
                            lean_dec(v___x_734_);
                            v___x_737_ = lean_box(0);
                            v_isShared_738_ = v_isSharedCheck_745_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_734_);
                        v___x_746_ = lean_box(0);
                        return v___x_746_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_val_735_) == 6 {
                    v_val_739_ = lean_ctor_get(v_val_735_, 0);
                    lean_inc_ref(v_val_739_);
                    lean_dec_ref_known(v_val_735_, 1);
                    v_induct_740_ = lean_ctor_get(v_val_739_, 1);
                    lean_inc(v_induct_740_);
                    lean_dec_ref(v_val_739_);
                    if v_isShared_738_ == 0 {
                        lean_ctor_set(v___x_737_, 0, v_induct_740_);
                        v___x_742_ = v___x_737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_743_, 0, v_induct_740_);
                        v___x_742_ = v_reuseFailAlloc_743_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_737_);
                    lean_dec(v_val_735_);
                    v___x_744_ = lean_box(0);
                    return v___x_744_;
                }
            }
            2 => {
                return v___x_742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isProjectionFn___redArg___lam__0(
    mut v_declName_747_: *mut LeanObject,
    mut v_toPure_748_: *mut LeanObject,
    mut v_____do__lift_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lean_Environment_isProjectionFn(v_____do__lift_749_, v_declName_747_);
    v___x_751_ = lean_box((v___x_750_) as usize);
    v___x_752_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_isProjectionFn___redArg(
    mut v_inst_753_: *mut LeanObject,
    mut v_inst_754_: *mut LeanObject,
    mut v_declName_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_756_ = lean_ctor_get(v_inst_754_, 0);
    lean_inc_ref(v_toApplicative_756_);
    v_toBind_757_ = lean_ctor_get(v_inst_754_, 1);
    lean_inc(v_toBind_757_);
    lean_dec_ref(v_inst_754_);
    v_getEnv_758_ = lean_ctor_get(v_inst_753_, 0);
    lean_inc(v_getEnv_758_);
    lean_dec_ref(v_inst_753_);
    v_toPure_759_ = lean_ctor_get(v_toApplicative_756_, 1);
    lean_inc(v_toPure_759_);
    lean_dec_ref(v_toApplicative_756_);
    v___f_760_ = lean_alloc_closure(
        l_Lean_isProjectionFn___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_760_, 0, v_declName_755_);
    lean_closure_set(v___f_760_, 1, v_toPure_759_);
    v___x_761_ = lean_apply_4(
        v_toBind_757_,
        lean_box(0),
        lean_box(0),
        v_getEnv_758_,
        v___f_760_,
    );
    return v___x_761_;
}
pub unsafe fn l_Lean_isProjectionFn(
    mut v_m_762_: *mut LeanObject,
    mut v_inst_763_: *mut LeanObject,
    mut v_inst_764_: *mut LeanObject,
    mut v_declName_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_isProjectionFn___redArg(v_inst_763_, v_inst_764_, v_declName_765_);
    return v___x_766_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(
    mut v_declName_767_: *mut LeanObject,
    mut v_toPure_768_: *mut LeanObject,
    mut v_____do__lift_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_769_, v_declName_767_);
    v___x_771_ = lean_apply_2(v_toPure_768_, lean_box(0), v___x_770_);
    return v___x_771_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___redArg(
    mut v_inst_772_: *mut LeanObject,
    mut v_inst_773_: *mut LeanObject,
    mut v_declName_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_775_ = lean_ctor_get(v_inst_773_, 0);
    lean_inc_ref(v_toApplicative_775_);
    v_toBind_776_ = lean_ctor_get(v_inst_773_, 1);
    lean_inc(v_toBind_776_);
    lean_dec_ref(v_inst_773_);
    v_getEnv_777_ = lean_ctor_get(v_inst_772_, 0);
    lean_inc(v_getEnv_777_);
    lean_dec_ref(v_inst_772_);
    v_toPure_778_ = lean_ctor_get(v_toApplicative_775_, 1);
    lean_inc(v_toPure_778_);
    lean_dec_ref(v_toApplicative_775_);
    v___f_779_ = lean_alloc_closure(
        l_Lean_getProjectionFnInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_779_, 0, v_declName_774_);
    lean_closure_set(v___f_779_, 1, v_toPure_778_);
    v___x_780_ = lean_apply_4(
        v_toBind_776_,
        lean_box(0),
        lean_box(0),
        v_getEnv_777_,
        v___f_779_,
    );
    return v___x_780_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f(
    mut v_m_781_: *mut LeanObject,
    mut v_inst_782_: *mut LeanObject,
    mut v_inst_783_: *mut LeanObject,
    mut v_declName_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_782_, v_inst_783_, v_declName_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr___redArg(
    mut v_x_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numParams_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fromClass_799_: u8 = 0;
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numParams_798_ = lean_ctor_get(v_x_797_, 0);
                v_fromClass_799_ = lean_ctor_get_uint8(
                    v_x_797_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_832_ = (!lean_is_exclusive(v_x_797_)) as u8;
                if v_isSharedCheck_832_ == 0 {
                    v___x_801_ = v_x_797_;
                    v_isShared_802_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numParams_798_);
                    lean_dec(v_x_797_);
                    v___x_801_ = lean_box(0);
                    v_isShared_802_ = v_isSharedCheck_832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_803_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5;
                v___x_804_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1;
                v___x_805_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12,
                );
                v___x_806_ = l_Nat_reprFast(v_numParams_798_);
                v___x_807_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_807_, 0, v___x_806_);
                v___x_808_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_808_, 0, v___x_805_);
                lean_ctor_set(v___x_808_, 1, v___x_807_);
                v___x_809_ = 0;
                if v_isShared_802_ == 0 {
                    lean_ctor_set_tag(v___x_801_, 6);
                    lean_ctor_set(v___x_801_, 0, v___x_808_);
                    v___x_811_ = v___x_801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = lean_alloc_ctor(6, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_808_);
                    v___x_811_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_811_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                v___x_812_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_812_, 0, v___x_804_);
                lean_ctor_set(v___x_812_, 1, v___x_811_);
                v___x_813_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9;
                v___x_814_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_814_, 0, v___x_812_);
                lean_ctor_set(v___x_814_, 1, v___x_813_);
                v___x_815_ = lean_box(1);
                v___x_816_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_816_, 0, v___x_814_);
                lean_ctor_set(v___x_816_, 1, v___x_815_);
                v___x_817_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17;
                v___x_818_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_818_, 0, v___x_816_);
                lean_ctor_set(v___x_818_, 1, v___x_817_);
                v___x_819_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_819_, 0, v___x_818_);
                lean_ctor_set(v___x_819_, 1, v___x_803_);
                v___x_820_ = l_Bool_repr___redArg(v_fromClass_799_);
                v___x_821_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_821_, 0, v___x_805_);
                lean_ctor_set(v___x_821_, 1, v___x_820_);
                v___x_822_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_822_, 0, v___x_821_);
                lean_ctor_set_uint8(
                    v___x_822_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                v___x_823_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_823_, 0, v___x_819_);
                lean_ctor_set(v___x_823_, 1, v___x_822_);
                v___x_824_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once
                    ),
                    _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20,
                );
                v___x_825_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21;
                v___x_826_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_826_, 0, v___x_825_);
                lean_ctor_set(v___x_826_, 1, v___x_823_);
                v___x_827_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22;
                v___x_828_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_828_, 0, v___x_826_);
                lean_ctor_set(v___x_828_, 1, v___x_827_);
                v___x_829_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_829_, 0, v___x_824_);
                lean_ctor_set(v___x_829_, 1, v___x_828_);
                v___x_830_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_830_, 0, v___x_829_);
                lean_ctor_set_uint8(
                    v___x_830_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_809_,
                );
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr(
    mut v_x_833_: *mut LeanObject,
    mut v_prec_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_835_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_833_);
    return v___x_835_;
}
pub unsafe fn l_Lean_instReprAuxParentProjectionInfo_repr___boxed(
    mut v_x_836_: *mut LeanObject,
    mut v_prec_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_838_: *mut LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_836_, v_prec_837_);
    lean_dec(v_prec_837_);
    return v_res_838_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_841_: *mut LeanObject,
    mut v_x_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_842_) == 0 {
                    v_k_843_ = lean_ctor_get(v_x_842_, 1);
                    v_v_844_ = lean_ctor_get(v_x_842_, 2);
                    v_l_845_ = lean_ctor_get(v_x_842_, 3);
                    v_r_846_ = lean_ctor_get(v_x_842_, 4);
                    v___x_847_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_841_, v_l_845_);
                    lean_inc(v_v_844_);
                    lean_inc(v_k_843_);
                    v___x_848_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_848_, 0, v_k_843_);
                    lean_ctor_set(v___x_848_, 1, v_v_844_);
                    v___x_849_ = lean_array_push(v___x_847_, v___x_848_);
                    v_init_841_ = v___x_849_;
                    v_x_842_ = v_r_846_;
                    state = 0;
                    continue;
                } else {
                    return v_init_841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_853_: *mut LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_851_, v_x_852_);
    lean_dec(v_x_852_);
    return v_res_853_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(
    mut v_env_854_: *mut LeanObject,
    mut v_as_855_: *mut LeanObject,
    mut v_i_856_: usize,
    mut v_stop_857_: usize,
    mut v_b_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: usize = 0;
    let mut v___x_862_: usize = 0;
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_864_ = lean_usize_dec_eq(v_i_856_, v_stop_857_);
                if v___x_864_ == 0 {
                    v___x_865_ = lean_array_uget_borrowed(v_as_855_, v_i_856_);
                    v_fst_866_ = lean_ctor_get(v___x_865_, 0);
                    lean_inc(v_fst_866_);
                    lean_inc_ref(v_env_854_);
                    v___x_867_ = l_Lean_Environment_contains(v_env_854_, v_fst_866_, v___x_864_);
                    if v___x_867_ == 0 {
                        v___y_860_ = v_b_858_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_865_);
                        v___x_868_ = lean_array_push(v_b_858_, v___x_865_);
                        v___y_860_ = v___x_868_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_854_);
                    return v_b_858_;
                }
            }
            1 => {
                v___x_861_ = 1usize;
                v___x_862_ = lean_usize_add(v_i_856_, v___x_861_);
                v_i_856_ = v___x_862_;
                v_b_858_ = v___y_860_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_869_: *mut LeanObject,
    mut v_as_870_: *mut LeanObject,
    mut v_i_871_: *mut LeanObject,
    mut v_stop_872_: *mut LeanObject,
    mut v_b_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_874_: usize = 0;
    let mut v_stop_boxed_875_: usize = 0;
    let mut v_res_876_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_874_ = lean_unbox_usize(v_i_871_);
    lean_dec(v_i_871_);
    v_stop_boxed_875_ = lean_unbox_usize(v_stop_872_);
    lean_dec(v_stop_872_);
    v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_869_, v_as_870_, v_i_boxed_874_, v_stop_boxed_875_, v_b_873_);
    lean_dec_ref(v_as_870_);
    return v_res_876_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
    mut v_env_883_: *mut LeanObject,
    mut v_s_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    v___x_885_ = lean_unsigned_to_nat(0);
    v___x_886_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_887_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v___x_886_, v_s_884_);
    v___x_888_ = lean_array_get_size(v___x_887_);
    v___x_889_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_890_ = lean_nat_dec_lt(v___x_885_, v___x_888_);
    if v___x_890_ == 0 {
        let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_887_);
        lean_dec_ref(v_env_883_);
        v___x_891_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
        return v___x_891_;
    } else {
        let mut v___x_892_: u8 = 0;
        v___x_892_ = lean_nat_dec_le(v___x_888_, v___x_888_);
        if v___x_892_ == 0 {
            if v___x_890_ == 0 {
                let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_887_);
                lean_dec_ref(v_env_883_);
                v___x_893_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
                return v___x_893_;
            } else {
                let mut v___x_894_: usize = 0;
                let mut v___x_895_: usize = 0;
                let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
                v___x_894_ = 0usize;
                v___x_895_ = lean_usize_of_nat(v___x_888_);
                v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_883_, v___x_887_, v___x_894_, v___x_895_, v___x_889_);
                lean_dec_ref(v___x_887_);
                lean_inc_ref_n(v___x_896_, 2);
                v___x_897_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_897_, 0, v___x_896_);
                lean_ctor_set(v___x_897_, 1, v___x_896_);
                lean_ctor_set(v___x_897_, 2, v___x_896_);
                return v___x_897_;
            }
        } else {
            let mut v___x_898_: usize = 0;
            let mut v___x_899_: usize = 0;
            let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
            v___x_898_ = 0usize;
            v___x_899_ = lean_usize_of_nat(v___x_888_);
            v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_883_, v___x_887_, v___x_898_, v___x_899_, v___x_889_);
            lean_dec_ref(v___x_887_);
            lean_inc_ref_n(v___x_900_, 2);
            v___x_901_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_901_, 0, v___x_900_);
            lean_ctor_set(v___x_901_, 1, v___x_900_);
            lean_ctor_set(v___x_901_, 2, v___x_900_);
            return v___x_901_;
        }
    }
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(
    mut v_env_902_: *mut LeanObject,
    mut v_s_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(v_env_902_, v_s_903_);
    lean_dec(v_s_903_);
    return v_res_904_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___f_911_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_912_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_;
    v___x_913_ = l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_;
    v___x_914_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_912_, v___x_913_, v___f_911_);
    return v___x_914_;
}
pub unsafe fn l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(
    mut v_a_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v_res_916_ =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
        );
    return v_res_916_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(
    mut v_init_917_: *mut LeanObject,
    mut v_t_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_919_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_917_, v_t_918_);
    return v___x_919_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_920_: *mut LeanObject,
    mut v_t_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_922_: *mut LeanObject = core::ptr::null_mut();
    v_res_922_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(v_init_920_, v_t_921_);
    lean_dec(v_t_921_);
    return v_res_922_;
}
pub unsafe fn l_Lean_addAuxParentProjectionInfo(
    mut v_env_923_: *mut LeanObject,
    mut v_projName_924_: *mut LeanObject,
    mut v_numParams_925_: *mut LeanObject,
    mut v_fromClass_926_: u8,
) -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_auxParentProjInfoExt;
    v___x_928_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_928_, 0, v_numParams_925_);
    lean_ctor_set_uint8(
        v___x_928_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_fromClass_926_,
    );
    v___x_929_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_927_,
        v_env_923_,
        v_projName_924_,
        v___x_928_,
    );
    return v___x_929_;
}
pub unsafe fn l_Lean_addAuxParentProjectionInfo___boxed(
    mut v_env_930_: *mut LeanObject,
    mut v_projName_931_: *mut LeanObject,
    mut v_numParams_932_: *mut LeanObject,
    mut v_fromClass_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fromClass_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v_fromClass_boxed_934_ = (lean_unbox(v_fromClass_933_) as u8);
    v_res_935_ = l_Lean_addAuxParentProjectionInfo(
        v_env_930_,
        v_projName_931_,
        v_numParams_932_,
        v_fromClass_boxed_934_,
    );
    return v_res_935_;
}
pub unsafe fn l_Lean_Environment_getAuxParentProjectionInfo_x3f(
    mut v_env_936_: *mut LeanObject,
    mut v_projName_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ = l_Lean_auxParentProjInfoExt;
    v_toEnvExtension_939_ = lean_ctor_get(v___x_938_, 0);
    v_asyncMode_940_ = lean_ctor_get(v_toEnvExtension_939_, 2);
    v___x_941_ = l_Lean_instInhabitedAuxParentProjectionInfo_default;
    v___x_942_ = 0;
    v___x_943_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_941_,
        v___x_938_,
        v_env_936_,
        v_projName_937_,
        v_asyncMode_940_,
        v___x_942_,
    );
    return v___x_943_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(
    mut v_declName_944_: *mut LeanObject,
    mut v_toPure_945_: *mut LeanObject,
    mut v_____do__lift_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ =
        l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_946_, v_declName_944_);
    v___x_948_ = lean_apply_2(v_toPure_945_, lean_box(0), v___x_947_);
    return v___x_948_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f___redArg(
    mut v_inst_949_: *mut LeanObject,
    mut v_inst_950_: *mut LeanObject,
    mut v_declName_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_952_ = lean_ctor_get(v_inst_950_, 0);
    lean_inc_ref(v_toApplicative_952_);
    v_toBind_953_ = lean_ctor_get(v_inst_950_, 1);
    lean_inc(v_toBind_953_);
    lean_dec_ref(v_inst_950_);
    v_getEnv_954_ = lean_ctor_get(v_inst_949_, 0);
    lean_inc(v_getEnv_954_);
    lean_dec_ref(v_inst_949_);
    v_toPure_955_ = lean_ctor_get(v_toApplicative_952_, 1);
    lean_inc(v_toPure_955_);
    lean_dec_ref(v_toApplicative_952_);
    v___f_956_ = lean_alloc_closure(
        l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_956_, 0, v_declName_951_);
    lean_closure_set(v___f_956_, 1, v_toPure_955_);
    v___x_957_ = lean_apply_4(
        v_toBind_953_,
        lean_box(0),
        lean_box(0),
        v_getEnv_954_,
        v___f_956_,
    );
    return v___x_957_;
}
pub unsafe fn l_Lean_getAuxParentProjectionInfo_x3f(
    mut v_m_958_: *mut LeanObject,
    mut v_inst_959_: *mut LeanObject,
    mut v_inst_960_: *mut LeanObject,
    mut v_declName_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    v___x_962_ =
        l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_959_, v_inst_960_, v_declName_961_);
    return v___x_962_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ProjFns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(
        );
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_projectionFnInfoExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_projectionFnInfoExt);
    lean_dec_ref(res);
    res =
        l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(
        );
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_auxParentProjInfoExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_auxParentProjInfoExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ProjFns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ProjFns(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ProjFns(builtin);
}
