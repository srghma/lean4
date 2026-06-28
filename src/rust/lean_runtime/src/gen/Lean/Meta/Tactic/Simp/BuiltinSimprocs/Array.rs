// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Array
// Imports: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkDefault, l_Lean_Meta_mkNone, l_Lean_Meta_mkSome,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getArrayLit_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Nat::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_addSEvalprocBuiltinAttr, l_Lean_Meta_Simp_addSimprocBuiltinAttr,
    l_Lean_Meta_Simp_registerBuiltinDSimproc,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag,
};
pub static l_Array_reduceGetElem___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Array_reduceGetElem___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_reduceGetElem___redArg___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [71, 101, 116, 69, 108, 101, 109, 0],
    };
static mut l_Array_reduceGetElem___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_reduceGetElem___redArg___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [103, 101, 116, 69, 108, 101, 109, 0],
    };
static mut l_Array_reduceGetElem___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__2_value) as *mut LeanObject;
static l_Array_reduceGetElem___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__1_value) as *mut LeanObject,
        854136310249810287 as *mut LeanObject,
    ],
};
pub static l_Array_reduceGetElem___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__2_value) as *mut LeanObject,
        8801718159307809986 as *mut LeanObject,
    ],
};
static mut l_Array_reduceGetElem___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,5265673996413937317 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Array_reduceGetElem___redArg___closed__3_value) as *mut LeanObject,((( 8 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__7_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value: LeanArrayObject<10> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*10) as u16, other: 0, tag: 246 }, m_size: 10, m_capacity: 10, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_reduceGetElem_x3f___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [71, 101, 116, 69, 108, 101, 109, 63, 0],
    };
static mut l_Array_reduceGetElem_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_reduceGetElem_x3f___redArg___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 101, 116, 69, 108, 101, 109, 63, 0],
    };
static mut l_Array_reduceGetElem_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__1_value) as *mut LeanObject;
static l_Array_reduceGetElem_x3f___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__0_value)
                as *mut LeanObject,
            1284173141442213452 as *mut LeanObject,
        ],
    };
pub static l_Array_reduceGetElem_x3f___redArg___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__1_value)
                as *mut LeanObject,
            14790288273250445109 as *mut LeanObject,
        ],
    };
static mut l_Array_reduceGetElem_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 100, 117, 99, 101, 71, 101, 116, 69, 108, 101, 109, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject,14230894781210111005 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__2_value) as *mut LeanObject,((( 7 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value: LeanArrayObject<9> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*9) as u16, other: 0, tag: 246 }, m_size: 9, m_capacity: 9, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_reduceGetElem_x21___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 101, 116, 69, 108, 101, 109, 33, 0],
    };
static mut l_Array_reduceGetElem_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem_x21___redArg___closed__0_value) as *mut LeanObject;
static l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Array_reduceGetElem_x3f___redArg___closed__0_value)
                as *mut LeanObject,
            1284173141442213452 as *mut LeanObject,
        ],
    };
pub static l_Array_reduceGetElem_x21___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_reduceGetElem_x21___redArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_reduceGetElem_x21___redArg___closed__0_value)
                as *mut LeanObject,
            16409410464876292983 as *mut LeanObject,
        ],
    };
static mut l_Array_reduceGetElem_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_reduceGetElem_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 100, 117, 99, 101, 71, 101, 116, 69, 108, 101, 109, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject,4474540644295654232 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Array_reduceGetElem_x21___redArg___closed__1_value) as *mut LeanObject,((( 8 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value: LeanArrayObject<10> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*10) as u16, other: 0, tag: 246 }, m_size: 10, m_capacity: 10, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__8_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Array_reduceGetElem___redArg(
    mut v_e_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v_arg_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    let mut v_arg_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: u8 = 0;
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: u8 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v_val_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_609_: u8 = 0;
    let mut v_val_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut v_a_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_isSharedCheck_649_: u8 = 0;
    let mut v_a_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_653_: u8 = 0;
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_568_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_562_, v_a_564_);
                if lean_obj_tag(v___x_568_) == 0 {
                    v_a_569_ = lean_ctor_get(v___x_568_, 0);
                    v_isSharedCheck_649_ = (!lean_is_exclusive(v___x_568_)) as u8;
                    if v_isSharedCheck_649_ == 0 {
                        v___x_571_ = v___x_568_;
                        v_isShared_572_ = v_isSharedCheck_649_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_569_);
                        lean_dec(v___x_568_);
                        v___x_571_ = lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_649_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_650_ = lean_ctor_get(v___x_568_, 0);
                    v_isSharedCheck_657_ = (!lean_is_exclusive(v___x_568_)) as u8;
                    if v_isSharedCheck_657_ == 0 {
                        v___x_652_ = v___x_568_;
                        v_isShared_653_ = v_isSharedCheck_657_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_650_);
                        lean_dec(v___x_568_);
                        v___x_652_ = lean_box(0);
                        v_isShared_653_ = v_isSharedCheck_657_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_578_ = l_Lean_Expr_cleanupAnnotations(v_a_569_);
                v___x_579_ = l_Lean_Expr_isApp(v___x_578_);
                if v___x_579_ == 0 {
                    lean_dec_ref(v___x_578_);
                    state = 2;
                    continue;
                } else {
                    v___x_580_ = l_Lean_Expr_appFnCleanup___redArg(v___x_578_);
                    v___x_581_ = l_Lean_Expr_isApp(v___x_580_);
                    if v___x_581_ == 0 {
                        lean_dec_ref(v___x_580_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_582_ = lean_ctor_get(v___x_580_, 1);
                        lean_inc_ref(v_arg_582_);
                        v___x_583_ = l_Lean_Expr_appFnCleanup___redArg(v___x_580_);
                        v___x_584_ = l_Lean_Expr_isApp(v___x_583_);
                        if v___x_584_ == 0 {
                            lean_dec_ref(v___x_583_);
                            lean_dec_ref(v_arg_582_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_585_ = lean_ctor_get(v___x_583_, 1);
                            lean_inc_ref(v_arg_585_);
                            v___x_586_ = l_Lean_Expr_appFnCleanup___redArg(v___x_583_);
                            v___x_587_ = l_Lean_Expr_isApp(v___x_586_);
                            if v___x_587_ == 0 {
                                lean_dec_ref(v___x_586_);
                                lean_dec_ref(v_arg_585_);
                                lean_dec_ref(v_arg_582_);
                                state = 2;
                                continue;
                            } else {
                                v___x_588_ = l_Lean_Expr_appFnCleanup___redArg(v___x_586_);
                                v___x_589_ = l_Lean_Expr_isApp(v___x_588_);
                                if v___x_589_ == 0 {
                                    lean_dec_ref(v___x_588_);
                                    lean_dec_ref(v_arg_585_);
                                    lean_dec_ref(v_arg_582_);
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_590_ = l_Lean_Expr_appFnCleanup___redArg(v___x_588_);
                                    v___x_591_ = l_Lean_Expr_isApp(v___x_590_);
                                    if v___x_591_ == 0 {
                                        lean_dec_ref(v___x_590_);
                                        lean_dec_ref(v_arg_585_);
                                        lean_dec_ref(v_arg_582_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_592_ = l_Lean_Expr_appFnCleanup___redArg(v___x_590_);
                                        v___x_593_ = l_Lean_Expr_isApp(v___x_592_);
                                        if v___x_593_ == 0 {
                                            lean_dec_ref(v___x_592_);
                                            lean_dec_ref(v_arg_585_);
                                            lean_dec_ref(v_arg_582_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_594_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_592_);
                                            v___x_595_ = l_Lean_Expr_isApp(v___x_594_);
                                            if v___x_595_ == 0 {
                                                lean_dec_ref(v___x_594_);
                                                lean_dec_ref(v_arg_585_);
                                                lean_dec_ref(v_arg_582_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_596_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_594_);
                                                v___x_597_ =
                                                    l_Array_reduceGetElem___redArg___closed__3;
                                                v___x_598_ =
                                                    l_Lean_Expr_isConstOf(v___x_596_, v___x_597_);
                                                lean_dec_ref(v___x_596_);
                                                if v___x_598_ == 0 {
                                                    lean_dec_ref(v_arg_585_);
                                                    lean_dec_ref(v_arg_582_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    lean_del_object(v___x_571_);
                                                    v___x_599_ = l_Lean_Meta_getNatValue_x3f(
                                                        v_arg_582_, v_a_563_, v_a_564_, v_a_565_,
                                                        v_a_566_,
                                                    );
                                                    lean_dec_ref(v_arg_582_);
                                                    if lean_obj_tag(v___x_599_) == 0 {
                                                        v_a_600_ = lean_ctor_get(v___x_599_, 0);
                                                        v_isSharedCheck_640_ =
                                                            (!lean_is_exclusive(v___x_599_)) as u8;
                                                        if v_isSharedCheck_640_ == 0 {
                                                            v___x_602_ = v___x_599_;
                                                            v_isShared_603_ = v_isSharedCheck_640_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_600_);
                                                            lean_dec(v___x_599_);
                                                            v___x_602_ = lean_box(0);
                                                            v_isShared_603_ = v_isSharedCheck_640_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_585_);
                                                        v_a_641_ = lean_ctor_get(v___x_599_, 0);
                                                        v_isSharedCheck_648_ =
                                                            (!lean_is_exclusive(v___x_599_)) as u8;
                                                        if v_isSharedCheck_648_ == 0 {
                                                            v___x_643_ = v___x_599_;
                                                            v_isShared_644_ = v_isSharedCheck_648_;
                                                            state = 13;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_641_);
                                                            lean_dec(v___x_599_);
                                                            v___x_643_ = lean_box(0);
                                                            v_isShared_644_ = v_isSharedCheck_648_;
                                                            state = 13;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_574_ = l_Array_reduceGetElem___redArg___closed__0;
                if v_isShared_572_ == 0 {
                    lean_ctor_set(v___x_571_, 0, v___x_574_);
                    v___x_576_ = v___x_571_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_576_;
            }
            4 => {
                if lean_obj_tag(v_a_600_) == 1 {
                    lean_del_object(v___x_602_);
                    v_val_604_ = lean_ctor_get(v_a_600_, 0);
                    lean_inc(v_val_604_);
                    lean_dec_ref_known(v_a_600_, 1);
                    v___x_605_ = l_Lean_Meta_getArrayLit_x3f(
                        v_arg_585_, v_a_563_, v_a_564_, v_a_565_, v_a_566_,
                    );
                    lean_dec_ref(v_arg_585_);
                    if lean_obj_tag(v___x_605_) == 0 {
                        v_a_606_ = lean_ctor_get(v___x_605_, 0);
                        v_isSharedCheck_627_ = (!lean_is_exclusive(v___x_605_)) as u8;
                        if v_isSharedCheck_627_ == 0 {
                            v___x_608_ = v___x_605_;
                            v_isShared_609_ = v_isSharedCheck_627_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_606_);
                            lean_dec(v___x_605_);
                            v___x_608_ = lean_box(0);
                            v_isShared_609_ = v_isSharedCheck_627_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_604_);
                        v_a_628_ = lean_ctor_get(v___x_605_, 0);
                        v_isSharedCheck_635_ = (!lean_is_exclusive(v___x_605_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_605_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_628_);
                            lean_dec(v___x_605_);
                            v___x_630_ = lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_600_);
                    lean_dec_ref(v_arg_585_);
                    v___x_636_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_603_ == 0 {
                        lean_ctor_set(v___x_602_, 0, v___x_636_);
                        v___x_638_ = v___x_602_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
                        v___x_638_ = v_reuseFailAlloc_639_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_606_) == 1 {
                    v_val_610_ = lean_ctor_get(v_a_606_, 0);
                    v_isSharedCheck_622_ = (!lean_is_exclusive(v_a_606_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_612_ = v_a_606_;
                        v_isShared_613_ = v_isSharedCheck_622_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_610_);
                        lean_dec(v_a_606_);
                        v___x_612_ = lean_box(0);
                        v_isShared_613_ = v_isSharedCheck_622_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_606_);
                    lean_dec(v_val_604_);
                    v___x_623_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_609_ == 0 {
                        lean_ctor_set(v___x_608_, 0, v___x_623_);
                        v___x_625_ = v___x_608_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
                        v___x_625_ = v_reuseFailAlloc_626_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_614_ = l_Lean_instInhabitedExpr;
                v___x_615_ = lean_array_get(v___x_614_, v_val_610_, v_val_604_);
                lean_dec(v_val_604_);
                lean_dec(v_val_610_);
                if v_isShared_613_ == 0 {
                    lean_ctor_set_tag(v___x_612_, 0);
                    lean_ctor_set(v___x_612_, 0, v___x_615_);
                    v___x_617_ = v___x_612_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_615_);
                    v___x_617_ = v_reuseFailAlloc_621_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_609_ == 0 {
                    lean_ctor_set(v___x_608_, 0, v___x_617_);
                    v___x_619_ = v___x_608_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
                    v___x_619_ = v_reuseFailAlloc_620_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_619_;
            }
            9 => {
                return v___x_625_;
            }
            10 => {
                if v_isShared_631_ == 0 {
                    v___x_633_ = v___x_630_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
                    v___x_633_ = v_reuseFailAlloc_634_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_633_;
            }
            12 => {
                return v___x_638_;
            }
            13 => {
                if v_isShared_644_ == 0 {
                    v___x_646_ = v___x_643_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
                    v___x_646_ = v_reuseFailAlloc_647_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_646_;
            }
            15 => {
                if v_isShared_653_ == 0 {
                    v___x_655_ = v___x_652_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
                    v___x_655_ = v_reuseFailAlloc_656_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_reduceGetElem___redArg___boxed(
    mut v_e_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
    mut v_a_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_664_: *mut LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Array_reduceGetElem___redArg(v_e_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
    lean_dec(v_a_662_);
    lean_dec_ref(v_a_661_);
    lean_dec(v_a_660_);
    lean_dec_ref(v_a_659_);
    return v_res_664_;
}
pub unsafe fn l_Array_reduceGetElem(
    mut v_e_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
    mut v_a_667_: *mut LeanObject,
    mut v_a_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    v___x_674_ = l_Array_reduceGetElem___redArg(v_e_665_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
    return v___x_674_;
}
pub unsafe fn l_Array_reduceGetElem___boxed(
    mut v_e_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
    mut v_a_680_: *mut LeanObject,
    mut v_a_681_: *mut LeanObject,
    mut v_a_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Array_reduceGetElem(
        v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_,
    );
    lean_dec(v_a_682_);
    lean_dec_ref(v_a_681_);
    lean_dec(v_a_680_);
    lean_dec_ref(v_a_679_);
    lean_dec(v_a_678_);
    lean_dec_ref(v_a_677_);
    lean_dec(v_a_676_);
    return v_res_684_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_;
    v___x_722_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_;
    v___x_723_ = lean_alloc_closure(
        l_Array_reduceGetElem___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_724_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_721_, v___x_722_, v___x_723_);
    return v___x_724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22____boxed(
    mut v_a_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_726_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_();
    return v_res_726_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = lean_alloc_closure(
        l_Array_reduceGetElem___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_728_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_728_, 0, v___x_727_);
    return v___x_728_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: u8 = 0;
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    v___x_730_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_;
    v___x_731_ = 1;
    v___x_732_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_);
    v___x_733_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_730_, v___x_731_, v___x_732_);
    return v___x_733_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24____boxed(
    mut v_a_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_735_: *mut LeanObject = core::ptr::null_mut();
    v_res_735_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_();
    return v_res_735_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_()
-> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_;
    v___x_738_ = 1;
    v___x_739_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_);
    v___x_740_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_737_, v___x_738_, v___x_739_);
    return v___x_740_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26____boxed(
    mut v_a_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_742_: *mut LeanObject = core::ptr::null_mut();
    v_res_742_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_();
    return v_res_742_;
}
pub unsafe fn l_Array_reduceGetElem_x3f___redArg(
    mut v_e_748_: *mut LeanObject,
    mut v_a_749_: *mut LeanObject,
    mut v_a_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u8 = 0;
    let mut v_arg_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    let mut v_arg_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v_arg_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_792_: u8 = 0;
    let mut v_val_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_val_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_807_: u8 = 0;
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_811_: u8 = 0;
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_818_: u8 = 0;
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_822_: u8 = 0;
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut v_a_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_835_: u8 = 0;
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut v_a_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_844_: u8 = 0;
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut v_isSharedCheck_849_: u8 = 0;
    let mut v_a_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_758_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_748_, v_a_750_);
                if lean_obj_tag(v___x_758_) == 0 {
                    v_a_759_ = lean_ctor_get(v___x_758_, 0);
                    v_isSharedCheck_849_ = (!lean_is_exclusive(v___x_758_)) as u8;
                    if v_isSharedCheck_849_ == 0 {
                        v___x_761_ = v___x_758_;
                        v_isShared_762_ = v_isSharedCheck_849_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_759_);
                        lean_dec(v___x_758_);
                        v___x_761_ = lean_box(0);
                        v_isShared_762_ = v_isSharedCheck_849_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_850_ = lean_ctor_get(v___x_758_, 0);
                    v_isSharedCheck_857_ = (!lean_is_exclusive(v___x_758_)) as u8;
                    if v_isSharedCheck_857_ == 0 {
                        v___x_852_ = v___x_758_;
                        v_isShared_853_ = v_isSharedCheck_857_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_850_);
                        lean_dec(v___x_758_);
                        v___x_852_ = lean_box(0);
                        v_isShared_853_ = v_isSharedCheck_857_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_756_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_756_, 0, v_r_755_);
                v___x_757_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_757_, 0, v___x_756_);
                return v___x_757_;
            }
            2 => {
                v___x_768_ = l_Lean_Expr_cleanupAnnotations(v_a_759_);
                v___x_769_ = l_Lean_Expr_isApp(v___x_768_);
                if v___x_769_ == 0 {
                    lean_dec_ref(v___x_768_);
                    state = 3;
                    continue;
                } else {
                    v_arg_770_ = lean_ctor_get(v___x_768_, 1);
                    lean_inc_ref(v_arg_770_);
                    v___x_771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_768_);
                    v___x_772_ = l_Lean_Expr_isApp(v___x_771_);
                    if v___x_772_ == 0 {
                        lean_dec_ref(v___x_771_);
                        lean_dec_ref(v_arg_770_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_773_ = lean_ctor_get(v___x_771_, 1);
                        lean_inc_ref(v_arg_773_);
                        v___x_774_ = l_Lean_Expr_appFnCleanup___redArg(v___x_771_);
                        v___x_775_ = l_Lean_Expr_isApp(v___x_774_);
                        if v___x_775_ == 0 {
                            lean_dec_ref(v___x_774_);
                            lean_dec_ref(v_arg_773_);
                            lean_dec_ref(v_arg_770_);
                            state = 3;
                            continue;
                        } else {
                            v___x_776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_774_);
                            v___x_777_ = l_Lean_Expr_isApp(v___x_776_);
                            if v___x_777_ == 0 {
                                lean_dec_ref(v___x_776_);
                                lean_dec_ref(v_arg_773_);
                                lean_dec_ref(v_arg_770_);
                                state = 3;
                                continue;
                            } else {
                                v___x_778_ = l_Lean_Expr_appFnCleanup___redArg(v___x_776_);
                                v___x_779_ = l_Lean_Expr_isApp(v___x_778_);
                                if v___x_779_ == 0 {
                                    lean_dec_ref(v___x_778_);
                                    lean_dec_ref(v_arg_773_);
                                    lean_dec_ref(v_arg_770_);
                                    state = 3;
                                    continue;
                                } else {
                                    v_arg_780_ = lean_ctor_get(v___x_778_, 1);
                                    lean_inc_ref(v_arg_780_);
                                    v___x_781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_778_);
                                    v___x_782_ = l_Lean_Expr_isApp(v___x_781_);
                                    if v___x_782_ == 0 {
                                        lean_dec_ref(v___x_781_);
                                        lean_dec_ref(v_arg_780_);
                                        lean_dec_ref(v_arg_773_);
                                        lean_dec_ref(v_arg_770_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_781_);
                                        v___x_784_ = l_Lean_Expr_isApp(v___x_783_);
                                        if v___x_784_ == 0 {
                                            lean_dec_ref(v___x_783_);
                                            lean_dec_ref(v_arg_780_);
                                            lean_dec_ref(v_arg_773_);
                                            lean_dec_ref(v_arg_770_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_785_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_783_);
                                            v___x_786_ =
                                                l_Array_reduceGetElem_x3f___redArg___closed__2;
                                            v___x_787_ =
                                                l_Lean_Expr_isConstOf(v___x_785_, v___x_786_);
                                            lean_dec_ref(v___x_785_);
                                            if v___x_787_ == 0 {
                                                lean_dec_ref(v_arg_780_);
                                                lean_dec_ref(v_arg_773_);
                                                lean_dec_ref(v_arg_770_);
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_del_object(v___x_761_);
                                                v___x_788_ = l_Lean_Meta_getNatValue_x3f(
                                                    v_arg_770_, v_a_749_, v_a_750_, v_a_751_,
                                                    v_a_752_,
                                                );
                                                lean_dec_ref(v_arg_770_);
                                                if lean_obj_tag(v___x_788_) == 0 {
                                                    v_a_789_ = lean_ctor_get(v___x_788_, 0);
                                                    v_isSharedCheck_840_ =
                                                        (!lean_is_exclusive(v___x_788_)) as u8;
                                                    if v_isSharedCheck_840_ == 0 {
                                                        v___x_791_ = v___x_788_;
                                                        v_isShared_792_ = v_isSharedCheck_840_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_789_);
                                                        lean_dec(v___x_788_);
                                                        v___x_791_ = lean_box(0);
                                                        v_isShared_792_ = v_isSharedCheck_840_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_780_);
                                                    lean_dec_ref(v_arg_773_);
                                                    v_a_841_ = lean_ctor_get(v___x_788_, 0);
                                                    v_isSharedCheck_848_ =
                                                        (!lean_is_exclusive(v___x_788_)) as u8;
                                                    if v_isSharedCheck_848_ == 0 {
                                                        v___x_843_ = v___x_788_;
                                                        v_isShared_844_ = v_isSharedCheck_848_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_841_);
                                                        lean_dec(v___x_788_);
                                                        v___x_843_ = lean_box(0);
                                                        v_isShared_844_ = v_isSharedCheck_848_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_764_ = l_Array_reduceGetElem___redArg___closed__0;
                if v_isShared_762_ == 0 {
                    lean_ctor_set(v___x_761_, 0, v___x_764_);
                    v___x_766_ = v___x_761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
                    v___x_766_ = v_reuseFailAlloc_767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_766_;
            }
            5 => {
                if lean_obj_tag(v_a_789_) == 1 {
                    lean_del_object(v___x_791_);
                    v_val_793_ = lean_ctor_get(v_a_789_, 0);
                    lean_inc(v_val_793_);
                    lean_dec_ref_known(v_a_789_, 1);
                    v___x_794_ = l_Lean_Meta_getArrayLit_x3f(
                        v_arg_773_, v_a_749_, v_a_750_, v_a_751_, v_a_752_,
                    );
                    lean_dec_ref(v_arg_773_);
                    if lean_obj_tag(v___x_794_) == 0 {
                        v_a_795_ = lean_ctor_get(v___x_794_, 0);
                        v_isSharedCheck_827_ = (!lean_is_exclusive(v___x_794_)) as u8;
                        if v_isSharedCheck_827_ == 0 {
                            v___x_797_ = v___x_794_;
                            v_isShared_798_ = v_isSharedCheck_827_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_795_);
                            lean_dec(v___x_794_);
                            v___x_797_ = lean_box(0);
                            v_isShared_798_ = v_isSharedCheck_827_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_793_);
                        lean_dec_ref(v_arg_780_);
                        v_a_828_ = lean_ctor_get(v___x_794_, 0);
                        v_isSharedCheck_835_ = (!lean_is_exclusive(v___x_794_)) as u8;
                        if v_isSharedCheck_835_ == 0 {
                            v___x_830_ = v___x_794_;
                            v_isShared_831_ = v_isSharedCheck_835_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_828_);
                            lean_dec(v___x_794_);
                            v___x_830_ = lean_box(0);
                            v_isShared_831_ = v_isSharedCheck_835_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_789_);
                    lean_dec_ref(v_arg_780_);
                    lean_dec_ref(v_arg_773_);
                    v___x_836_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_792_ == 0 {
                        lean_ctor_set(v___x_791_, 0, v___x_836_);
                        v___x_838_ = v___x_791_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
                        v___x_838_ = v_reuseFailAlloc_839_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_795_) == 1 {
                    lean_del_object(v___x_797_);
                    v_val_799_ = lean_ctor_get(v_a_795_, 0);
                    lean_inc(v_val_799_);
                    lean_dec_ref_known(v_a_795_, 1);
                    v___x_800_ = lean_array_get_size(v_val_799_);
                    v___x_801_ = lean_nat_dec_lt(v_val_793_, v___x_800_);
                    if v___x_801_ == 0 {
                        lean_dec(v_val_799_);
                        lean_dec(v_val_793_);
                        v___x_802_ =
                            l_Lean_Meta_mkNone(v_arg_780_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
                        if lean_obj_tag(v___x_802_) == 0 {
                            v_a_803_ = lean_ctor_get(v___x_802_, 0);
                            lean_inc(v_a_803_);
                            lean_dec_ref_known(v___x_802_, 1);
                            v_r_755_ = v_a_803_;
                            state = 1;
                            continue;
                        } else {
                            v_a_804_ = lean_ctor_get(v___x_802_, 0);
                            v_isSharedCheck_811_ = (!lean_is_exclusive(v___x_802_)) as u8;
                            if v_isSharedCheck_811_ == 0 {
                                v___x_806_ = v___x_802_;
                                v_isShared_807_ = v_isSharedCheck_811_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_804_);
                                lean_dec(v___x_802_);
                                v___x_806_ = lean_box(0);
                                v_isShared_807_ = v_isSharedCheck_811_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v___x_812_ = lean_array_fget(v_val_799_, v_val_793_);
                        lean_dec(v_val_793_);
                        lean_dec(v_val_799_);
                        v___x_813_ = l_Lean_Meta_mkSome(
                            v_arg_780_, v___x_812_, v_a_749_, v_a_750_, v_a_751_, v_a_752_,
                        );
                        if lean_obj_tag(v___x_813_) == 0 {
                            v_a_814_ = lean_ctor_get(v___x_813_, 0);
                            lean_inc(v_a_814_);
                            lean_dec_ref_known(v___x_813_, 1);
                            v_r_755_ = v_a_814_;
                            state = 1;
                            continue;
                        } else {
                            v_a_815_ = lean_ctor_get(v___x_813_, 0);
                            v_isSharedCheck_822_ = (!lean_is_exclusive(v___x_813_)) as u8;
                            if v_isSharedCheck_822_ == 0 {
                                v___x_817_ = v___x_813_;
                                v_isShared_818_ = v_isSharedCheck_822_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_815_);
                                lean_dec(v___x_813_);
                                v___x_817_ = lean_box(0);
                                v_isShared_818_ = v_isSharedCheck_822_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_795_);
                    lean_dec(v_val_793_);
                    lean_dec_ref(v_arg_780_);
                    v___x_823_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_798_ == 0 {
                        lean_ctor_set(v___x_797_, 0, v___x_823_);
                        v___x_825_ = v___x_797_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
                        v___x_825_ = v_reuseFailAlloc_826_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_807_ == 0 {
                    v___x_809_ = v___x_806_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
                    v___x_809_ = v_reuseFailAlloc_810_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_809_;
            }
            9 => {
                if v_isShared_818_ == 0 {
                    v___x_820_ = v___x_817_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
                    v___x_820_ = v_reuseFailAlloc_821_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_820_;
            }
            11 => {
                return v___x_825_;
            }
            12 => {
                if v_isShared_831_ == 0 {
                    v___x_833_ = v___x_830_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
                    v___x_833_ = v_reuseFailAlloc_834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_833_;
            }
            14 => {
                return v___x_838_;
            }
            15 => {
                if v_isShared_844_ == 0 {
                    v___x_846_ = v___x_843_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
                    v___x_846_ = v_reuseFailAlloc_847_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_846_;
            }
            17 => {
                if v_isShared_853_ == 0 {
                    v___x_855_ = v___x_852_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
                    v___x_855_ = v_reuseFailAlloc_856_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_reduceGetElem_x3f___redArg___boxed(
    mut v_e_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_864_: *mut LeanObject = core::ptr::null_mut();
    v_res_864_ =
        l_Array_reduceGetElem_x3f___redArg(v_e_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
    lean_dec(v_a_862_);
    lean_dec_ref(v_a_861_);
    lean_dec(v_a_860_);
    lean_dec_ref(v_a_859_);
    return v_res_864_;
}
pub unsafe fn l_Array_reduceGetElem_x3f(
    mut v_e_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
    mut v_a_867_: *mut LeanObject,
    mut v_a_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
    mut v_a_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ =
        l_Array_reduceGetElem_x3f___redArg(v_e_865_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
    return v___x_874_;
}
pub unsafe fn l_Array_reduceGetElem_x3f___boxed(
    mut v_e_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_884_: *mut LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Array_reduceGetElem_x3f(
        v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_,
    );
    lean_dec(v_a_882_);
    lean_dec_ref(v_a_881_);
    lean_dec(v_a_880_);
    lean_dec_ref(v_a_879_);
    lean_dec(v_a_878_);
    lean_dec_ref(v_a_877_);
    lean_dec(v_a_876_);
    return v_res_884_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_()
-> *mut LeanObject {
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_908_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_;
    v___x_909_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_;
    v___x_910_ = lean_alloc_closure(
        l_Array_reduceGetElem_x3f___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_911_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_908_, v___x_909_, v___x_910_);
    return v___x_911_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21____boxed(
    mut v_a_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_913_: *mut LeanObject = core::ptr::null_mut();
    v_res_913_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_();
    return v_res_913_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_()
-> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_alloc_closure(
        l_Array_reduceGetElem_x3f___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_915_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_915_, 0, v___x_914_);
    return v___x_915_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_()
-> *mut LeanObject {
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_;
    v___x_918_ = 1;
    v___x_919_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_);
    v___x_920_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_917_, v___x_918_, v___x_919_);
    return v___x_920_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23____boxed(
    mut v_a_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_922_: *mut LeanObject = core::ptr::null_mut();
    v_res_922_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_();
    return v_res_922_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_()
-> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_;
    v___x_925_ = 1;
    v___x_926_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_);
    v___x_927_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_924_, v___x_925_, v___x_926_);
    return v___x_927_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25____boxed(
    mut v_a_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_929_: *mut LeanObject = core::ptr::null_mut();
    v_res_929_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_();
    return v_res_929_;
}
pub unsafe fn l_Array_reduceGetElem_x21___redArg(
    mut v_e_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
    mut v_a_938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v_arg_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    let mut v_arg_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: u8 = 0;
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v_arg_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v_val_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v_val_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1005_: u8 = 0;
    let mut v_a_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1009_: u8 = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_a_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1026_: u8 = 0;
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v_a_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_944_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_934_, v_a_936_);
                if lean_obj_tag(v___x_944_) == 0 {
                    v_a_945_ = lean_ctor_get(v___x_944_, 0);
                    v_isSharedCheck_1027_ = (!lean_is_exclusive(v___x_944_)) as u8;
                    if v_isSharedCheck_1027_ == 0 {
                        v___x_947_ = v___x_944_;
                        v_isShared_948_ = v_isSharedCheck_1027_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_945_);
                        lean_dec(v___x_944_);
                        v___x_947_ = lean_box(0);
                        v_isShared_948_ = v_isSharedCheck_1027_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1028_ = lean_ctor_get(v___x_944_, 0);
                    v_isSharedCheck_1035_ = (!lean_is_exclusive(v___x_944_)) as u8;
                    if v_isSharedCheck_1035_ == 0 {
                        v___x_1030_ = v___x_944_;
                        v_isShared_1031_ = v_isSharedCheck_1035_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1028_);
                        lean_dec(v___x_944_);
                        v___x_1030_ = lean_box(0);
                        v_isShared_1031_ = v_isSharedCheck_1035_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_942_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_942_, 0, v_r_941_);
                v___x_943_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_943_, 0, v___x_942_);
                return v___x_943_;
            }
            2 => {
                v___x_954_ = l_Lean_Expr_cleanupAnnotations(v_a_945_);
                v___x_955_ = l_Lean_Expr_isApp(v___x_954_);
                if v___x_955_ == 0 {
                    lean_dec_ref(v___x_954_);
                    state = 3;
                    continue;
                } else {
                    v_arg_956_ = lean_ctor_get(v___x_954_, 1);
                    lean_inc_ref(v_arg_956_);
                    v___x_957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_954_);
                    v___x_958_ = l_Lean_Expr_isApp(v___x_957_);
                    if v___x_958_ == 0 {
                        lean_dec_ref(v___x_957_);
                        lean_dec_ref(v_arg_956_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_959_ = lean_ctor_get(v___x_957_, 1);
                        lean_inc_ref(v_arg_959_);
                        v___x_960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_957_);
                        v___x_961_ = l_Lean_Expr_isApp(v___x_960_);
                        if v___x_961_ == 0 {
                            lean_dec_ref(v___x_960_);
                            lean_dec_ref(v_arg_959_);
                            lean_dec_ref(v_arg_956_);
                            state = 3;
                            continue;
                        } else {
                            v___x_962_ = l_Lean_Expr_appFnCleanup___redArg(v___x_960_);
                            v___x_963_ = l_Lean_Expr_isApp(v___x_962_);
                            if v___x_963_ == 0 {
                                lean_dec_ref(v___x_962_);
                                lean_dec_ref(v_arg_959_);
                                lean_dec_ref(v_arg_956_);
                                state = 3;
                                continue;
                            } else {
                                v___x_964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_962_);
                                v___x_965_ = l_Lean_Expr_isApp(v___x_964_);
                                if v___x_965_ == 0 {
                                    lean_dec_ref(v___x_964_);
                                    lean_dec_ref(v_arg_959_);
                                    lean_dec_ref(v_arg_956_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_966_ = l_Lean_Expr_appFnCleanup___redArg(v___x_964_);
                                    v___x_967_ = l_Lean_Expr_isApp(v___x_966_);
                                    if v___x_967_ == 0 {
                                        lean_dec_ref(v___x_966_);
                                        lean_dec_ref(v_arg_959_);
                                        lean_dec_ref(v_arg_956_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_968_ = lean_ctor_get(v___x_966_, 1);
                                        lean_inc_ref(v_arg_968_);
                                        v___x_969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_966_);
                                        v___x_970_ = l_Lean_Expr_isApp(v___x_969_);
                                        if v___x_970_ == 0 {
                                            lean_dec_ref(v___x_969_);
                                            lean_dec_ref(v_arg_968_);
                                            lean_dec_ref(v_arg_959_);
                                            lean_dec_ref(v_arg_956_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_971_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_969_);
                                            v___x_972_ = l_Lean_Expr_isApp(v___x_971_);
                                            if v___x_972_ == 0 {
                                                lean_dec_ref(v___x_971_);
                                                lean_dec_ref(v_arg_968_);
                                                lean_dec_ref(v_arg_959_);
                                                lean_dec_ref(v_arg_956_);
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_973_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_971_);
                                                v___x_974_ =
                                                    l_Array_reduceGetElem_x21___redArg___closed__1;
                                                v___x_975_ =
                                                    l_Lean_Expr_isConstOf(v___x_973_, v___x_974_);
                                                lean_dec_ref(v___x_973_);
                                                if v___x_975_ == 0 {
                                                    lean_dec_ref(v_arg_968_);
                                                    lean_dec_ref(v_arg_959_);
                                                    lean_dec_ref(v_arg_956_);
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_del_object(v___x_947_);
                                                    v___x_976_ = l_Lean_Meta_getNatValue_x3f(
                                                        v_arg_956_, v_a_935_, v_a_936_, v_a_937_,
                                                        v_a_938_,
                                                    );
                                                    lean_dec_ref(v_arg_956_);
                                                    if lean_obj_tag(v___x_976_) == 0 {
                                                        v_a_977_ = lean_ctor_get(v___x_976_, 0);
                                                        v_isSharedCheck_1018_ =
                                                            (!lean_is_exclusive(v___x_976_)) as u8;
                                                        if v_isSharedCheck_1018_ == 0 {
                                                            v___x_979_ = v___x_976_;
                                                            v_isShared_980_ = v_isSharedCheck_1018_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_977_);
                                                            lean_dec(v___x_976_);
                                                            v___x_979_ = lean_box(0);
                                                            v_isShared_980_ = v_isSharedCheck_1018_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_968_);
                                                        lean_dec_ref(v_arg_959_);
                                                        v_a_1019_ = lean_ctor_get(v___x_976_, 0);
                                                        v_isSharedCheck_1026_ =
                                                            (!lean_is_exclusive(v___x_976_)) as u8;
                                                        if v_isSharedCheck_1026_ == 0 {
                                                            v___x_1021_ = v___x_976_;
                                                            v_isShared_1022_ =
                                                                v_isSharedCheck_1026_;
                                                            state = 13;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_1019_);
                                                            lean_dec(v___x_976_);
                                                            v___x_1021_ = lean_box(0);
                                                            v_isShared_1022_ =
                                                                v_isSharedCheck_1026_;
                                                            state = 13;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_950_ = l_Array_reduceGetElem___redArg___closed__0;
                if v_isShared_948_ == 0 {
                    lean_ctor_set(v___x_947_, 0, v___x_950_);
                    v___x_952_ = v___x_947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_952_;
            }
            5 => {
                if lean_obj_tag(v_a_977_) == 1 {
                    lean_del_object(v___x_979_);
                    v_val_981_ = lean_ctor_get(v_a_977_, 0);
                    lean_inc(v_val_981_);
                    lean_dec_ref_known(v_a_977_, 1);
                    v___x_982_ = l_Lean_Meta_getArrayLit_x3f(
                        v_arg_959_, v_a_935_, v_a_936_, v_a_937_, v_a_938_,
                    );
                    lean_dec_ref(v_arg_959_);
                    if lean_obj_tag(v___x_982_) == 0 {
                        v_a_983_ = lean_ctor_get(v___x_982_, 0);
                        v_isSharedCheck_1005_ = (!lean_is_exclusive(v___x_982_)) as u8;
                        if v_isSharedCheck_1005_ == 0 {
                            v___x_985_ = v___x_982_;
                            v_isShared_986_ = v_isSharedCheck_1005_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_983_);
                            lean_dec(v___x_982_);
                            v___x_985_ = lean_box(0);
                            v_isShared_986_ = v_isSharedCheck_1005_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_981_);
                        lean_dec_ref(v_arg_968_);
                        v_a_1006_ = lean_ctor_get(v___x_982_, 0);
                        v_isSharedCheck_1013_ = (!lean_is_exclusive(v___x_982_)) as u8;
                        if v_isSharedCheck_1013_ == 0 {
                            v___x_1008_ = v___x_982_;
                            v_isShared_1009_ = v_isSharedCheck_1013_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1006_);
                            lean_dec(v___x_982_);
                            v___x_1008_ = lean_box(0);
                            v_isShared_1009_ = v_isSharedCheck_1013_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_977_);
                    lean_dec_ref(v_arg_968_);
                    lean_dec_ref(v_arg_959_);
                    v___x_1014_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_980_ == 0 {
                        lean_ctor_set(v___x_979_, 0, v___x_1014_);
                        v___x_1016_ = v___x_979_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
                        v___x_1016_ = v_reuseFailAlloc_1017_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v_a_983_) == 1 {
                    lean_del_object(v___x_985_);
                    v_val_987_ = lean_ctor_get(v_a_983_, 0);
                    lean_inc(v_val_987_);
                    lean_dec_ref_known(v_a_983_, 1);
                    v___x_988_ = lean_array_get_size(v_val_987_);
                    v___x_989_ = lean_nat_dec_lt(v_val_981_, v___x_988_);
                    if v___x_989_ == 0 {
                        lean_dec(v_val_987_);
                        lean_dec(v_val_981_);
                        v___x_990_ = l_Lean_Meta_mkDefault(
                            v_arg_968_, v_a_935_, v_a_936_, v_a_937_, v_a_938_,
                        );
                        if lean_obj_tag(v___x_990_) == 0 {
                            v_a_991_ = lean_ctor_get(v___x_990_, 0);
                            lean_inc(v_a_991_);
                            lean_dec_ref_known(v___x_990_, 1);
                            v_r_941_ = v_a_991_;
                            state = 1;
                            continue;
                        } else {
                            v_a_992_ = lean_ctor_get(v___x_990_, 0);
                            v_isSharedCheck_999_ = (!lean_is_exclusive(v___x_990_)) as u8;
                            if v_isSharedCheck_999_ == 0 {
                                v___x_994_ = v___x_990_;
                                v_isShared_995_ = v_isSharedCheck_999_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_992_);
                                lean_dec(v___x_990_);
                                v___x_994_ = lean_box(0);
                                v_isShared_995_ = v_isSharedCheck_999_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_968_);
                        v___x_1000_ = lean_array_fget(v_val_987_, v_val_981_);
                        lean_dec(v_val_981_);
                        lean_dec(v_val_987_);
                        v_r_941_ = v___x_1000_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_983_);
                    lean_dec(v_val_981_);
                    lean_dec_ref(v_arg_968_);
                    v___x_1001_ = l_Array_reduceGetElem___redArg___closed__0;
                    if v_isShared_986_ == 0 {
                        lean_ctor_set(v___x_985_, 0, v___x_1001_);
                        v___x_1003_ = v___x_985_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
                        v___x_1003_ = v_reuseFailAlloc_1004_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_995_ == 0 {
                    v___x_997_ = v___x_994_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_997_;
            }
            9 => {
                return v___x_1003_;
            }
            10 => {
                if v_isShared_1009_ == 0 {
                    v___x_1011_ = v___x_1008_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
                    v___x_1011_ = v_reuseFailAlloc_1012_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1011_;
            }
            12 => {
                return v___x_1016_;
            }
            13 => {
                if v_isShared_1022_ == 0 {
                    v___x_1024_ = v___x_1021_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
                    v___x_1024_ = v_reuseFailAlloc_1025_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1024_;
            }
            15 => {
                if v_isShared_1031_ == 0 {
                    v___x_1033_ = v___x_1030_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
                    v___x_1033_ = v_reuseFailAlloc_1034_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_reduceGetElem_x21___redArg___boxed(
    mut v_e_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1042_: *mut LeanObject = core::ptr::null_mut();
    v_res_1042_ =
        l_Array_reduceGetElem_x21___redArg(v_e_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
    lean_dec(v_a_1040_);
    lean_dec_ref(v_a_1039_);
    lean_dec(v_a_1038_);
    lean_dec_ref(v_a_1037_);
    return v_res_1042_;
}
pub unsafe fn l_Array_reduceGetElem_x21(
    mut v_e_1043_: *mut LeanObject,
    mut v_a_1044_: *mut LeanObject,
    mut v_a_1045_: *mut LeanObject,
    mut v_a_1046_: *mut LeanObject,
    mut v_a_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l_Array_reduceGetElem_x21___redArg(v_e_1043_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
    return v___x_1052_;
}
pub unsafe fn l_Array_reduceGetElem_x21___boxed(
    mut v_e_1053_: *mut LeanObject,
    mut v_a_1054_: *mut LeanObject,
    mut v_a_1055_: *mut LeanObject,
    mut v_a_1056_: *mut LeanObject,
    mut v_a_1057_: *mut LeanObject,
    mut v_a_1058_: *mut LeanObject,
    mut v_a_1059_: *mut LeanObject,
    mut v_a_1060_: *mut LeanObject,
    mut v_a_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Array_reduceGetElem_x21(
        v_e_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_,
    );
    lean_dec(v_a_1060_);
    lean_dec_ref(v_a_1059_);
    lean_dec(v_a_1058_);
    lean_dec_ref(v_a_1057_);
    lean_dec(v_a_1056_);
    lean_dec_ref(v_a_1055_);
    lean_dec(v_a_1054_);
    return v_res_1062_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_()
-> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_;
    v___x_1088_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_;
    v___x_1089_ = lean_alloc_closure(
        l_Array_reduceGetElem_x21___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1090_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1087_, v___x_1088_, v___x_1089_);
    return v___x_1090_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21____boxed(
    mut v_a_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1092_: *mut LeanObject = core::ptr::null_mut();
    v_res_1092_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_();
    return v_res_1092_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_()
-> *mut LeanObject {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    v___x_1093_ = lean_alloc_closure(
        l_Array_reduceGetElem_x21___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1094_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1094_, 0, v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_()
-> *mut LeanObject {
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    v___x_1096_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_;
    v___x_1097_ = 1;
    v___x_1098_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_);
    v___x_1099_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1096_, v___x_1097_, v___x_1098_);
    return v___x_1099_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23____boxed(
    mut v_a_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1101_: *mut LeanObject = core::ptr::null_mut();
    v_res_1101_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_();
    return v_res_1101_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_()
-> *mut LeanObject {
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    v___x_1103_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_;
    v___x_1104_ = 1;
    v___x_1105_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_);
    v___x_1106_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1103_, v___x_1104_, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25____boxed(
    mut v_a_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1108_: *mut LeanObject = core::ptr::null_mut();
    v_res_1108_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_();
    return v_res_1108_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_declare__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem___regBuiltin_Array_reduceGetElem_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_561566828____hygCtx___hyg_26_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x3f_declare__11_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_21_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_23_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x3f___regBuiltin_Array_reduceGetElem_x3f_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_1761453663____hygCtx___hyg_25_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0____regBuiltin_Array_reduceGetElem_x21_declare__16_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_21_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_23_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_0__Array_reduceGetElem_x21___regBuiltin_Array_reduceGetElem_x21_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array_3101361598____hygCtx___hyg_25_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
}
