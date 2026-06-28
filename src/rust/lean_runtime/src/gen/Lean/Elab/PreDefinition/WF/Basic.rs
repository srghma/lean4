// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Basic
// Imports: Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_evalTactic,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [114, 97, 119, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 66, 121, 71, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,16213016488940853032 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,17075027055874776185 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<242> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 242, m_capacity: 242, m_length: 241, m_data: [83, 104, 111, 119, 115, 32, 116, 104, 101, 32, 114, 97, 119, 32, 96, 100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 98, 121, 96, 32, 103, 111, 97, 108, 32, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 100, 101, 116, 97, 105, 108, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 99, 108, 101, 97, 110, 105, 110, 103, 32, 105, 116, 32, 117, 112, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 96, 99, 108, 101, 97, 110, 95, 119, 102, 96, 32, 116, 97, 99, 116, 105, 99, 46, 32, 67, 97, 110, 32, 98, 101, 32, 101, 110, 97, 98, 108, 101, 100, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 112, 117, 114, 112, 111, 115, 101, 115, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 97, 110, 32, 105, 115, 115, 117, 101, 32, 105, 102, 32, 121, 111, 117, 32, 104, 97, 118, 101, 32, 116, 111, 32, 117, 115, 101, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 32, 102, 111, 114, 32, 111, 116, 104, 101, 114, 32, 114, 101, 97, 115, 111, 110, 115, 46, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 70, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,15475474165463193880 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,14743055034776225543 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,14892011465466138370 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__2_value: LeanStringObject<9> =
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
        m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__2_value)
                as *mut LeanObject,
            14131640301685195369 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__5_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__5_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__7_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__7_value) as *mut LeanObject;
static l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__7_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__9_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__9_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__11_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            116, 97, 99, 116, 105, 99, 67, 108, 101, 97, 110, 95, 119, 102, 0,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__11_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__11_value)
                as *mut LeanObject,
            11462525315186813201 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__12_value) as *mut LeanObject;
pub static l_Lean_Elab_WF_applyCleanWfTactic___closed__13_value: LeanStringObject<9> =
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
        m_data: [99, 108, 101, 97, 110, 95, 119, 102, 0],
    };
static mut l_Lean_Elab_WF_applyCleanWfTactic___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_WF_applyCleanWfTactic___closed__13_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__spec__0(
    mut v_name_144_: *mut LeanObject,
    mut v_decl_145_: *mut LeanObject,
    mut v_ref_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: u8 = 0;
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_157_: u8 = 0;
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut v_unused_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_167_: u8 = 0;
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_148_ = lean_ctor_get(v_decl_145_, 0);
                v_descr_149_ = lean_ctor_get(v_decl_145_, 1);
                v_deprecation_x3f_150_ = lean_ctor_get(v_decl_145_, 2);
                v___x_151_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_152_ = (lean_unbox(v_defValue_148_) as u8);
                lean_ctor_set_uint8(v___x_151_, 0 as u32, v___x_152_);
                lean_inc(v_deprecation_x3f_150_);
                lean_inc_ref(v_descr_149_);
                lean_inc_n(v_name_144_, 2);
                v___x_153_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_153_, 0, v_name_144_);
                lean_ctor_set(v___x_153_, 1, v_ref_146_);
                lean_ctor_set(v___x_153_, 2, v___x_151_);
                lean_ctor_set(v___x_153_, 3, v_descr_149_);
                lean_ctor_set(v___x_153_, 4, v_deprecation_x3f_150_);
                v___x_154_ = lean_register_option(v_name_144_, v___x_153_);
                if lean_obj_tag(v___x_154_) == 0 {
                    v_isSharedCheck_162_ = (!lean_is_exclusive(v___x_154_)) as u8;
                    if v_isSharedCheck_162_ == 0 {
                        v_unused_163_ = lean_ctor_get(v___x_154_, 0);
                        lean_dec(v_unused_163_);
                        v___x_156_ = v___x_154_;
                        v_isShared_157_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_154_);
                        v___x_156_ = lean_box(0);
                        v_isShared_157_ = v_isSharedCheck_162_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_144_);
                    v_a_164_ = lean_ctor_get(v___x_154_, 0);
                    v_isSharedCheck_171_ = (!lean_is_exclusive(v___x_154_)) as u8;
                    if v_isSharedCheck_171_ == 0 {
                        v___x_166_ = v___x_154_;
                        v_isShared_167_ = v_isSharedCheck_171_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_164_);
                        lean_dec(v___x_154_);
                        v___x_166_ = lean_box(0);
                        v_isShared_167_ = v_isSharedCheck_171_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_148_);
                v___x_158_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_158_, 0, v_name_144_);
                lean_ctor_set(v___x_158_, 1, v_defValue_148_);
                if v_isShared_157_ == 0 {
                    lean_ctor_set(v___x_156_, 0, v___x_158_);
                    v___x_160_ = v___x_156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
                    v___x_160_ = v_reuseFailAlloc_161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_160_;
            }
            3 => {
                if v_isShared_167_ == 0 {
                    v___x_169_ = v___x_166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
                    v___x_169_ = v_reuseFailAlloc_170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_172_: *mut LeanObject,
    mut v_decl_173_: *mut LeanObject,
    mut v_ref_174_: *mut LeanObject,
    mut v_a_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_176_: *mut LeanObject = core::ptr::null_mut();
    v_res_176_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__spec__0(v_name_172_, v_decl_173_, v_ref_174_);
    lean_dec_ref(v_decl_173_);
    return v_res_176_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    v___x_198_ = l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_;
    v___x_199_ = l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_;
    v___x_200_ = l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_;
    v___x_201_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4__spec__0(v___x_198_, v___x_199_, v___x_200_);
    return v___x_201_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4____boxed(
    mut v_a_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_203_: *mut LeanObject = core::ptr::null_mut();
    v_res_203_ = l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_();
    return v_res_203_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_WF_applyCleanWfTactic_spec__0(
    mut v_opts_204_: *mut LeanObject,
    mut v_opt_205_: *mut LeanObject,
) -> u8 {
    let mut v_name_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    v_name_206_ = lean_ctor_get(v_opt_205_, 0);
    v_defValue_207_ = lean_ctor_get(v_opt_205_, 1);
    v_map_208_ = lean_ctor_get(v_opts_204_, 0);
    v___x_209_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_208_,
            v_name_206_,
        );
    if lean_obj_tag(v___x_209_) == 0 {
        let mut v___x_210_: u8 = 0;
        v___x_210_ = (lean_unbox(v_defValue_207_) as u8);
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut LeanObject = core::ptr::null_mut();
        v_val_211_ = lean_ctor_get(v___x_209_, 0);
        lean_inc(v_val_211_);
        lean_dec_ref_known(v___x_209_, 1);
        if lean_obj_tag(v_val_211_) == 1 {
            let mut v_v_212_: u8 = 0;
            v_v_212_ = lean_ctor_get_uint8(v_val_211_, 0 as u32);
            lean_dec_ref_known(v_val_211_, 0);
            return v_v_212_;
        } else {
            let mut v___x_213_: u8 = 0;
            lean_dec(v_val_211_);
            v___x_213_ = (lean_unbox(v_defValue_207_) as u8);
            return v___x_213_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_WF_applyCleanWfTactic_spec__0___boxed(
    mut v_opts_214_: *mut LeanObject,
    mut v_opt_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: u8 = 0;
    let mut v_r_217_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ =
        l_Lean_Option_get___at___00Lean_Elab_WF_applyCleanWfTactic_spec__0(v_opts_214_, v_opt_215_);
    lean_dec_ref(v_opt_215_);
    lean_dec_ref(v_opts_214_);
    v_r_217_ = lean_box((v_res_216_) as usize);
    return v_r_217_;
}
pub unsafe fn l_Lean_Elab_WF_applyCleanWfTactic(
    mut v_a_246_: *mut LeanObject,
    mut v_a_247_: *mut LeanObject,
    mut v_a_248_: *mut LeanObject,
    mut v_a_249_: *mut LeanObject,
    mut v_a_250_: *mut LeanObject,
    mut v_a_251_: *mut LeanObject,
    mut v_a_252_: *mut LeanObject,
    mut v_a_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: u8 = 0;
    v_options_255_ = lean_ctor_get(v_a_252_, 2);
    v_ref_256_ = lean_ctor_get(v_a_252_, 5);
    v___x_257_ = l_Lean_Elab_WF_debug_rawDecreasingByGoal;
    v___x_258_ = l_Lean_Option_get___at___00Lean_Elab_WF_applyCleanWfTactic_spec__0(
        v_options_255_,
        v___x_257_,
    );
    if v___x_258_ == 0 {
        let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
        v___x_259_ = l_Lean_SourceInfo_fromRef(v_ref_256_, v___x_258_);
        v___x_260_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__3;
        v___x_261_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__4;
        lean_inc_n(v___x_259_, 6);
        v___x_262_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_262_, 0, v___x_259_);
        lean_ctor_set(v___x_262_, 1, v___x_261_);
        v___x_263_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__6;
        v___x_264_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__8;
        v___x_265_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__10;
        v___x_266_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__12;
        v___x_267_ = l_Lean_Elab_WF_applyCleanWfTactic___closed__13;
        v___x_268_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_268_, 0, v___x_259_);
        lean_ctor_set(v___x_268_, 1, v___x_267_);
        v___x_269_ = l_Lean_Syntax_node1(v___x_259_, v___x_266_, v___x_268_);
        v___x_270_ = l_Lean_Syntax_node1(v___x_259_, v___x_265_, v___x_269_);
        v___x_271_ = l_Lean_Syntax_node1(v___x_259_, v___x_264_, v___x_270_);
        v___x_272_ = l_Lean_Syntax_node1(v___x_259_, v___x_263_, v___x_271_);
        v___x_273_ = l_Lean_Syntax_node2(v___x_259_, v___x_260_, v___x_262_, v___x_272_);
        v___x_274_ = l_Lean_Elab_Tactic_evalTactic(
            v___x_273_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_,
            v_a_253_,
        );
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        v___x_275_ = lean_box(0);
        v___x_276_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_276_, 0, v___x_275_);
        return v___x_276_;
    }
}
pub unsafe fn l_Lean_Elab_WF_applyCleanWfTactic___boxed(
    mut v_a_277_: *mut LeanObject,
    mut v_a_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
    mut v_a_283_: *mut LeanObject,
    mut v_a_284_: *mut LeanObject,
    mut v_a_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_286_: *mut LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Lean_Elab_WF_applyCleanWfTactic(
        v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_,
    );
    lean_dec(v_a_284_);
    lean_dec_ref(v_a_283_);
    lean_dec(v_a_282_);
    lean_dec_ref(v_a_281_);
    lean_dec(v_a_280_);
    lean_dec_ref(v_a_279_);
    lean_dec(v_a_278_);
    lean_dec_ref(v_a_277_);
    return v_res_286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_WF_Basic_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Basic_753368024____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_WF_debug_rawDecreasingByGoal = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_WF_debug_rawDecreasingByGoal);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_Basic(builtin);
}
