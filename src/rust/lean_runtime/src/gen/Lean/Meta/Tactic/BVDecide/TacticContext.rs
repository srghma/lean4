// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.TacticContext
// Imports: Lean.Meta.Tactic.BVDecide.Attr
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_exeExtension, l_System_FilePath_join, l_System_FilePath_parent,
    l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::l_System_FilePath_pathExists;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_mkAuxName;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::{
    initialize_Lean_Meta_Tactic_BVDecide_Attr, l_Lean_Meta_Tactic_BVDecide_sat_solver,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_panic_fn_borrowed, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_app_path;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 100, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value: LeanStringObject<10> =
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
        m_data: [95, 101, 120, 112, 114, 95, 100, 101, 102, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value)
                as *mut LeanObject,
            16385472900907787029 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value: LeanStringObject<10> =
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
        m_data: [95, 99, 101, 114, 116, 95, 100, 101, 102, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value)
                as *mut LeanObject,
            11425183056726910951 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            95, 114, 101, 102, 108, 101, 99, 116, 105, 111, 110, 95, 100, 101, 102, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value)
                as *mut LeanObject,
            5620442111418141226 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value: LeanStringObject<5> =
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
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value: LeanStringObject<7> =
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
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 97, 116, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value)
                as *mut LeanObject,
            142734480563613395 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value)
                as *mut LeanObject,
            15847151208953044930 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value)
                as *mut LeanObject,
            9704604365865994158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            85, 115, 105, 110, 103, 32, 83, 65, 84, 32, 115, 111, 108, 118, 101, 114, 32, 97, 116,
            32, 39, 0,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(
    mut v_opts_309_: *mut LeanObject,
    mut v_opt_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v_name_311_ = lean_ctor_get(v_opt_310_, 0);
    v_defValue_312_ = lean_ctor_get(v_opt_310_, 1);
    v_map_313_ = lean_ctor_get(v_opts_309_, 0);
    v___x_314_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_313_,
            v_name_311_,
        );
    if lean_obj_tag(v___x_314_) == 0 {
        lean_inc(v_defValue_312_);
        return v_defValue_312_;
    } else {
        let mut v_val_315_: *mut LeanObject = core::ptr::null_mut();
        v_val_315_ = lean_ctor_get(v___x_314_, 0);
        lean_inc(v_val_315_);
        lean_dec_ref_known(v___x_314_, 1);
        if lean_obj_tag(v_val_315_) == 0 {
            let mut v_v_316_: *mut LeanObject = core::ptr::null_mut();
            v_v_316_ = lean_ctor_get(v_val_315_, 0);
            lean_inc_ref(v_v_316_);
            lean_dec_ref_known(v_val_315_, 1);
            return v_v_316_;
        } else {
            lean_dec(v_val_315_);
            lean_inc(v_defValue_312_);
            return v_defValue_312_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0___boxed(
    mut v_opts_317_: *mut LeanObject,
    mut v_opt_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_319_: *mut LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(v_opts_317_, v_opt_318_);
    lean_dec_ref(v_opt_318_);
    lean_dec_ref(v_opts_317_);
    return v_res_319_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(
    mut v_msg_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0;
    v___x_323_ = lean_panic_fn_borrowed(v___x_322_, v_msg_321_);
    return v___x_323_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3;
    v___x_329_ = lean_unsigned_to_nat(14);
    v___x_330_ = lean_unsigned_to_nat(22);
    v___x_331_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2;
    v___x_332_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1;
    v___x_333_ =
        l_mkPanicMessageWithDecl(v___x_332_, v___x_331_, v___x_330_, v___x_329_, v___x_328_);
    return v___x_333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(
    mut v_a_334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_347_: u8 = 0;
    let mut v___y_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: u8 = 0;
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_365_: u8 = 0;
    let mut v_a_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_369_: u8 = 0;
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_336_ = lean_ctor_get(v_a_334_, 2);
                v_ref_337_ = lean_ctor_get(v_a_334_, 5);
                v___x_338_ = l_Lean_Meta_Tactic_BVDecide_sat_solver;
                v___x_339_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(v_options_336_, v___x_338_);
                v___x_340_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0;
                v___x_341_ = lean_string_dec_eq(v___x_339_, v___x_340_);
                if v___x_341_ == 0 {
                    v___x_342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_342_, 0, v___x_339_);
                    return v___x_342_;
                } else {
                    lean_dec_ref(v___x_339_);
                    v___x_343_ = lean_io_app_path();
                    if lean_obj_tag(v___x_343_) == 0 {
                        v_a_344_ = lean_ctor_get(v___x_343_, 0);
                        v_isSharedCheck_365_ = (!lean_is_exclusive(v___x_343_)) as u8;
                        if v_isSharedCheck_365_ == 0 {
                            v___x_346_ = v___x_343_;
                            v_isShared_347_ = v_isSharedCheck_365_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_344_);
                            lean_dec(v___x_343_);
                            v___x_346_ = lean_box(0);
                            v_isShared_347_ = v_isSharedCheck_365_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_366_ = lean_ctor_get(v___x_343_, 0);
                        v_isSharedCheck_377_ = (!lean_is_exclusive(v___x_343_)) as u8;
                        if v_isSharedCheck_377_ == 0 {
                            v___x_368_ = v___x_343_;
                            v_isShared_369_ = v_isSharedCheck_377_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_366_);
                            lean_dec(v___x_343_);
                            v___x_368_ = lean_box(0);
                            v_isShared_369_ = v_isSharedCheck_377_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_361_ = l_System_FilePath_parent(v_a_344_);
                if lean_obj_tag(v___x_361_) == 0 {
                    v___x_362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4);
                    v___x_363_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(v___x_362_);
                    v___y_349_ = v___x_363_;
                    state = 2;
                    continue;
                } else {
                    v_val_364_ = lean_ctor_get(v___x_361_, 0);
                    lean_inc(v_val_364_);
                    lean_dec_ref_known(v___x_361_, 1);
                    v___y_349_ = v_val_364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_350_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0;
                v___x_351_ = l_System_FilePath_join(v___y_349_, v___x_350_);
                v___x_352_ = l_System_FilePath_exeExtension;
                v___x_353_ = l_System_FilePath_withExtension(v___x_351_, v___x_352_);
                v___x_354_ = l_System_FilePath_pathExists(v___x_353_);
                if v___x_354_ == 0 {
                    lean_dec_ref(v___x_353_);
                    if v_isShared_347_ == 0 {
                        lean_ctor_set(v___x_346_, 0, v___x_350_);
                        v___x_356_ = v___x_346_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_350_);
                        v___x_356_ = v_reuseFailAlloc_357_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_347_ == 0 {
                        lean_ctor_set(v___x_346_, 0, v___x_353_);
                        v___x_359_ = v___x_346_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_353_);
                        v___x_359_ = v_reuseFailAlloc_360_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_356_;
            }
            4 => {
                return v___x_359_;
            }
            5 => {
                v___x_370_ = lean_io_error_to_string(v_a_366_);
                v___x_371_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_371_, 0, v___x_370_);
                v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
                lean_inc(v_ref_337_);
                v___x_373_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_373_, 0, v_ref_337_);
                lean_ctor_set(v___x_373_, 1, v___x_372_);
                if v_isShared_369_ == 0 {
                    lean_ctor_set(v___x_368_, 0, v___x_373_);
                    v___x_375_ = v___x_368_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
                    v___x_375_ = v_reuseFailAlloc_376_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___boxed(
    mut v_a_378_: *mut LeanObject,
    mut v_a_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_380_: *mut LeanObject = core::ptr::null_mut();
    v_res_380_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_378_);
    lean_dec_ref(v_a_378_);
    return v_res_380_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(
    mut v_a_381_: *mut LeanObject,
    mut v_a_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_381_);
    return v___x_384_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___boxed(
    mut v_a_385_: *mut LeanObject,
    mut v_a_386_: *mut LeanObject,
    mut v_a_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(v_a_385_, v_a_386_);
    lean_dec(v_a_386_);
    lean_dec_ref(v_a_385_);
    return v_res_388_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(
    mut v_msgData_389_: *mut LeanObject,
    mut v___y_390_: *mut LeanObject,
    mut v___y_391_: *mut LeanObject,
    mut v___y_392_: *mut LeanObject,
    mut v___y_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = lean_st_ref_get(v___y_393_);
    v_env_396_ = lean_ctor_get(v___x_395_, 0);
    lean_inc_ref(v_env_396_);
    lean_dec(v___x_395_);
    v___x_397_ = lean_st_ref_get(v___y_391_);
    v_mctx_398_ = lean_ctor_get(v___x_397_, 0);
    lean_inc_ref(v_mctx_398_);
    lean_dec(v___x_397_);
    v_lctx_399_ = lean_ctor_get(v___y_390_, 2);
    v_options_400_ = lean_ctor_get(v___y_392_, 2);
    lean_inc_ref(v_options_400_);
    lean_inc_ref(v_lctx_399_);
    v___x_401_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_401_, 0, v_env_396_);
    lean_ctor_set(v___x_401_, 1, v_mctx_398_);
    lean_ctor_set(v___x_401_, 2, v_lctx_399_);
    lean_ctor_set(v___x_401_, 3, v_options_400_);
    v___x_402_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_402_, 0, v___x_401_);
    lean_ctor_set(v___x_402_, 1, v_msgData_389_);
    v___x_403_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_403_, 0, v___x_402_);
    return v___x_403_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0___boxed(
    mut v_msgData_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
    mut v___y_407_: *mut LeanObject,
    mut v___y_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_410_: *mut LeanObject = core::ptr::null_mut();
    v_res_410_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msgData_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
    lean_dec(v___y_408_);
    lean_dec_ref(v___y_407_);
    lean_dec(v___y_406_);
    lean_dec_ref(v___y_405_);
    return v_res_410_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: f64 = 0.0;
    v___x_411_ = lean_unsigned_to_nat(0);
    v___x_412_ = lean_float_of_nat(v___x_411_);
    return v___x_412_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(
    mut v_cls_415_: *mut LeanObject,
    mut v_msg_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_440_: u8 = 0;
    let mut v_tid_441_: u64 = 0;
    let mut v_traces_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: f64 = 0.0;
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_isSharedCheck_467_: u8 = 0;
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_422_ = lean_ctor_get(v___y_419_, 5);
                v___x_423_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
                v_a_424_ = lean_ctor_get(v___x_423_, 0);
                v_isSharedCheck_468_ = (!lean_is_exclusive(v___x_423_)) as u8;
                if v_isSharedCheck_468_ == 0 {
                    v___x_426_ = v___x_423_;
                    v_isShared_427_ = v_isSharedCheck_468_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_424_);
                    lean_dec(v___x_423_);
                    v___x_426_ = lean_box(0);
                    v_isShared_427_ = v_isSharedCheck_468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_428_ = lean_st_ref_take(v___y_420_);
                v_traceState_429_ = lean_ctor_get(v___x_428_, 4);
                v_env_430_ = lean_ctor_get(v___x_428_, 0);
                v_nextMacroScope_431_ = lean_ctor_get(v___x_428_, 1);
                v_ngen_432_ = lean_ctor_get(v___x_428_, 2);
                v_auxDeclNGen_433_ = lean_ctor_get(v___x_428_, 3);
                v_cache_434_ = lean_ctor_get(v___x_428_, 5);
                v_messages_435_ = lean_ctor_get(v___x_428_, 6);
                v_infoState_436_ = lean_ctor_get(v___x_428_, 7);
                v_snapshotTasks_437_ = lean_ctor_get(v___x_428_, 8);
                v_isSharedCheck_467_ = (!lean_is_exclusive(v___x_428_)) as u8;
                if v_isSharedCheck_467_ == 0 {
                    v___x_439_ = v___x_428_;
                    v_isShared_440_ = v_isSharedCheck_467_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_437_);
                    lean_inc(v_infoState_436_);
                    lean_inc(v_messages_435_);
                    lean_inc(v_cache_434_);
                    lean_inc(v_traceState_429_);
                    lean_inc(v_auxDeclNGen_433_);
                    lean_inc(v_ngen_432_);
                    lean_inc(v_nextMacroScope_431_);
                    lean_inc(v_env_430_);
                    lean_dec(v___x_428_);
                    v___x_439_ = lean_box(0);
                    v_isShared_440_ = v_isSharedCheck_467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_441_ = lean_ctor_get_uint64(
                    v_traceState_429_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_442_ = lean_ctor_get(v_traceState_429_, 0);
                v_isSharedCheck_466_ = (!lean_is_exclusive(v_traceState_429_)) as u8;
                if v_isSharedCheck_466_ == 0 {
                    v___x_444_ = v_traceState_429_;
                    v_isShared_445_ = v_isSharedCheck_466_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_442_);
                    lean_dec(v_traceState_429_);
                    v___x_444_ = lean_box(0);
                    v_isShared_445_ = v_isSharedCheck_466_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_446_ = lean_box(0);
                v___x_447_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0);
                v___x_448_ = 0;
                v___x_449_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0;
                v___x_450_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_450_, 0, v_cls_415_);
                lean_ctor_set(v___x_450_, 1, v___x_446_);
                lean_ctor_set(v___x_450_, 2, v___x_449_);
                lean_ctor_set_float(
                    v___x_450_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_447_,
                );
                lean_ctor_set_float(
                    v___x_450_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_447_,
                );
                lean_ctor_set_uint8(
                    v___x_450_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_448_,
                );
                v___x_451_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1;
                v___x_452_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_452_, 0, v___x_450_);
                lean_ctor_set(v___x_452_, 1, v_a_424_);
                lean_ctor_set(v___x_452_, 2, v___x_451_);
                lean_inc(v_ref_422_);
                v___x_453_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_453_, 0, v_ref_422_);
                lean_ctor_set(v___x_453_, 1, v___x_452_);
                v___x_454_ = l_Lean_PersistentArray_push___redArg(v_traces_442_, v___x_453_);
                if v_isShared_445_ == 0 {
                    lean_ctor_set(v___x_444_, 0, v___x_454_);
                    v___x_456_ = v___x_444_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_454_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_465_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_441_,
                    );
                    v___x_456_ = v_reuseFailAlloc_465_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_440_ == 0 {
                    lean_ctor_set(v___x_439_, 4, v___x_456_);
                    v___x_458_ = v___x_439_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_464_, 0, v_env_430_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 1, v_nextMacroScope_431_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 2, v_ngen_432_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 3, v_auxDeclNGen_433_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 4, v___x_456_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 5, v_cache_434_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 6, v_messages_435_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 7, v_infoState_436_);
                    lean_ctor_set(v_reuseFailAlloc_464_, 8, v_snapshotTasks_437_);
                    v___x_458_ = v_reuseFailAlloc_464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_459_ = lean_st_ref_set(v___y_420_, v___x_458_);
                v___x_460_ = lean_box(0);
                if v_isShared_427_ == 0 {
                    lean_ctor_set(v___x_426_, 0, v___x_460_);
                    v___x_462_ = v___x_426_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
                    v___x_462_ = v_reuseFailAlloc_463_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___boxed(
    mut v_cls_469_: *mut LeanObject,
    mut v_msg_470_: *mut LeanObject,
    mut v___y_471_: *mut LeanObject,
    mut v___y_472_: *mut LeanObject,
    mut v___y_473_: *mut LeanObject,
    mut v___y_474_: *mut LeanObject,
    mut v___y_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_476_: *mut LeanObject = core::ptr::null_mut();
    v_res_476_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(
            v_cls_469_, v_msg_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_,
        );
    lean_dec(v___y_474_);
    lean_dec_ref(v___y_473_);
    lean_dec(v___y_472_);
    lean_dec_ref(v___y_471_);
    return v_res_476_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12() -> *mut LeanObject
{
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_496_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9;
    v___x_497_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11;
    v___x_498_ = l_Lean_Name_append(v___x_497_, v___x_496_);
    return v___x_498_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14() -> *mut LeanObject
{
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13;
    v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16() -> *mut LeanObject
{
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15;
    v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
    return v___x_504_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_TacticContext_new(
    mut v_lratPath_505_: *mut LeanObject,
    mut v_config_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
    mut v_a_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
    mut v_a_511_: *mut LeanObject,
    mut v_a_512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_534_: u8 = 0;
    let mut v_inheritedTraceOptions_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_a_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_a_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_a_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_a_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_514_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1;
                v___x_515_ = l_Lean_Elab_Term_mkAuxName(
                    v___x_514_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_,
                );
                if lean_obj_tag(v___x_515_) == 0 {
                    v_a_516_ = lean_ctor_get(v___x_515_, 0);
                    lean_inc(v_a_516_);
                    lean_dec_ref_known(v___x_515_, 1);
                    v___x_517_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3;
                    v___x_518_ = l_Lean_Elab_Term_mkAuxName(
                        v___x_517_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_,
                    );
                    if lean_obj_tag(v___x_518_) == 0 {
                        v_a_519_ = lean_ctor_get(v___x_518_, 0);
                        lean_inc(v_a_519_);
                        lean_dec_ref_known(v___x_518_, 1);
                        v___x_520_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5;
                        v___x_521_ = l_Lean_Elab_Term_mkAuxName(
                            v___x_520_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_,
                        );
                        if lean_obj_tag(v___x_521_) == 0 {
                            v_a_522_ = lean_ctor_get(v___x_521_, 0);
                            lean_inc(v_a_522_);
                            lean_dec_ref_known(v___x_521_, 1);
                            v___x_523_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_511_);
                            if lean_obj_tag(v___x_523_) == 0 {
                                v_a_524_ = lean_ctor_get(v___x_523_, 0);
                                v_isSharedCheck_554_ = (!lean_is_exclusive(v___x_523_)) as u8;
                                if v_isSharedCheck_554_ == 0 {
                                    v___x_526_ = v___x_523_;
                                    v_isShared_527_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_524_);
                                    lean_dec(v___x_523_);
                                    v___x_526_ = lean_box(0);
                                    v_isShared_527_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_522_);
                                lean_dec(v_a_519_);
                                lean_dec(v_a_516_);
                                lean_dec_ref(v_config_506_);
                                lean_dec_ref(v_lratPath_505_);
                                v_a_555_ = lean_ctor_get(v___x_523_, 0);
                                v_isSharedCheck_562_ = (!lean_is_exclusive(v___x_523_)) as u8;
                                if v_isSharedCheck_562_ == 0 {
                                    v___x_557_ = v___x_523_;
                                    v_isShared_558_ = v_isSharedCheck_562_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_555_);
                                    lean_dec(v___x_523_);
                                    v___x_557_ = lean_box(0);
                                    v_isShared_558_ = v_isSharedCheck_562_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_519_);
                            lean_dec(v_a_516_);
                            lean_dec_ref(v_config_506_);
                            lean_dec_ref(v_lratPath_505_);
                            v_a_563_ = lean_ctor_get(v___x_521_, 0);
                            v_isSharedCheck_570_ = (!lean_is_exclusive(v___x_521_)) as u8;
                            if v_isSharedCheck_570_ == 0 {
                                v___x_565_ = v___x_521_;
                                v_isShared_566_ = v_isSharedCheck_570_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_563_);
                                lean_dec(v___x_521_);
                                v___x_565_ = lean_box(0);
                                v_isShared_566_ = v_isSharedCheck_570_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_516_);
                        lean_dec_ref(v_config_506_);
                        lean_dec_ref(v_lratPath_505_);
                        v_a_571_ = lean_ctor_get(v___x_518_, 0);
                        v_isSharedCheck_578_ = (!lean_is_exclusive(v___x_518_)) as u8;
                        if v_isSharedCheck_578_ == 0 {
                            v___x_573_ = v___x_518_;
                            v_isShared_574_ = v_isSharedCheck_578_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_571_);
                            lean_dec(v___x_518_);
                            v___x_573_ = lean_box(0);
                            v_isShared_574_ = v_isSharedCheck_578_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_config_506_);
                    lean_dec_ref(v_lratPath_505_);
                    v_a_579_ = lean_ctor_get(v___x_515_, 0);
                    v_isSharedCheck_586_ = (!lean_is_exclusive(v___x_515_)) as u8;
                    if v_isSharedCheck_586_ == 0 {
                        v___x_581_ = v___x_515_;
                        v_isShared_582_ = v_isSharedCheck_586_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_579_);
                        lean_dec(v___x_515_);
                        v___x_581_ = lean_box(0);
                        v_isShared_582_ = v_isSharedCheck_586_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_options_533_ = lean_ctor_get(v_a_511_, 2);
                v_hasTrace_534_ = lean_ctor_get_uint8(
                    v_options_533_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_534_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v_inheritedTraceOptions_535_ = lean_ctor_get(v_a_511_, 13);
                    v___x_536_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9;
                    v___x_537_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12,
                    );
                    v___x_538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_535_,
                        v_options_533_,
                        v___x_537_,
                    );
                    if v___x_538_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_539_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14,
                        );
                        lean_inc(v_a_524_);
                        v___x_540_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_540_, 0, v_a_524_);
                        v___x_541_ = l_Lean_MessageData_ofFormat(v___x_540_);
                        v___x_542_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_542_, 0, v___x_539_);
                        lean_ctor_set(v___x_542_, 1, v___x_541_);
                        v___x_543_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16,
                        );
                        v___x_544_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_544_, 0, v___x_542_);
                        lean_ctor_set(v___x_544_, 1, v___x_543_);
                        v___x_545_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v___x_536_, v___x_544_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
                        if lean_obj_tag(v___x_545_) == 0 {
                            lean_dec_ref_known(v___x_545_, 1);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_526_);
                            lean_dec(v_a_524_);
                            lean_dec(v_a_522_);
                            lean_dec(v_a_519_);
                            lean_dec(v_a_516_);
                            lean_dec_ref(v_config_506_);
                            lean_dec_ref(v_lratPath_505_);
                            v_a_546_ = lean_ctor_get(v___x_545_, 0);
                            v_isSharedCheck_553_ = (!lean_is_exclusive(v___x_545_)) as u8;
                            if v_isSharedCheck_553_ == 0 {
                                v___x_548_ = v___x_545_;
                                v_isShared_549_ = v_isSharedCheck_553_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_546_);
                                lean_dec(v___x_545_);
                                v___x_548_ = lean_box(0);
                                v_isShared_549_ = v_isSharedCheck_553_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_529_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_529_, 0, v_a_516_);
                lean_ctor_set(v___x_529_, 1, v_a_519_);
                lean_ctor_set(v___x_529_, 2, v_a_522_);
                lean_ctor_set(v___x_529_, 3, v_a_524_);
                lean_ctor_set(v___x_529_, 4, v_lratPath_505_);
                lean_ctor_set(v___x_529_, 5, v_config_506_);
                if v_isShared_527_ == 0 {
                    lean_ctor_set(v___x_526_, 0, v___x_529_);
                    v___x_531_ = v___x_526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_531_;
            }
            4 => {
                if v_isShared_549_ == 0 {
                    v___x_551_ = v___x_548_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
                    v___x_551_ = v_reuseFailAlloc_552_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_551_;
            }
            6 => {
                if v_isShared_558_ == 0 {
                    v___x_560_ = v___x_557_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_560_;
            }
            8 => {
                if v_isShared_566_ == 0 {
                    v___x_568_ = v___x_565_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
                    v___x_568_ = v_reuseFailAlloc_569_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_568_;
            }
            10 => {
                if v_isShared_574_ == 0 {
                    v___x_576_ = v___x_573_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_576_;
            }
            12 => {
                if v_isShared_582_ == 0 {
                    v___x_584_ = v___x_581_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
                    v___x_584_ = v_reuseFailAlloc_585_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_TacticContext_new___boxed(
    mut v_lratPath_587_: *mut LeanObject,
    mut v_config_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
    mut v_a_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
    mut v_a_592_: *mut LeanObject,
    mut v_a_593_: *mut LeanObject,
    mut v_a_594_: *mut LeanObject,
    mut v_a_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_596_: *mut LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(
        v_lratPath_587_,
        v_config_588_,
        v_a_589_,
        v_a_590_,
        v_a_591_,
        v_a_592_,
        v_a_593_,
        v_a_594_,
    );
    lean_dec(v_a_594_);
    lean_dec_ref(v_a_593_);
    lean_dec(v_a_592_);
    lean_dec_ref(v_a_591_);
    lean_dec(v_a_590_);
    lean_dec_ref(v_a_589_);
    return v_res_596_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(
    mut v_cls_597_: *mut LeanObject,
    mut v_msg_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
    mut v___y_600_: *mut LeanObject,
    mut v___y_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    v___x_606_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(
            v_cls_597_, v_msg_598_, v___y_601_, v___y_602_, v___y_603_, v___y_604_,
        );
    return v___x_606_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___boxed(
    mut v_cls_607_: *mut LeanObject,
    mut v_msg_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
    mut v___y_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
    mut v___y_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_616_: *mut LeanObject = core::ptr::null_mut();
    v_res_616_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(
        v_cls_607_, v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_,
        v___y_614_,
    );
    lean_dec(v___y_614_);
    lean_dec_ref(v___y_613_);
    lean_dec(v___y_612_);
    lean_dec_ref(v___y_611_);
    lean_dec(v___y_610_);
    lean_dec_ref(v___y_609_);
    return v_res_616_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
}
