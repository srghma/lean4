// Lean compiler output
// Module: Init.Data.Array.Lemmas
// Imports: Init.Data.List.ToArray Init.Data.List.Control Init.Data.Array.Basic Init.Data.Array.Bootstrap Init.Data.Nat.Lemmas Init.Data.Nat.MinMax Init.ByCases Init.Data.Array.DecidableEq Init.Data.Bool Init.Data.Fin.Lemmas Init.Data.List.Find Init.Data.List.Nat.Basic Init.Data.List.Nat.Modify Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.Zip Init.Data.Nat.Linear Init.Data.Nat.Simproc Init.Data.Option.Lemmas Init.Data.Prod Init.Omega Init.TacticsExtra
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg,
    l_Array_contains___redArg, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Nat::Basic::{
    initialize_Init_Data_List_Nat_Basic, runtime_initialize_Init_Data_List_Nat_Basic,
};
use crate::r#gen::Init::Data::List::Nat::Modify::{
    initialize_Init_Data_List_Nat_Modify, runtime_initialize_Init_Data_List_Nat_Modify,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, l_Nat_decidableBallLT___redArg,
    l_Nat_decidableExistsLT_x27___redArg, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Array_filterMap__replicate___auto__7___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__0_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__1_value: LeanStringObject<7> =
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
static mut l_Array_filterMap__replicate___auto__7___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__1_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__2_value: LeanStringObject<7> =
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
static mut l_Array_filterMap__replicate___auto__7___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__2_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__3_value: LeanStringObject<10> =
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
static mut l_Array_filterMap__replicate___auto__7___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__3_value)
        as *mut LeanObject;
static l_Array_filterMap__replicate___auto__7___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Array_filterMap__replicate___auto__7___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__4_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Array_filterMap__replicate___auto__7___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__5_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__6_value: LeanStringObject<19> =
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
static mut l_Array_filterMap__replicate___auto__7___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__6_value)
        as *mut LeanObject;
static l_Array_filterMap__replicate___auto__7___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Array_filterMap__replicate___auto__7___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__7_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__8_value: LeanStringObject<5> =
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
static mut l_Array_filterMap__replicate___auto__7___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__8_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__9_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__10_value: LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__10_value)
        as *mut LeanObject;
static l_Array_filterMap__replicate___auto__7___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Array_filterMap__replicate___auto__7___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__10_value)
                as *mut LeanObject,
            12783917532758215986 as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__11_value)
        as *mut LeanObject;
static mut l_Array_filterMap__replicate___auto__7___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_filterMap__replicate___auto__7___closed__14_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__14_value)
        as *mut LeanObject;
static l_Array_filterMap__replicate___auto__7___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__15_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Array_filterMap__replicate___auto__7___closed__15_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Array_filterMap__replicate___auto__7___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__14_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__15_value)
        as *mut LeanObject;
pub static l_Array_filterMap__replicate___auto__7___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Array_filterMap__replicate___auto__7___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Array_filterMap__replicate___auto__7___closed__16_value)
        as *mut LeanObject;
static mut l_Array_filterMap__replicate___auto__7___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_filterMap__replicate___auto__7___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_filterMap__replicate___auto__7___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_filterMap__replicate___auto__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_toListRev___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Array_toListRev___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Array_toListRev___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_toListRev___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toListRev___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Array_toListRev___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__9_value) as *mut LeanObject;
pub static l_Array_toListRev___redArg___closed__10_value: LeanClosureObject<0> =
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
        m_fun: l_Array_toListRev___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toListRev___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toListRev___redArg___closed__10_value) as *mut LeanObject;
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(
    mut v_xs_620_: *mut LeanObject,
    mut v_inst_621_: *mut LeanObject,
    mut v_n_622_: *mut LeanObject,
    mut v_h_623_: *mut LeanObject,
) -> u8 {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: u8 = 0;
    v___x_624_ = lean_array_fget_borrowed(v_xs_620_, v_n_622_);
    lean_inc(v___x_624_);
    v___x_625_ = lean_apply_1(v_inst_621_, v___x_624_);
    v___x_626_ = (lean_unbox(v___x_625_) as u8);
    return v___x_626_;
}
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed(
    mut v_xs_627_: *mut LeanObject,
    mut v_inst_628_: *mut LeanObject,
    mut v_n_629_: *mut LeanObject,
    mut v_h_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_631_: u8 = 0;
    let mut v_r_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0(
        v_xs_627_,
        v_inst_628_,
        v_n_629_,
        v_h_630_,
    );
    lean_dec(v_n_629_);
    lean_dec_ref(v_xs_627_);
    v_r_632_ = lean_box((v_res_631_) as usize);
    return v_r_632_;
}
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred___redArg(
    mut v_xs_633_: *mut LeanObject,
    mut v_inst_634_: *mut LeanObject,
) -> u8 {
    let mut v___f_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    lean_inc_ref(v_xs_633_);
    v___f_635_ = lean_alloc_closure(
        l_Array_instDecidableForallForallMemOfDecidablePred___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_635_, 0, v_xs_633_);
    lean_closure_set(v___f_635_, 1, v_inst_634_);
    v___x_636_ = lean_array_get_size(v_xs_633_);
    lean_dec_ref(v_xs_633_);
    v___x_637_ = l_Nat_decidableBallLT___redArg(v___x_636_, v___f_635_);
    return v___x_637_;
}
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred___redArg___boxed(
    mut v_xs_638_: *mut LeanObject,
    mut v_inst_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_640_: u8 = 0;
    let mut v_r_641_: *mut LeanObject = core::ptr::null_mut();
    v_res_640_ =
        l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_638_, v_inst_639_);
    v_r_641_ = lean_box((v_res_640_) as usize);
    return v_r_641_;
}
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred(
    mut v_00_u03b1_642_: *mut LeanObject,
    mut v_xs_643_: *mut LeanObject,
    mut v_p_644_: *mut LeanObject,
    mut v_inst_645_: *mut LeanObject,
) -> u8 {
    let mut v___x_646_: u8 = 0;
    v___x_646_ =
        l_Array_instDecidableForallForallMemOfDecidablePred___redArg(v_xs_643_, v_inst_645_);
    return v___x_646_;
}
pub unsafe fn l_Array_instDecidableForallForallMemOfDecidablePred___boxed(
    mut v_00_u03b1_647_: *mut LeanObject,
    mut v_xs_648_: *mut LeanObject,
    mut v_p_649_: *mut LeanObject,
    mut v_inst_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_651_: u8 = 0;
    let mut v_r_652_: *mut LeanObject = core::ptr::null_mut();
    v_res_651_ = l_Array_instDecidableForallForallMemOfDecidablePred(
        v_00_u03b1_647_,
        v_xs_648_,
        v_p_649_,
        v_inst_650_,
    );
    v_r_652_ = lean_box((v_res_651_) as usize);
    return v_r_652_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(
    mut v_xs_653_: *mut LeanObject,
    mut v_inst_654_: *mut LeanObject,
    mut v_m_655_: *mut LeanObject,
    mut v_h_656_: *mut LeanObject,
) -> u8 {
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    v___x_657_ = lean_array_fget_borrowed(v_xs_653_, v_m_655_);
    lean_inc(v___x_657_);
    v___x_658_ = lean_apply_1(v_inst_654_, v___x_657_);
    v___x_659_ = (lean_unbox(v___x_658_) as u8);
    return v___x_659_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed(
    mut v_xs_660_: *mut LeanObject,
    mut v_inst_661_: *mut LeanObject,
    mut v_m_662_: *mut LeanObject,
    mut v_h_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_664_: u8 = 0;
    let mut v_r_665_: *mut LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0(
        v_xs_660_,
        v_inst_661_,
        v_m_662_,
        v_h_663_,
    );
    lean_dec(v_m_662_);
    lean_dec_ref(v_xs_660_);
    v_r_665_ = lean_box((v_res_664_) as usize);
    return v_r_665_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(
    mut v_xs_666_: *mut LeanObject,
    mut v_inst_667_: *mut LeanObject,
) -> u8 {
    let mut v___f_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    lean_inc_ref(v_xs_666_);
    v___f_668_ = lean_alloc_closure(
        l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_668_, 0, v_xs_666_);
    lean_closure_set(v___f_668_, 1, v_inst_667_);
    v___x_669_ = lean_array_get_size(v_xs_666_);
    lean_dec_ref(v_xs_666_);
    v___x_670_ = l_Nat_decidableExistsLT_x27___redArg(v___x_669_, v___f_668_);
    return v___x_670_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred___redArg___boxed(
    mut v_xs_671_: *mut LeanObject,
    mut v_inst_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_673_: u8 = 0;
    let mut v_r_674_: *mut LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_671_, v_inst_672_);
    v_r_674_ = lean_box((v_res_673_) as usize);
    return v_r_674_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred(
    mut v_00_u03b1_675_: *mut LeanObject,
    mut v_xs_676_: *mut LeanObject,
    mut v_p_677_: *mut LeanObject,
    mut v_inst_678_: *mut LeanObject,
) -> u8 {
    let mut v___x_679_: u8 = 0;
    v___x_679_ = l_Array_instDecidableExistsAndMemOfDecidablePred___redArg(v_xs_676_, v_inst_678_);
    return v___x_679_;
}
pub unsafe fn l_Array_instDecidableExistsAndMemOfDecidablePred___boxed(
    mut v_00_u03b1_680_: *mut LeanObject,
    mut v_xs_681_: *mut LeanObject,
    mut v_p_682_: *mut LeanObject,
    mut v_inst_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: u8 = 0;
    let mut v_r_685_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Array_instDecidableExistsAndMemOfDecidablePred(
        v_00_u03b1_680_,
        v_xs_681_,
        v_p_682_,
        v_inst_683_,
    );
    v_r_685_ = lean_box((v_res_684_) as usize);
    return v_r_685_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter___redArg(
    mut v_x_686_: *mut LeanObject,
    mut v_h__1_687_: *mut LeanObject,
    mut v_h__2_688_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_686_) == 0 {
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_688_);
        v___x_689_ = lean_box(0);
        v___x_690_ = lean_apply_1(v_h__1_687_, v___x_689_);
        return v___x_690_;
    } else {
        let mut v_head_691_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_687_);
        v_head_691_ = lean_ctor_get(v_x_686_, 0);
        lean_inc(v_head_691_);
        v_tail_692_ = lean_ctor_get(v_x_686_, 1);
        lean_inc(v_tail_692_);
        lean_dec_ref_known(v_x_686_, 2);
        v___x_693_ = lean_apply_2(v_h__2_688_, v_head_691_, v_tail_692_);
        return v___x_693_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_694_: *mut LeanObject,
    mut v_motive_695_: *mut LeanObject,
    mut v_x_696_: *mut LeanObject,
    mut v_h__1_697_: *mut LeanObject,
    mut v_h__2_698_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_696_) == 0 {
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_698_);
        v___x_699_ = lean_box(0);
        v___x_700_ = lean_apply_1(v_h__1_697_, v___x_699_);
        return v___x_700_;
    } else {
        let mut v_head_701_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_697_);
        v_head_701_ = lean_ctor_get(v_x_696_, 0);
        lean_inc(v_head_701_);
        v_tail_702_ = lean_ctor_get(v_x_696_, 1);
        lean_inc(v_tail_702_);
        lean_dec_ref_known(v_x_696_, 2);
        v___x_703_ = lean_apply_2(v_h__2_698_, v_head_701_, v_tail_702_);
        return v___x_703_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_704_: u8,
    mut v_h__1_705_: *mut LeanObject,
    mut v_h__2_706_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_704_ == 0 {
        let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_705_);
        v___x_707_ = lean_box(0);
        v___x_708_ = lean_apply_1(v_h__2_706_, v___x_707_);
        return v___x_708_;
    } else {
        let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_706_);
        v___x_709_ = lean_box(0);
        v___x_710_ = lean_apply_1(v_h__1_705_, v___x_709_);
        return v___x_710_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_711_: *mut LeanObject,
    mut v_h__1_712_: *mut LeanObject,
    mut v_h__2_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_26__boxed_714_: u8 = 0;
    let mut v_res_715_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_714_ = (lean_unbox(v_____do__lift_711_) as u8);
    v_res_715_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_714_,
        v_h__1_712_,
        v_h__2_713_,
    );
    return v_res_715_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(
    mut v_motive_716_: *mut LeanObject,
    mut v_____do__lift_717_: u8,
    mut v_h__1_718_: *mut LeanObject,
    mut v_h__2_719_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_717_ == 0 {
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_718_);
        v___x_720_ = lean_box(0);
        v___x_721_ = lean_apply_1(v_h__2_719_, v___x_720_);
        return v___x_721_;
    } else {
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_719_);
        v___x_722_ = lean_box(0);
        v___x_723_ = lean_apply_1(v_h__1_718_, v___x_722_);
        return v___x_723_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_724_: *mut LeanObject,
    mut v_____do__lift_725_: *mut LeanObject,
    mut v_h__1_726_: *mut LeanObject,
    mut v_h__2_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_37__boxed_728_: u8 = 0;
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_728_ = (lean_unbox(v_____do__lift_725_) as u8);
    v_res_729_ = l___private_Init_Data_Array_Lemmas_0__List_anyM_match__1_splitter(
        v_motive_724_,
        v_____do__lift_37__boxed_728_,
        v_h__1_726_,
        v_h__2_727_,
    );
    return v_res_729_;
}
pub unsafe fn l_Array_instDecidableMemOfLawfulBEq___redArg(
    mut v_inst_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_as_732_: *mut LeanObject,
) -> u8 {
    let mut v___x_733_: u8 = 0;
    v___x_733_ = l_Array_contains___redArg(v_inst_730_, v_as_732_, v_a_731_);
    return v___x_733_;
}
pub unsafe fn l_Array_instDecidableMemOfLawfulBEq___redArg___boxed(
    mut v_inst_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_as_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_737_: u8 = 0;
    let mut v_r_738_: *mut LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Array_instDecidableMemOfLawfulBEq___redArg(v_inst_734_, v_a_735_, v_as_736_);
    v_r_738_ = lean_box((v_res_737_) as usize);
    return v_r_738_;
}
pub unsafe fn l_Array_instDecidableMemOfLawfulBEq(
    mut v_00_u03b1_739_: *mut LeanObject,
    mut v_inst_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_as_743_: *mut LeanObject,
) -> u8 {
    let mut v___x_744_: u8 = 0;
    v___x_744_ = l_Array_contains___redArg(v_inst_740_, v_as_743_, v_a_742_);
    return v___x_744_;
}
pub unsafe fn l_Array_instDecidableMemOfLawfulBEq___boxed(
    mut v_00_u03b1_745_: *mut LeanObject,
    mut v_inst_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
    mut v_as_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_750_: u8 = 0;
    let mut v_r_751_: *mut LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Array_instDecidableMemOfLawfulBEq(
        v_00_u03b1_745_,
        v_inst_746_,
        v_inst_747_,
        v_a_748_,
        v_as_749_,
    );
    v_r_751_ = lean_box((v_res_750_) as usize);
    return v_r_751_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_752_: *mut LeanObject,
    mut v_h__1_753_: *mut LeanObject,
    mut v_h__2_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_756_: u8 = 0;
    v_zero_755_ = lean_unsigned_to_nat(0);
    v_isZero_756_ = lean_nat_dec_eq(v_x_752_, v_zero_755_);
    if v_isZero_756_ == 1 {
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_754_);
        v___x_757_ = lean_apply_1(v_h__1_753_, lean_box(0));
        return v___x_757_;
    } else {
        let mut v_one_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_753_);
        v_one_758_ = lean_unsigned_to_nat(1);
        v_n_759_ = lean_nat_sub(v_x_752_, v_one_758_);
        v___x_760_ = lean_apply_2(v_h__2_754_, v_n_759_, lean_box(0));
        return v___x_760_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_761_: *mut LeanObject,
    mut v_h__1_762_: *mut LeanObject,
    mut v_h__2_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_764_: *mut LeanObject = core::ptr::null_mut();
    v_res_764_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___redArg(
        v_x_761_,
        v_h__1_762_,
        v_h__2_763_,
    );
    lean_dec(v_x_761_);
    return v_res_764_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_765_: *mut LeanObject,
    mut v_xs_766_: *mut LeanObject,
    mut v_motive_767_: *mut LeanObject,
    mut v_x_768_: *mut LeanObject,
    mut v_x_769_: *mut LeanObject,
    mut v_h__1_770_: *mut LeanObject,
    mut v_h__2_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_773_: u8 = 0;
    v_zero_772_ = lean_unsigned_to_nat(0);
    v_isZero_773_ = lean_nat_dec_eq(v_x_768_, v_zero_772_);
    if v_isZero_773_ == 1 {
        let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_771_);
        v___x_774_ = lean_apply_1(v_h__1_770_, lean_box(0));
        return v___x_774_;
    } else {
        let mut v_one_775_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_770_);
        v_one_775_ = lean_unsigned_to_nat(1);
        v_n_776_ = lean_nat_sub(v_x_768_, v_one_775_);
        v___x_777_ = lean_apply_2(v_h__2_771_, v_n_776_, lean_box(0));
        return v___x_777_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_778_: *mut LeanObject,
    mut v_xs_779_: *mut LeanObject,
    mut v_motive_780_: *mut LeanObject,
    mut v_x_781_: *mut LeanObject,
    mut v_x_782_: *mut LeanObject,
    mut v_h__1_783_: *mut LeanObject,
    mut v_h__2_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_785_ = l___private_Init_Data_Array_Lemmas_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_778_,
        v_xs_779_,
        v_motive_780_,
        v_x_781_,
        v_x_782_,
        v_h__1_783_,
        v_h__2_784_,
    );
    lean_dec(v_x_781_);
    lean_dec_ref(v_xs_779_);
    return v_res_785_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter___redArg(
    mut v_____do__lift_786_: *mut LeanObject,
    mut v_h__1_787_: *mut LeanObject,
    mut v_h__2_788_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_786_) == 0 {
        let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_787_);
        v___x_789_ = lean_box(0);
        v___x_790_ = lean_apply_1(v_h__2_788_, v___x_789_);
        return v___x_790_;
    } else {
        let mut v_val_791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_788_);
        v_val_791_ = lean_ctor_get(v_____do__lift_786_, 0);
        lean_inc(v_val_791_);
        lean_dec_ref_known(v_____do__lift_786_, 1);
        v___x_792_ = lean_apply_1(v_h__1_787_, v_val_791_);
        return v___x_792_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_filterMapM_match__1_splitter(
    mut v_00_u03b2_793_: *mut LeanObject,
    mut v_motive_794_: *mut LeanObject,
    mut v_____do__lift_795_: *mut LeanObject,
    mut v_h__1_796_: *mut LeanObject,
    mut v_h__2_797_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_795_) == 0 {
        let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_796_);
        v___x_798_ = lean_box(0);
        v___x_799_ = lean_apply_1(v_h__2_797_, v___x_798_);
        return v___x_799_;
    } else {
        let mut v_val_800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_797_);
        v_val_800_ = lean_ctor_get(v_____do__lift_795_, 0);
        lean_inc(v_val_800_);
        lean_dec_ref_known(v_____do__lift_795_, 1);
        v___x_801_ = lean_apply_1(v_h__1_796_, v_val_800_);
        return v___x_801_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_802_: *mut LeanObject,
    mut v_h__1_803_: *mut LeanObject,
    mut v_h__2_804_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_802_) == 0 {
        let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_804_);
        v___x_805_ = lean_box(0);
        v___x_806_ = lean_apply_1(v_h__1_803_, v___x_805_);
        return v___x_806_;
    } else {
        let mut v_val_807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_803_);
        v_val_807_ = lean_ctor_get(v_x_802_, 0);
        lean_inc(v_val_807_);
        lean_dec_ref_known(v_x_802_, 1);
        v___x_808_ = lean_apply_1(v_h__2_804_, v_val_807_);
        return v___x_808_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_809_: *mut LeanObject,
    mut v_motive_810_: *mut LeanObject,
    mut v_x_811_: *mut LeanObject,
    mut v_h__1_812_: *mut LeanObject,
    mut v_h__2_813_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_811_) == 0 {
        let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_813_);
        v___x_814_ = lean_box(0);
        v___x_815_ = lean_apply_1(v_h__1_812_, v___x_814_);
        return v___x_815_;
    } else {
        let mut v_val_816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_812_);
        v_val_816_ = lean_ctor_get(v_x_811_, 0);
        lean_inc(v_val_816_);
        lean_dec_ref_known(v_x_811_, 1);
        v___x_817_ = lean_apply_1(v_h__2_813_, v_val_816_);
        return v___x_817_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter___redArg(
    mut v_x_818_: *mut LeanObject,
    mut v_h__1_819_: *mut LeanObject,
    mut v_h__2_820_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_818_) == 0 {
        let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_820_);
        v___x_821_ = lean_box(0);
        v___x_822_ = lean_apply_1(v_h__1_819_, v___x_821_);
        return v___x_822_;
    } else {
        let mut v_val_823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_819_);
        v_val_823_ = lean_ctor_get(v_x_818_, 0);
        lean_inc(v_val_823_);
        lean_dec_ref_known(v_x_818_, 1);
        v___x_824_ = lean_apply_1(v_h__2_820_, v_val_823_);
        return v___x_824_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_filterMap__push_match__1_splitter(
    mut v_00_u03b2_825_: *mut LeanObject,
    mut v_motive_826_: *mut LeanObject,
    mut v_x_827_: *mut LeanObject,
    mut v_h__1_828_: *mut LeanObject,
    mut v_h__2_829_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_827_) == 0 {
        let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_829_);
        v___x_830_ = lean_box(0);
        v___x_831_ = lean_apply_1(v_h__1_828_, v___x_830_);
        return v___x_831_;
    } else {
        let mut v_val_832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_828_);
        v_val_832_ = lean_ctor_get(v_x_827_, 0);
        lean_inc(v_val_832_);
        lean_dec_ref_known(v_x_827_, 1);
        v___x_833_ = lean_apply_1(v_h__2_829_, v_val_832_);
        return v___x_833_;
    }
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__12() -> *mut LeanObject {
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Array_filterMap__replicate___auto__7___closed__10;
    v___x_861_ = l_Lean_mkAtom(v___x_860_);
    return v___x_861_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__13() -> *mut LeanObject {
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_862_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__12),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__12_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__12,
    );
    v___x_863_ = l_Array_filterMap__replicate___auto__7___closed__5;
    v___x_864_ = lean_array_push(v___x_863_, v___x_862_);
    return v___x_864_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__17() -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Array_filterMap__replicate___auto__7___closed__16;
    v___x_876_ = l_Array_filterMap__replicate___auto__7___closed__5;
    v___x_877_ = lean_array_push(v___x_876_, v___x_875_);
    return v___x_877_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__18() -> *mut LeanObject {
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    v___x_878_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__17),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__17_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__17,
    );
    v___x_879_ = l_Array_filterMap__replicate___auto__7___closed__15;
    v___x_880_ = lean_box(2);
    v___x_881_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_881_, 0, v___x_880_);
    lean_ctor_set(v___x_881_, 1, v___x_879_);
    lean_ctor_set(v___x_881_, 2, v___x_878_);
    return v___x_881_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__19() -> *mut LeanObject {
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    v___x_882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__18),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__18_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__18,
    );
    v___x_883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__13),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__13_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__13,
    );
    v___x_884_ = lean_array_push(v___x_883_, v___x_882_);
    return v___x_884_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__20() -> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Array_filterMap__replicate___auto__7___closed__16;
    v___x_886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__19),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__19_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__19,
    );
    v___x_887_ = lean_array_push(v___x_886_, v___x_885_);
    return v___x_887_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__21() -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Array_filterMap__replicate___auto__7___closed__16;
    v___x_889_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__20),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__20_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__20,
    );
    v___x_890_ = lean_array_push(v___x_889_, v___x_888_);
    return v___x_890_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__22() -> *mut LeanObject {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Array_filterMap__replicate___auto__7___closed__16;
    v___x_892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__21),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__21_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__21,
    );
    v___x_893_ = lean_array_push(v___x_892_, v___x_891_);
    return v___x_893_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__23() -> *mut LeanObject {
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v___x_894_ = l_Array_filterMap__replicate___auto__7___closed__16;
    v___x_895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__22),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__22_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__22,
    );
    v___x_896_ = lean_array_push(v___x_895_, v___x_894_);
    return v___x_896_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__24() -> *mut LeanObject {
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    v___x_897_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__23),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__23_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__23,
    );
    v___x_898_ = l_Array_filterMap__replicate___auto__7___closed__11;
    v___x_899_ = lean_box(2);
    v___x_900_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_900_, 0, v___x_899_);
    lean_ctor_set(v___x_900_, 1, v___x_898_);
    lean_ctor_set(v___x_900_, 2, v___x_897_);
    return v___x_900_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__25() -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    v___x_901_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__24),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__24_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__24,
    );
    v___x_902_ = l_Array_filterMap__replicate___auto__7___closed__5;
    v___x_903_ = lean_array_push(v___x_902_, v___x_901_);
    return v___x_903_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__26() -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    v___x_904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__25),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__25_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__25,
    );
    v___x_905_ = l_Array_filterMap__replicate___auto__7___closed__9;
    v___x_906_ = lean_box(2);
    v___x_907_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_907_, 0, v___x_906_);
    lean_ctor_set(v___x_907_, 1, v___x_905_);
    lean_ctor_set(v___x_907_, 2, v___x_904_);
    return v___x_907_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__27() -> *mut LeanObject {
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_908_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__26),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__26_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__26,
    );
    v___x_909_ = l_Array_filterMap__replicate___auto__7___closed__5;
    v___x_910_ = lean_array_push(v___x_909_, v___x_908_);
    return v___x_910_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__28() -> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__27),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__27_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__27,
    );
    v___x_912_ = l_Array_filterMap__replicate___auto__7___closed__7;
    v___x_913_ = lean_box(2);
    v___x_914_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v___x_913_);
    lean_ctor_set(v___x_914_, 1, v___x_912_);
    lean_ctor_set(v___x_914_, 2, v___x_911_);
    return v___x_914_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__29() -> *mut LeanObject {
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__28),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__28_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__28,
    );
    v___x_916_ = l_Array_filterMap__replicate___auto__7___closed__5;
    v___x_917_ = lean_array_push(v___x_916_, v___x_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7___closed__30() -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__29),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__29_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__29,
    );
    v___x_919_ = l_Array_filterMap__replicate___auto__7___closed__4;
    v___x_920_ = lean_box(2);
    v___x_921_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_921_, 0, v___x_920_);
    lean_ctor_set(v___x_921_, 1, v___x_919_);
    lean_ctor_set(v___x_921_, 2, v___x_918_);
    return v___x_921_;
}
pub unsafe fn _init_l_Array_filterMap__replicate___auto__7() -> *mut LeanObject {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___x_922_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__30),
        core::ptr::addr_of_mut!(l_Array_filterMap__replicate___auto__7___closed__30_once),
        _init_l_Array_filterMap__replicate___auto__7___closed__30,
    );
    return v___x_922_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter___redArg(
    mut v_x_923_: *mut LeanObject,
    mut v_h__1_924_: *mut LeanObject,
    mut v_h__2_925_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_923_) == 0 {
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_925_);
        v___x_926_ = lean_box(0);
        v___x_927_ = lean_apply_1(v_h__1_924_, v___x_926_);
        return v___x_927_;
    } else {
        let mut v_val_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_924_);
        v_val_928_ = lean_ctor_get(v_x_923_, 0);
        lean_inc(v_val_928_);
        lean_dec_ref_known(v_x_923_, 1);
        v___x_929_ = lean_apply_1(v_h__2_925_, v_val_928_);
        return v___x_929_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_filterMap__replicate_match__1_splitter(
    mut v_00_u03b2_930_: *mut LeanObject,
    mut v_motive_931_: *mut LeanObject,
    mut v_x_932_: *mut LeanObject,
    mut v_h__1_933_: *mut LeanObject,
    mut v_h__2_934_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_932_) == 0 {
        let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_934_);
        v___x_935_ = lean_box(0);
        v___x_936_ = lean_apply_1(v_h__1_933_, v___x_935_);
        return v___x_936_;
    } else {
        let mut v_val_937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_933_);
        v_val_937_ = lean_ctor_get(v_x_932_, 0);
        lean_inc(v_val_937_);
        lean_dec_ref_known(v_x_932_, 1);
        v___x_938_ = lean_apply_1(v_h__2_934_, v_val_937_);
        return v___x_938_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(
    mut v_i_939_: *mut LeanObject,
    mut v_h__1_940_: *mut LeanObject,
    mut v_h__2_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_943_: u8 = 0;
    v_zero_942_ = lean_unsigned_to_nat(0);
    v_isZero_943_ = lean_nat_dec_eq(v_i_939_, v_zero_942_);
    if v_isZero_943_ == 1 {
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_941_);
        v___x_944_ = lean_box(0);
        v___x_945_ = lean_apply_1(v_h__1_940_, v___x_944_);
        return v___x_945_;
    } else {
        let mut v_one_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_940_);
        v_one_946_ = lean_unsigned_to_nat(1);
        v_n_947_ = lean_nat_sub(v_i_939_, v_one_946_);
        v___x_948_ = lean_apply_1(v_h__2_941_, v_n_947_);
        return v___x_948_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg___boxed(
    mut v_i_949_: *mut LeanObject,
    mut v_h__1_950_: *mut LeanObject,
    mut v_h__2_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_952_ =
        l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___redArg(
            v_i_949_,
            v_h__1_950_,
            v_h__2_951_,
        );
    lean_dec(v_i_949_);
    return v_res_952_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(
    mut v_motive_953_: *mut LeanObject,
    mut v_i_954_: *mut LeanObject,
    mut v_h__1_955_: *mut LeanObject,
    mut v_h__2_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_958_: u8 = 0;
    v_zero_957_ = lean_unsigned_to_nat(0);
    v_isZero_958_ = lean_nat_dec_eq(v_i_954_, v_zero_957_);
    if v_isZero_958_ == 1 {
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_956_);
        v___x_959_ = lean_box(0);
        v___x_960_ = lean_apply_1(v_h__1_955_, v___x_959_);
        return v___x_960_;
    } else {
        let mut v_one_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_955_);
        v_one_961_ = lean_unsigned_to_nat(1);
        v_n_962_ = lean_nat_sub(v_i_954_, v_one_961_);
        v___x_963_ = lean_apply_1(v_h__2_956_, v_n_962_);
        return v___x_963_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter___boxed(
    mut v_motive_964_: *mut LeanObject,
    mut v_i_965_: *mut LeanObject,
    mut v_h__1_966_: *mut LeanObject,
    mut v_h__2_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_968_ = l___private_Init_Data_Array_Lemmas_0__Array_appendCore_loop_match__1_splitter(
        v_motive_964_,
        v_i_965_,
        v_h__1_966_,
        v_h__2_967_,
    );
    lean_dec(v_i_965_);
    return v_res_968_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(
    mut v_x_969_: *mut LeanObject,
    mut v_x_970_: *mut LeanObject,
    mut v_h__1_971_: *mut LeanObject,
    mut v_h__2_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_974_: u8 = 0;
    v_zero_973_ = lean_unsigned_to_nat(0);
    v_isZero_974_ = lean_nat_dec_eq(v_x_969_, v_zero_973_);
    if v_isZero_974_ == 1 {
        let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_972_);
        v___x_975_ = lean_apply_1(v_h__1_971_, v_x_970_);
        return v___x_975_;
    } else {
        let mut v_one_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_971_);
        v_one_976_ = lean_unsigned_to_nat(1);
        v_n_977_ = lean_nat_sub(v_x_969_, v_one_976_);
        v___x_978_ = lean_apply_2(v_h__2_972_, v_n_977_, v_x_970_);
        return v___x_978_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg___boxed(
    mut v_x_979_: *mut LeanObject,
    mut v_x_980_: *mut LeanObject,
    mut v_h__1_981_: *mut LeanObject,
    mut v_h__2_982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_983_: *mut LeanObject = core::ptr::null_mut();
    v_res_983_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___redArg(
        v_x_979_,
        v_x_980_,
        v_h__1_981_,
        v_h__2_982_,
    );
    lean_dec(v_x_979_);
    return v_res_983_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(
    mut v_00_u03b1_984_: *mut LeanObject,
    mut v_motive_985_: *mut LeanObject,
    mut v_x_986_: *mut LeanObject,
    mut v_x_987_: *mut LeanObject,
    mut v_h__1_988_: *mut LeanObject,
    mut v_h__2_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_991_: u8 = 0;
    v_zero_990_ = lean_unsigned_to_nat(0);
    v_isZero_991_ = lean_nat_dec_eq(v_x_986_, v_zero_990_);
    if v_isZero_991_ == 1 {
        let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_989_);
        v___x_992_ = lean_apply_1(v_h__1_988_, v_x_987_);
        return v___x_992_;
    } else {
        let mut v_one_993_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_988_);
        v_one_993_ = lean_unsigned_to_nat(1);
        v_n_994_ = lean_nat_sub(v_x_986_, v_one_993_);
        v___x_995_ = lean_apply_2(v_h__2_989_, v_n_994_, v_x_987_);
        return v___x_995_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter___boxed(
    mut v_00_u03b1_996_: *mut LeanObject,
    mut v_motive_997_: *mut LeanObject,
    mut v_x_998_: *mut LeanObject,
    mut v_x_999_: *mut LeanObject,
    mut v_h__1_1000_: *mut LeanObject,
    mut v_h__2_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1002_: *mut LeanObject = core::ptr::null_mut();
    v_res_1002_ = l___private_Init_Data_Array_Lemmas_0__Array_shrink_match__1_splitter(
        v_00_u03b1_996_,
        v_motive_997_,
        v_x_998_,
        v_x_999_,
        v_h__1_1000_,
        v_h__2_1001_,
    );
    lean_dec(v_x_998_);
    return v_res_1002_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
    mut v_i_1003_: *mut LeanObject,
    mut v_h__1_1004_: *mut LeanObject,
    mut v_h__2_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1007_: u8 = 0;
    v_zero_1006_ = lean_unsigned_to_nat(0);
    v_isZero_1007_ = lean_nat_dec_eq(v_i_1003_, v_zero_1006_);
    if v_isZero_1007_ == 1 {
        let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1005_);
        v___x_1008_ = lean_box(0);
        v___x_1009_ = lean_apply_1(v_h__1_1004_, v___x_1008_);
        return v___x_1009_;
    } else {
        let mut v_one_1010_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1004_);
        v_one_1010_ = lean_unsigned_to_nat(1);
        v_n_1011_ = lean_nat_sub(v_i_1003_, v_one_1010_);
        v___x_1012_ = lean_apply_1(v_h__2_1005_, v_n_1011_);
        return v___x_1012_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg___boxed(
    mut v_i_1013_: *mut LeanObject,
    mut v_h__1_1014_: *mut LeanObject,
    mut v_h__2_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1016_: *mut LeanObject = core::ptr::null_mut();
    v_res_1016_ =
        l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___redArg(
            v_i_1013_,
            v_h__1_1014_,
            v_h__2_1015_,
        );
    lean_dec(v_i_1013_);
    return v_res_1016_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(
    mut v_motive_1017_: *mut LeanObject,
    mut v_i_1018_: *mut LeanObject,
    mut v_h__1_1019_: *mut LeanObject,
    mut v_h__2_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1022_: u8 = 0;
    v_zero_1021_ = lean_unsigned_to_nat(0);
    v_isZero_1022_ = lean_nat_dec_eq(v_i_1018_, v_zero_1021_);
    if v_isZero_1022_ == 1 {
        let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1020_);
        v___x_1023_ = lean_box(0);
        v___x_1024_ = lean_apply_1(v_h__1_1019_, v___x_1023_);
        return v___x_1024_;
    } else {
        let mut v_one_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1019_);
        v_one_1025_ = lean_unsigned_to_nat(1);
        v_n_1026_ = lean_nat_sub(v_i_1018_, v_one_1025_);
        v___x_1027_ = lean_apply_1(v_h__2_1020_, v_n_1026_);
        return v___x_1027_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter___boxed(
    mut v_motive_1028_: *mut LeanObject,
    mut v_i_1029_: *mut LeanObject,
    mut v_h__1_1030_: *mut LeanObject,
    mut v_h__2_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ = l___private_Init_Data_Array_Lemmas_0__Array_foldlM_loop_match__1_splitter(
        v_motive_1028_,
        v_i_1029_,
        v_h__1_1030_,
        v_h__2_1031_,
    );
    lean_dec(v_i_1029_);
    return v_res_1032_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_1033_: *mut LeanObject,
    mut v_h__1_1034_: *mut LeanObject,
    mut v_h__2_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1037_: u8 = 0;
    v_zero_1036_ = lean_unsigned_to_nat(0);
    v_isZero_1037_ = lean_nat_dec_eq(v_i_1033_, v_zero_1036_);
    if v_isZero_1037_ == 1 {
        let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1035_);
        v___x_1038_ = lean_apply_1(v_h__1_1034_, lean_box(0));
        return v___x_1038_;
    } else {
        let mut v_one_1039_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1034_);
        v_one_1039_ = lean_unsigned_to_nat(1);
        v_n_1040_ = lean_nat_sub(v_i_1033_, v_one_1039_);
        v___x_1041_ = lean_apply_2(v_h__2_1035_, v_n_1040_, lean_box(0));
        return v___x_1041_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_1042_: *mut LeanObject,
    mut v_h__1_1043_: *mut LeanObject,
    mut v_h__2_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1045_: *mut LeanObject = core::ptr::null_mut();
    v_res_1045_ =
        l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_1042_,
            v_h__1_1043_,
            v_h__2_1044_,
        );
    lean_dec(v_i_1042_);
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_1046_: *mut LeanObject,
    mut v_as_1047_: *mut LeanObject,
    mut v_motive_1048_: *mut LeanObject,
    mut v_i_1049_: *mut LeanObject,
    mut v_h_1050_: *mut LeanObject,
    mut v_h__1_1051_: *mut LeanObject,
    mut v_h__2_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1054_: u8 = 0;
    v_zero_1053_ = lean_unsigned_to_nat(0);
    v_isZero_1054_ = lean_nat_dec_eq(v_i_1049_, v_zero_1053_);
    if v_isZero_1054_ == 1 {
        let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1052_);
        v___x_1055_ = lean_apply_1(v_h__1_1051_, lean_box(0));
        return v___x_1055_;
    } else {
        let mut v_one_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1051_);
        v_one_1056_ = lean_unsigned_to_nat(1);
        v_n_1057_ = lean_nat_sub(v_i_1049_, v_one_1056_);
        v___x_1058_ = lean_apply_2(v_h__2_1052_, v_n_1057_, lean_box(0));
        return v___x_1058_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_1059_: *mut LeanObject,
    mut v_as_1060_: *mut LeanObject,
    mut v_motive_1061_: *mut LeanObject,
    mut v_i_1062_: *mut LeanObject,
    mut v_h_1063_: *mut LeanObject,
    mut v_h__1_1064_: *mut LeanObject,
    mut v_h__2_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l___private_Init_Data_Array_Lemmas_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_1059_,
        v_as_1060_,
        v_motive_1061_,
        v_i_1062_,
        v_h_1063_,
        v_h__1_1064_,
        v_h__2_1065_,
    );
    lean_dec(v_i_1062_);
    lean_dec_ref(v_as_1060_);
    return v_res_1066_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter___redArg(
    mut v_x_1067_: *mut LeanObject,
    mut v_h__1_1068_: *mut LeanObject,
    mut v_h__2_1069_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1067_) == 0 {
        let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1068_);
        v___x_1070_ = lean_box(0);
        v___x_1071_ = lean_apply_1(v_h__2_1069_, v___x_1070_);
        return v___x_1071_;
    } else {
        let mut v_val_1072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1069_);
        v_val_1072_ = lean_ctor_get(v_x_1067_, 0);
        lean_inc(v_val_1072_);
        lean_dec_ref_known(v_x_1067_, 1);
        v___x_1073_ = lean_apply_1(v_h__1_1068_, v_val_1072_);
        return v___x_1073_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__List_foldl__filterMap_match__1_splitter(
    mut v_00_u03b2_1074_: *mut LeanObject,
    mut v_motive_1075_: *mut LeanObject,
    mut v_x_1076_: *mut LeanObject,
    mut v_h__1_1077_: *mut LeanObject,
    mut v_h__2_1078_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1076_) == 0 {
        let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1077_);
        v___x_1079_ = lean_box(0);
        v___x_1080_ = lean_apply_1(v_h__2_1078_, v___x_1079_);
        return v___x_1080_;
    } else {
        let mut v_val_1081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1078_);
        v_val_1081_ = lean_ctor_get(v_x_1076_, 0);
        lean_inc(v_val_1081_);
        lean_dec_ref_known(v_x_1076_, 1);
        v___x_1082_ = lean_apply_1(v_h__1_1077_, v_val_1081_);
        return v___x_1082_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter___redArg(
    mut v_x_1083_: *mut LeanObject,
    mut v_h__1_1084_: *mut LeanObject,
    mut v_h__2_1085_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1083_) == 0 {
        let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1084_);
        v___x_1086_ = lean_box(0);
        v___x_1087_ = lean_apply_1(v_h__2_1085_, v___x_1086_);
        return v___x_1087_;
    } else {
        let mut v_val_1088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1085_);
        v_val_1088_ = lean_ctor_get(v_x_1083_, 0);
        lean_inc(v_val_1088_);
        lean_dec_ref_known(v_x_1083_, 1);
        v___x_1089_ = lean_apply_1(v_h__1_1084_, v_val_1088_);
        return v___x_1089_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_foldl__filterMap_x27_match__1_splitter(
    mut v_00_u03b2_1090_: *mut LeanObject,
    mut v_motive_1091_: *mut LeanObject,
    mut v_x_1092_: *mut LeanObject,
    mut v_h__1_1093_: *mut LeanObject,
    mut v_h__2_1094_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1092_) == 0 {
        let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1093_);
        v___x_1095_ = lean_box(0);
        v___x_1096_ = lean_apply_1(v_h__2_1094_, v___x_1095_);
        return v___x_1096_;
    } else {
        let mut v_val_1097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1094_);
        v_val_1097_ = lean_ctor_get(v_x_1092_, 0);
        lean_inc(v_val_1097_);
        lean_dec_ref_known(v_x_1092_, 1);
        v___x_1098_ = lean_apply_1(v_h__1_1093_, v_val_1097_);
        return v___x_1098_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___redArg(
    mut v_x_1099_: *mut LeanObject,
    mut v_h__1_1100_: *mut LeanObject,
    mut v_h__2_1101_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1099_) == 0 {
        let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1101_);
        v___x_1102_ = lean_box(0);
        v___x_1103_ = lean_apply_1(v_h__1_1100_, v___x_1102_);
        return v___x_1103_;
    } else {
        let mut v_val_1104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1100_);
        v_val_1104_ = lean_ctor_get(v_x_1099_, 0);
        lean_inc(v_val_1104_);
        lean_dec_ref_known(v_x_1099_, 1);
        v___x_1105_ = lean_apply_1(v_h__2_1101_, v_val_1104_);
        return v___x_1105_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(
    mut v_00_u03b1_1106_: *mut LeanObject,
    mut v_as_1107_: *mut LeanObject,
    mut v_motive_1108_: *mut LeanObject,
    mut v_x_1109_: *mut LeanObject,
    mut v_h__1_1110_: *mut LeanObject,
    mut v_h__2_1111_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1109_) == 0 {
        let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1111_);
        v___x_1112_ = lean_box(0);
        v___x_1113_ = lean_apply_1(v_h__1_1110_, v___x_1112_);
        return v___x_1113_;
    } else {
        let mut v_val_1114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1110_);
        v_val_1114_ = lean_ctor_get(v_x_1109_, 0);
        lean_inc(v_val_1114_);
        lean_dec_ref_known(v_x_1109_, 1);
        v___x_1115_ = lean_apply_1(v_h__2_1111_, v_val_1114_);
        return v___x_1115_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter___boxed(
    mut v_00_u03b1_1116_: *mut LeanObject,
    mut v_as_1117_: *mut LeanObject,
    mut v_motive_1118_: *mut LeanObject,
    mut v_x_1119_: *mut LeanObject,
    mut v_h__1_1120_: *mut LeanObject,
    mut v_h__2_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l___private_Init_Data_Array_Lemmas_0__Array_erase_match__1_splitter(
        v_00_u03b1_1116_,
        v_as_1117_,
        v_motive_1118_,
        v_x_1119_,
        v_h__1_1120_,
        v_h__2_1121_,
    );
    lean_dec_ref(v_as_1117_);
    return v_res_1122_;
}
pub unsafe fn l_Array_toListRev___redArg___lam__0(
    mut v_x1_1123_: *mut LeanObject,
    mut v_x2_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1125_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1125_, 0, v_x2_1124_);
    lean_ctor_set(v___x_1125_, 1, v_x1_1123_);
    return v___x_1125_;
}
pub unsafe fn l_Array_toListRev___redArg(mut v_xs_1146_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    v___x_1147_ = lean_box(0);
    v___x_1148_ = lean_unsigned_to_nat(0);
    v___x_1149_ = lean_array_get_size(v_xs_1146_);
    v___x_1150_ = l_Array_toListRev___redArg___closed__9;
    v___x_1151_ = lean_nat_dec_lt(v___x_1148_, v___x_1149_);
    if v___x_1151_ == 0 {
        lean_dec_ref(v_xs_1146_);
        return v___x_1147_;
    } else {
        let mut v___f_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: u8 = 0;
        v___f_1152_ = l_Array_toListRev___redArg___closed__10;
        v___x_1153_ = lean_nat_dec_le(v___x_1149_, v___x_1149_);
        if v___x_1153_ == 0 {
            if v___x_1151_ == 0 {
                lean_dec_ref(v_xs_1146_);
                return v___x_1147_;
            } else {
                let mut v___x_1154_: usize = 0;
                let mut v___x_1155_: usize = 0;
                let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
                v___x_1154_ = 0usize;
                v___x_1155_ = lean_usize_of_nat(v___x_1149_);
                v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_1150_,
                    v___f_1152_,
                    v_xs_1146_,
                    v___x_1154_,
                    v___x_1155_,
                    v___x_1147_,
                );
                return v___x_1156_;
            }
        } else {
            let mut v___x_1157_: usize = 0;
            let mut v___x_1158_: usize = 0;
            let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
            v___x_1157_ = 0usize;
            v___x_1158_ = lean_usize_of_nat(v___x_1149_);
            v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_1150_,
                v___f_1152_,
                v_xs_1146_,
                v___x_1157_,
                v___x_1158_,
                v___x_1147_,
            );
            return v___x_1159_;
        }
    }
}
pub unsafe fn l_Array_toListRev(
    mut v_00_u03b1_1160_: *mut LeanObject,
    mut v_xs_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    v___x_1162_ = lean_box(0);
    v___x_1163_ = lean_unsigned_to_nat(0);
    v___x_1164_ = lean_array_get_size(v_xs_1161_);
    v___x_1165_ = l_Array_toListRev___redArg___closed__9;
    v___x_1166_ = lean_nat_dec_lt(v___x_1163_, v___x_1164_);
    if v___x_1166_ == 0 {
        lean_dec_ref(v_xs_1161_);
        return v___x_1162_;
    } else {
        let mut v___f_1167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: u8 = 0;
        v___f_1167_ = l_Array_toListRev___redArg___closed__10;
        v___x_1168_ = lean_nat_dec_le(v___x_1164_, v___x_1164_);
        if v___x_1168_ == 0 {
            if v___x_1166_ == 0 {
                lean_dec_ref(v_xs_1161_);
                return v___x_1162_;
            } else {
                let mut v___x_1169_: usize = 0;
                let mut v___x_1170_: usize = 0;
                let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
                v___x_1169_ = 0usize;
                v___x_1170_ = lean_usize_of_nat(v___x_1164_);
                v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                    v___x_1165_,
                    v___f_1167_,
                    v_xs_1161_,
                    v___x_1169_,
                    v___x_1170_,
                    v___x_1162_,
                );
                return v___x_1171_;
            }
        } else {
            let mut v___x_1172_: usize = 0;
            let mut v___x_1173_: usize = 0;
            let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
            v___x_1172_ = 0usize;
            v___x_1173_ = lean_usize_of_nat(v___x_1164_);
            v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(
                v___x_1165_,
                v___f_1167_,
                v_xs_1161_,
                v___x_1172_,
                v___x_1173_,
                v___x_1162_,
            );
            return v___x_1174_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(
    mut v_x_1175_: *mut LeanObject,
    mut v_h__1_1176_: *mut LeanObject,
    mut v_h__2_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1179_: u8 = 0;
    v_zero_1178_ = lean_unsigned_to_nat(0);
    v_isZero_1179_ = lean_nat_dec_eq(v_x_1175_, v_zero_1178_);
    if v_isZero_1179_ == 1 {
        let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1176_);
        v___x_1180_ = lean_apply_1(v_h__2_1177_, lean_box(0));
        return v___x_1180_;
    } else {
        let mut v_one_1181_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1177_);
        v_one_1181_ = lean_unsigned_to_nat(1);
        v_n_1182_ = lean_nat_sub(v_x_1175_, v_one_1181_);
        v___x_1183_ = lean_apply_2(v_h__1_1176_, v_n_1182_, lean_box(0));
        return v___x_1183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg___boxed(
    mut v_x_1184_: *mut LeanObject,
    mut v_h__1_1185_: *mut LeanObject,
    mut v_h__2_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1187_: *mut LeanObject = core::ptr::null_mut();
    v_res_1187_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___redArg(
        v_x_1184_,
        v_h__1_1185_,
        v_h__2_1186_,
    );
    lean_dec(v_x_1184_);
    return v_res_1187_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(
    mut v_n_1188_: *mut LeanObject,
    mut v_motive_1189_: *mut LeanObject,
    mut v_x_1190_: *mut LeanObject,
    mut v_x_1191_: *mut LeanObject,
    mut v_h__1_1192_: *mut LeanObject,
    mut v_h__2_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1195_: u8 = 0;
    v_zero_1194_ = lean_unsigned_to_nat(0);
    v_isZero_1195_ = lean_nat_dec_eq(v_x_1190_, v_zero_1194_);
    if v_isZero_1195_ == 1 {
        let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1192_);
        v___x_1196_ = lean_apply_1(v_h__2_1193_, lean_box(0));
        return v___x_1196_;
    } else {
        let mut v_one_1197_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1193_);
        v_one_1197_ = lean_unsigned_to_nat(1);
        v_n_1198_ = lean_nat_sub(v_x_1190_, v_one_1197_);
        v___x_1199_ = lean_apply_2(v_h__1_1192_, v_n_1198_, lean_box(0));
        return v___x_1199_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter___boxed(
    mut v_n_1200_: *mut LeanObject,
    mut v_motive_1201_: *mut LeanObject,
    mut v_x_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
    mut v_h__1_1204_: *mut LeanObject,
    mut v_h__2_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_res_1206_ = l___private_Init_Data_Array_Lemmas_0__Array_ofFn_go_match__1_splitter(
        v_n_1200_,
        v_motive_1201_,
        v_x_1202_,
        v_x_1203_,
        v_h__1_1204_,
        v_h__2_1205_,
    );
    lean_dec(v_x_1202_);
    lean_dec(v_n_1200_);
    return v_res_1206_;
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter___redArg(
    mut v_opt_1207_: *mut LeanObject,
    mut v_h__1_1208_: *mut LeanObject,
    mut v_h__2_1209_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_opt_1207_) == 0 {
        let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1208_);
        v___x_1210_ = lean_box(0);
        v___x_1211_ = lean_apply_1(v_h__2_1209_, v___x_1210_);
        return v___x_1211_;
    } else {
        let mut v_val_1212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1209_);
        v_val_1212_ = lean_ctor_get(v_opt_1207_, 0);
        lean_inc(v_val_1212_);
        lean_dec_ref_known(v_opt_1207_, 1);
        v___x_1213_ = lean_apply_1(v_h__1_1208_, v_val_1212_);
        return v___x_1213_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__Option_getD_match__1_splitter(
    mut v_00_u03b1_1214_: *mut LeanObject,
    mut v_motive_1215_: *mut LeanObject,
    mut v_opt_1216_: *mut LeanObject,
    mut v_h__1_1217_: *mut LeanObject,
    mut v_h__2_1218_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_opt_1216_) == 0 {
        let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1217_);
        v___x_1219_ = lean_box(0);
        v___x_1220_ = lean_apply_1(v_h__2_1218_, v___x_1219_);
        return v___x_1220_;
    } else {
        let mut v_val_1221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1218_);
        v_val_1221_ = lean_ctor_get(v_opt_1216_, 0);
        lean_inc(v_val_1221_);
        lean_dec_ref_known(v_opt_1216_, 1);
        v___x_1222_ = lean_apply_1(v_h__1_1217_, v_val_1221_);
        return v___x_1222_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_1223_: *mut LeanObject,
    mut v_h__1_1224_: *mut LeanObject,
    mut v_h__2_1225_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1223_) == 0 {
        let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1224_);
        v___x_1226_ = lean_box(0);
        v___x_1227_ = lean_apply_1(v_h__2_1225_, v___x_1226_);
        return v___x_1227_;
    } else {
        let mut v_val_1228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1225_);
        v_val_1228_ = lean_ctor_get(v_x_1223_, 0);
        lean_inc(v_val_1228_);
        lean_dec_ref_known(v_x_1223_, 1);
        v___x_1229_ = lean_apply_1(v_h__1_1224_, v_val_1228_);
        return v___x_1229_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_1230_: *mut LeanObject,
    mut v_motive_1231_: *mut LeanObject,
    mut v_x_1232_: *mut LeanObject,
    mut v_h__1_1233_: *mut LeanObject,
    mut v_h__2_1234_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1232_) == 0 {
        let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1233_);
        v___x_1235_ = lean_box(0);
        v___x_1236_ = lean_apply_1(v_h__2_1234_, v___x_1235_);
        return v___x_1236_;
    } else {
        let mut v_val_1237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1234_);
        v_val_1237_ = lean_ctor_get(v_x_1232_, 0);
        lean_inc(v_val_1237_);
        lean_dec_ref_known(v_x_1232_, 1);
        v___x_1238_ = lean_apply_1(v_h__1_1233_, v_val_1237_);
        return v___x_1238_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_filterMap__replicate___auto__7 = _init_l_Array_filterMap__replicate___auto__7();
    lean_mark_persistent(l_Array_filterMap__replicate___auto__7);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Lemmas(builtin);
}
